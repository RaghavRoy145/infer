import sys
import os
import json
import csv
import re
from clang import cindex
from pathlib import Path

# --- Configuration ---
cindex.Config.set_library_path('/usr/lib/llvm-14/lib')

class CFGBuilder:
    def __init__(self, source_file, include_paths=None):
        self.source_file = source_file
        self.index = cindex.Index.create()
        clang_args = ['-x', 'c', '-I/usr/include']
        if include_paths:
            for path in include_paths: clang_args.append(f'-I{path}')
        try:
            self.tu = self.index.parse(self.source_file, args=clang_args)
        except cindex.TranslationUnitLoadError:
             raise
        if not self.tu: raise RuntimeError("Clang failed to create a translation unit.")
        has_errors, error_messages = False, []
        for diag in self.tu.diagnostics:
            if diag.severity >= cindex.Diagnostic.Error:
                has_errors = True
                error_messages.append(f"  [Clang Diagnostic] L{diag.location.line}: {diag.spelling}")
        if has_errors: raise RuntimeError(f"Error parsing translation unit:\n" + "\n".join(error_messages))

    def build_for_function(self, function_name):
        func_cursor = self._find_function_cursor(function_name)
        if not func_cursor: raise RuntimeError(f"Function '{function_name}' not found in AST.")
        self.cfg = {function_name: []}
        self._traverse_ast(func_cursor, function_name)
        return self.cfg[function_name]

    def _find_function_cursor(self, function_name):
        for node in self.tu.cursor.get_children():
            if node.location.file and node.location.file.name == self.source_file:
                if node.spelling == function_name and node.kind == cindex.CursorKind.FUNCTION_DECL:
                    return node
        return None

    def _traverse_ast(self, cursor, function_name):
        if cursor.location.file and cursor.location.file.name == self.source_file:
            if cursor.kind.is_statement() or cursor.kind.is_declaration():
                if cursor.kind != cindex.CursorKind.COMPOUND_STMT:
                    self.cfg[function_name].append({'line': cursor.location.line})
        for child in cursor.get_children(): self._traverse_ast(child, function_name)

class PatchAnalyzer:
    def __init__(self, source_file, function_name, include_paths=None):
        self.source_file = source_file
        self.function_name = function_name.strip()
        builder = CFGBuilder(self.source_file, include_paths)
        self.cfg_nodes = builder.build_for_function(self.function_name)
        self.total_function_nodes = len(self.cfg_nodes)

    def analyze(self, patch_file_path, tool_name):
        if tool_name == "monobrow": return self._analyze_json_patch(patch_file_path)
        elif tool_name in ["efffix", "footpatch"]: return self._analyze_diff_patch(patch_file_path, tool_name)
        else: raise ValueError(f"Unknown tool: {tool_name}")

    def _analyze_json_patch(self, json_file):
        with open(json_file, 'r') as f: data = json.load(f)[0]
        plan_type = data.get('plan_type')
        details = data.get('details', {})
        metrics = {"total_function_nodes": self.total_function_nodes, "total_aliases": details.get('metrics', {}).get('total_aliases', 'N/A')}
        if plan_type == 'Skip':
            if 'start_line' not in details: raise ValueError("JSON 'Skip' plan missing 'start_line'.")
            metrics.update({"patch_type": "Guarded Block", "cost_g_overhead": details['metrics'].get('cost_g_overhead_final', 1), "cost_rep_modification": "N/A"})
            nodes_in_scope = [n for n in self.cfg_nodes if details['start_line'] <= n['line'] <= details['end_line']]
            cost_l_local = max(0, len(nodes_in_scope) - 1)
            metrics["cost_l_local_imprecision"] = cost_l_local
            metrics["L_local_norm"] = cost_l_local / self.total_function_nodes if self.total_function_nodes > 0 else 0
            metrics["structural_impact"] = 0
            return metrics
        elif plan_type == 'Replace':
            metrics.update({"patch_type": "Replace", "cost_g_overhead": "N/A", "cost_l_local_imprecision": "N/A", "structural_impact": 0, "L_local_norm": 0.0, "cost_rep_modification": details['metrics'].get('cost_rep_modification', 1)})
            return metrics
        else: raise ValueError(f"No valid plan found. Plan type was '{plan_type}'.")

    def _analyze_diff_patch(self, patch_file, tool_name):
        with open(patch_file, 'r') as f: content = f.read()
        match = re.search(r'^\+([^\+].*)', content, re.MULTILINE)
        added_line = match.group(1).strip() if match else ""
        line_num_match = re.search(r'@@ -\d+,\d+ \+(\d+),\d+ @@', content)
        patch_line = int(line_num_match.group(1)) if line_num_match else 0
        metrics = {"total_function_nodes": self.total_function_nodes, "total_aliases": "N/A"}
        if ('=' in added_line and ('malloc' in added_line or re.search(r'=\s*\w+;', added_line))) and 'if' not in added_line:
             metrics.update({"patch_type": "Replace", "cost_g_overhead": "N/A", "cost_l_local_imprecision": "N/A", "structural_impact": 0, "L_local_norm": 0.0, "cost_rep_modification": 1 + (1 if 'malloc' in added_line else 0)})
        else:
            patch_type = "Early Exit" if 'return' in added_line else "Guarded Block"
            metrics.update({"patch_type": patch_type, "cost_g_overhead": 1, "cost_rep_modification": "N/A"})
            if patch_type == "Early Exit":
                metrics.update({"cost_l_local_imprecision": 0, "L_local_norm": 0.0, "structural_impact": len([n for n in self.cfg_nodes if n['line'] > patch_line])})
            else:
                nodes_in_scope = [n for n in self.cfg_nodes if n['line'] == patch_line]
                cost_l_local = max(0, len(nodes_in_scope) - 1)
                metrics.update({"cost_l_local_imprecision": cost_l_local, "L_local_norm": cost_l_local / self.total_function_nodes if self.total_function_nodes > 0 else 0, "structural_impact": 0})
        return metrics

def main():
    if len(sys.argv) != 4:
        print("Usage: python batch_analyzer.py <manifest.csv> <path_to_source_root> <path_to_patches_root>")
        sys.exit(1)

    manifest_file, source_root, patches_root = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
    output_file = "results.csv"
    results = []

    with open(manifest_file, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            try:
                bug_id, source_rel_path = row['bug_id'].strip(), row['source_file'].strip()
                base_dir = source_root / 'openssl-1' if 'openssl' in bug_id else source_root / 'generated_tests'
                source_file = base_dir / source_rel_path
                print(f"Processing {bug_id}...")
                if not source_file.is_file():
                    print(f"  [WARNING] Source not found: {source_file}. Skipping.", file=sys.stderr); continue
                
                include_paths = []
                if 'openssl' in bug_id:
                    openssl_root = source_root / 'openssl-1'
                    include_paths = [str(openssl_root), str(openssl_root / 'include'), str(openssl_root / 'crypto')]
                
                patch_path_str = row['patch_folder'].strip()
                patch_path = patches_root / patch_path_str
                
                patch_files_to_process = []
                if patch_path_str.endswith('.json'):
                    patch_files_to_process.append(patch_path)
                else: 
                    # --- CRITICAL FIX: Find ALL patch files in the directory ---
                    patch_files_to_process.extend(list(patch_path.glob('*.patch')))
                
                if not patch_files_to_process:
                    print(f"  [WARNING] No patches found in {patch_path}. Skipping.", file=sys.stderr); continue

                analyzer = PatchAnalyzer(str(source_file), row['function_name'], include_paths)
                
                # --- CRITICAL FIX: Loop through all found patch files ---
                for patch_file in patch_files_to_process:
                    metrics = analyzer.analyze(str(patch_file), row['tool_name'])
                    # Add filename to distinguish multiple patches for the same bug
                    full_result = {**row, **metrics, "patch_filename": patch_file.name}
                    results.append(full_result)
                    print(f"  Successfully processed patch: {patch_file.name}")

            except (RuntimeError, FileNotFoundError, ValueError) as e:
                print(f"  [INFO] Skipping {bug_id}: {e}", file=sys.stderr)
    
    if results:
        with open(output_file, 'w', newline='') as f:
            fieldnames = sorted(list(set(k for r in results for k in r.keys())))
            writer = csv.DictWriter(f, fieldnames=fieldnames)
            writer.writeheader()
            writer.writerows(results)
        print(f"\nAnalysis complete. Results saved to {output_file}")

if __name__ == "__main__":
    main()
