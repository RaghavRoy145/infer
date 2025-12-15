import sys
from clang import cindex
from pathlib import Path

# --- Configuration ---
# Use the same path that worked before
cindex.Config.set_library_path('/usr/lib/llvm-14/lib')

def find_functions_in_file(tu, source_file_path):
    """Recursively traverses the AST and prints function declarations found in the specific source file."""
    
    # We need the absolute path for a reliable comparison
    source_file_abs_path = str(Path(source_file_path).resolve())

    def traverse(node):
        # Check if the node is in the file we care about
        if node.location.file and str(Path(node.location.file.name).resolve()) == source_file_abs_path:
            # Check if the node is a function declaration
            if node.kind == cindex.CursorKind.FUNCTION_DECL:
                print(
                    f"Found Function: '{node.spelling}'\n"
                    f"  at Line: {node.location.line}\n"
                    f"  in File: {node.location.file.name}\n"
                    f"-------------------------"
                )

        # Recurse for children
        for child in node.get_children():
            traverse(child)

    traverse(tu.cursor)


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 ast_inspector.py <path_to_c_file>")
        sys.exit(1)
        
    source_file = sys.argv[1]
    print(f"--- Inspecting AST for: {source_file} ---\n")

    try:
        index = cindex.Index.create()
        
        # --- We must provide the correct include paths for OpenSSL to parse correctly ---
        source_root = Path.cwd() / 'source' # Assumes you run from benchmarks/
        openssl_root = source_root / 'openssl-1'
        clang_args = [
            '-x', 'c',
            '-I/usr/include',
            f'-I{openssl_root}',
            f'-I{openssl_root / "include"}',
            f'-I{openssl_root / "crypto"}'
        ]

        tu = index.parse(source_file, args=clang_args)

        if not tu:
            print("[FATAL] Clang failed to create a translation unit.")
            return

        find_functions_in_file(tu, source_file)

    except Exception as e:
        print(f"\n[FATAL] An unexpected error occurred: {e}")

if __name__ == "__main__":
    main()
