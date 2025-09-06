#!/bin/bash

# ==============================================================================
# Filter Plausible Patches Script (Corrected Scope)
# ==============================================================================

# The file containing the list of representative clusters
REPS_FILE="final_reps.txt"
# Defaulting to "true" for a safe dry run. Change to "false" to enable deletion.
DRY_RUN="false"

if [ ! -f "$REPS_FILE" ]; then
    echo "Error: Representative patches file not found at: $REPS_FILE"
    exit 1
fi

echo "[+] Starting patch filtering process..."

declare -A keeper_patches

# --- Step 1: Parse the final_reps.txt file ---
while IFS= read -r line; do
    if [[ $line =~ efffix-efffix-(original|disabled-learn)-(openssl-[0-9]+)-(null-ptr-[0-9]+)-.*(cluster-L[0-9]+-[0-9]+) ]]; then
        # --- START OF FIX: Removed 'local' keyword ---
        track="${BASH_REMATCH[1]}"
        subject="${BASH_REMATCH[2]}"
        bug_id="${BASH_REMATCH[3]}"
        cluster_name="${BASH_REMATCH[4]}"
        
        simple_name="${subject}-${bug_id}-${track}"
        
        keeper_patches["$simple_name"]+=" rep_${cluster_name}.patch"
        # --- END OF FIX ---
    fi
done < "$REPS_FILE"

echo "[+] Parsed representative patches from $REPS_FILE."

# --- Step 2: Iterate through the directories and filter the patches ---
for dir in openssl-*-null-ptr-*; do
    if [ -d "$dir" ] && [[ -v keeper_patches["$dir"] ]]; then
        printf "\n--- Processing Directory: %s ---\n" "$dir"
        
        # --- START OF FIX: Removed 'local' keyword ---
        keepers="${keeper_patches[$dir]}"
        
        for patch_file in "$dir"/*.patch; do
            base_name=$(basename "$patch_file")
            # --- END OF FIX ---
            
            if [[ ! " $keepers " =~ " $base_name " ]]; then
                if [ "$DRY_RUN" == "true" ]; then
                    echo "  [DRY RUN] Would delete: $patch_file"
                else
                    echo "  [-] Deleting: $patch_file"
                    rm "$patch_file"
                fi
            else
                echo "  [+] Keeping: $patch_file"
            fi
        done
    fi
done

echo ""
echo "[+] Filtering complete."
