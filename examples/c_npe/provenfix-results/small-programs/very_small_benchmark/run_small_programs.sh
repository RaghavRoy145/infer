#!/bin/bash
# Note: not using set -e to ensure script always reaches the attach prompt

IMAGE="yahuuuuui/fse24-prove_n_fix:ubuntu"
CONTAINER_NAME="small-programs-analysis"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
OUTPUT_DIR="${SCRIPT_DIR}/results/${TIMESTAMP}"

echo "=== ProveNFix Small Programs Analysis ==="
echo "Using spec.c (root) on main branch"
echo ""
echo "Container: ${CONTAINER_NAME}"
echo "Results: ${OUTPUT_DIR}"
echo ""

mkdir -p "$OUTPUT_DIR"

# Collect all .c files in this directory (excluding spec files)
C_FILES=()
for f in "${SCRIPT_DIR}"/*.c; do
    [ -f "$f" ] && C_FILES+=("$(basename "$f")")
done

if [ ${#C_FILES[@]} -eq 0 ]; then
    echo "ERROR: No .c files found in ${SCRIPT_DIR}"
    exit 1
fi

echo "Found ${#C_FILES[@]} C files to analyze:"
printf "  - %s\n" "${C_FILES[@]}"
echo ""

# Pull image
echo "[1/5] Pulling Docker image..."
docker pull "$IMAGE"

# Handle existing container
if docker ps -a --format '{{.Names}}' | grep -q "^${CONTAINER_NAME}$"; then
    echo "Container '${CONTAINER_NAME}' already exists."
    read -p "Remove it and start fresh? (y/n): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        docker rm -f "$CONTAINER_NAME"
    else
        echo "Exiting."
        exit 1
    fi
fi

# Start container
echo "[2/5] Creating container..."
docker run -d --name "$CONTAINER_NAME" "$IMAGE" tail -f /dev/null

# Use main branch
echo "[3/5] Using main branch..."
docker exec "$CONTAINER_NAME" bash -c '
    cd /home/infer_TempFix
    git stash
    git checkout main
    echo "Branch: $(git branch --show-current)"
'

echo ""
echo "[4/5] Building ProveNFix..."
docker exec "$CONTAINER_NAME" bash -c '
    cd /home/infer_TempFix
    ./compile
'

# Copy all C files into the container
docker exec "$CONTAINER_NAME" mkdir -p /home/small-programs
for f in "${C_FILES[@]}"; do
    docker cp "${SCRIPT_DIR}/${f}" "${CONTAINER_NAME}:/home/small-programs/${f}"
done

# Run analysis on each file
echo ""
echo "[5/5] Running Infer (Pulse) on each file..."
echo ""

for f in "${C_FILES[@]}"; do
    NAME="${f%.c}"
    echo "--- Analyzing: ${f} ---"

    docker exec "$CONTAINER_NAME" bash -c "
        cd /home/small-programs
        cp /home/infer_TempFix/spec.c spec.c
        rm -rf infer-out
        rm -f /home/infer_TempFix/TempFix-out/detail.txt
        rm -f /home/infer_TempFix/TempFix-out/report.csv
        /home/infer_TempFix/infer/bin/infer run --pulse -- clang -c ${f}
        python3 /home/infer_TempFix/TempFixDataAnalysis.py
    "

    # Save results for this file
    docker cp "${CONTAINER_NAME}:/home/infer_TempFix/TempFix-out/detail.txt" "${OUTPUT_DIR}/${NAME}_detail.txt" 2>/dev/null || true
    docker cp "${CONTAINER_NAME}:/home/infer_TempFix/TempFix-out/report.csv" "${OUTPUT_DIR}/${NAME}_output.txt" 2>/dev/null || true

    # Print summary for this file
    if [ -f "${OUTPUT_DIR}/${NAME}_detail.txt" ]; then
        DETAIL_SIZE=$(stat -c%s "${OUTPUT_DIR}/${NAME}_detail.txt" 2>/dev/null || echo "0")
        if [ "$DETAIL_SIZE" -gt 10 ]; then
            BUG_COUNT=$(grep -c "Future-condition checking" "${OUTPUT_DIR}/${NAME}_detail.txt" 2>/dev/null || echo "0")
            echo "  >>> Bugs found: ${BUG_COUNT}"
            echo "  ----------------------------------------"
            cat "${OUTPUT_DIR}/${NAME}_detail.txt"
            echo "  ----------------------------------------"
        else
            echo "  >>> No bugs found"
        fi
    else
        echo "  >>> detail.txt not found"
    fi
    echo ""
done

echo ""
echo "=== Analysis Complete ==="
echo ""
echo "Results saved to: ${OUTPUT_DIR}"
ls -la "${OUTPUT_DIR}"
echo ""

echo "Container '${CONTAINER_NAME}' is still running."
echo "To attach: docker exec -it ${CONTAINER_NAME} bash"
echo "To remove: docker rm -f ${CONTAINER_NAME}"
echo ""

read -p "Attach to container now? (y/n): " -n 1 -r
echo
if [[ $REPLY =~ ^[Yy]$ ]]; then
    docker exec -it "$CONTAINER_NAME" bash -c "cd /home/small-programs && bash"
fi
