#!/bin/bash

# Script to run Infer with repair-specific options
# Usage: ./run-repair.sh <path-to-c-file>

if [ $# -lt 1 ]; then
    echo "Usage: $0 <path-to-c-file>"
    echo "Example: $0 ../../examples/c_npe/demo.c"
    exit 1
fi

# Get the file path
FILE_PATH="$1"

# Get absolute path
ABS_FILE_PATH=$(cd "$(dirname "$FILE_PATH")" && pwd)/$(basename "$FILE_PATH")

# Check if file exists
if [ ! -f "$ABS_FILE_PATH" ]; then
    echo "Error: File $ABS_FILE_PATH does not exist"
    exit 1
fi

# Get file name and directory
FILE_NAME=$(basename "$ABS_FILE_PATH")
FILE_DIR=$(dirname "$ABS_FILE_PATH")

# Build Docker image if it doesn't exist
if ! docker images | grep -q "infer-repair"; then
    echo "Building Docker image..."
    docker build -t infer-repair .
fi

# Run Infer with repair options
echo "Running Infer (repair mode) on $FILE_NAME..."
docker run --rm -v "$FILE_DIR":/examples:ro infer-repair sh -c "
    cp /examples/$FILE_NAME /tmp/ && 
    cd /tmp && 
    echo '=== Running Infer with repair options ===' &&
    infer --keep-going --debug --pulse-only -- cc -c $FILE_NAME && 
    echo '' && 
    echo '=== Searching for Repair output ===' && 
    grep -nriw 'Repair' . 2>/dev/null || echo 'No Repair output found' &&
    echo '' && 
    echo '=== Infer Results ===' && 
    cat infer-out/report.txt 2>/dev/null || echo 'No report generated'
"