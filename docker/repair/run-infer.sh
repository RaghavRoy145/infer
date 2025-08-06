#!/bin/bash

# Script to run Infer on a specific file using Docker
# Usage: ./run-infer.sh <path-to-c-file> [additional-infer-options]

if [ $# -lt 1 ]; then
    echo "Usage: $0 <path-to-c-file> [additional-infer-options]"
    echo "Example: $0 ../../examples/hello.c"
    echo "Example: $0 ../../examples/c_npe/demo.c --keep-going --debug --pulse-only"
    exit 1
fi

# Get the file path
FILE_PATH="$1"
shift  # Remove first argument, leaving any additional options

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

# Run Infer in Docker
echo "Running Infer on $FILE_NAME..."
docker run --rm -v "$FILE_DIR":/examples:ro infer-repair sh -c "
    cp /examples/$FILE_NAME /tmp/ && 
    cd /tmp && 
    infer $@ -- clang -c $FILE_NAME && 
    echo '' && 
    echo '=== Infer Results ===' && 
    cat infer-out/report.txt 2>/dev/null || echo 'No issues found'
"