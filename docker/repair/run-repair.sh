#!/bin/bash

# Script to run Infer with repair-specific options
# Usage: ./run-repair.sh <path-to-c-file>

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
MAGENTA='\033[0;35m'
NC='\033[0m' # No Color
DIM='\033[2m'

if [ $# -lt 1 ]; then
    echo -e "${RED}Usage: $0 <path-to-c-file>${NC}"
    echo -e "${DIM}Example: $0 ../../examples/c_npe/demo.c${NC}"
    exit 1
fi

# Get the file path
FILE_PATH="$1"

# Get absolute path
ABS_FILE_PATH=$(cd "$(dirname "$FILE_PATH")" && pwd)/$(basename "$FILE_PATH")

# Check if file exists
if [ ! -f "$ABS_FILE_PATH" ]; then
    echo -e "${RED}Error: File $ABS_FILE_PATH does not exist${NC}"
    exit 1
fi

# Get file name and directory
FILE_NAME=$(basename "$ABS_FILE_PATH")
FILE_DIR=$(dirname "$ABS_FILE_PATH")

# Build Docker image if it doesn't exist
if ! docker images | grep -q "infer-repair"; then
    echo -e "${YELLOW}Docker image not found. Building...${NC}"
    echo -e "${DIM}Run ./build-docker.sh to build from source with your changes${NC}"
    exit 1
fi

# Run Infer with repair options
echo -e "${BLUE}=== Running Infer (repair mode) on $FILE_NAME ===${NC}"
docker run --rm -v "$FILE_DIR":/examples:ro infer-repair sh -c "
    cp /examples/$FILE_NAME /tmp/ && 
    cd /tmp && 
    echo -e '\033[0;36m>>> Running Infer with repair options\033[0m' &&
    infer --keep-going --debug --pulse-only -- cc -c $FILE_NAME 2>&1 | \
    sed 's/^/\x1b[2m[INFER]\x1b[0m /' && 
    echo '' && 
    echo -e '\033[0;36m>>> Searching for Repair output\033[0m' && 
    { grep -E '\[repair-plan\]|\[repair-log\]|\[repair\]' infer-out/logs/* 2>/dev/null | \
      sed 's/^/\x1b[0;32m[REPAIR]\x1b[0m /' || \
      echo -e '\033[0;31mNo Repair output found\033[0m'; } &&
    echo '' && 
    echo -e '\033[0;36m>>> Infer Results\033[0m' && 
    { cat infer-out/report.txt 2>/dev/null | sed 's/^/\x1b[0;33m[REPORT]\x1b[0m /' || \
      echo -e '\033[0;31mNo report generated\033[0m'; }
"