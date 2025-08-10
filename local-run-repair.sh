#!/bin/bash

# Script to run Infer with repair functionality using local installation
# Usage: ./local-run-repair.sh <path-to-c-file>

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Check if a file was provided
if [ $# -eq 0 ]; then
    echo -e "${RED}Error: No input file provided${NC}"
    echo "Usage: $0 <path-to-c-file>"
    echo "Example: $0 examples/c_npe/test01_simple_null.c"
    exit 1
fi

INPUT_FILE="$1"

# Check if file exists
if [ ! -f "$INPUT_FILE" ]; then
    echo -e "${RED}Error: File '$INPUT_FILE' not found${NC}"
    exit 1
fi

# Get absolute path
INPUT_FILE_ABS=$(cd "$(dirname "$INPUT_FILE")" && pwd)/$(basename "$INPUT_FILE")
FILENAME=$(basename "$INPUT_FILE")

echo -e "${BLUE}=== Running Infer Repair Analysis ===${NC}"
echo -e "${GREEN}Input file:${NC} $INPUT_FILE_ABS"
echo ""

# Set path to local infer binary BEFORE changing directory
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
INFER_DIR="$SCRIPT_DIR/infer/bin"
export PATH="$INFER_DIR:$PATH"

if [ ! -f "$INFER_DIR/infer" ]; then
    echo -e "${RED}Error: Infer not found at $INFER_DIR/infer${NC}"
    echo "Please ensure Infer is built and installed in the infer/bin directory"
    exit 1
fi

# Create a temporary working directory
WORK_DIR=$(mktemp -d -t infer-repair-XXXXXX)
echo -e "${YELLOW}Working directory:${NC} $WORK_DIR"

# Copy the input file to working directory
cp "$INPUT_FILE_ABS" "$WORK_DIR/$FILENAME"
cd "$WORK_DIR"

# Run Infer with repair-specific options
echo -e "${BLUE}Running Infer analysis...${NC}"
echo ""

INFER_DEBUG=1 infer run \
    --pulse-only \
    --debug-level 2 \
    --no-progress-bar \
    -- clang -c "$FILENAME" 2>&1 | tee analysis.log

echo ""
echo -e "${GREEN}=== Analysis Complete ===${NC}"
echo ""

# Extract repair information from logs
echo -e "${BLUE}=== Searching for Repair Plans ===${NC}"
if grep -q -i "repair" analysis.log; then
    echo -e "${GREEN}Found repair output:${NC}"
    grep -i "repair" analysis.log | while IFS= read -r line; do
        echo "  $line"
    done
else
    echo -e "${YELLOW}No repair output found in logs${NC}"
    echo "This could mean:"
    echo "  1. No null pointer issues were found"
    echo "  2. Repair functionality is not enabled in this build"
    echo "  3. The file doesn't contain repairable issues"
fi

echo ""
echo -e "${BLUE}=== Infer Report ===${NC}"
infer report

echo ""
echo -e "${BLUE}=== Files Generated ===${NC}"
echo "Analysis log: $WORK_DIR/analysis.log"
echo "Infer output: $WORK_DIR/infer-out/"

echo ""
echo -e "${YELLOW}To clean up temporary files, run:${NC}"
echo "  rm -rf $WORK_DIR"