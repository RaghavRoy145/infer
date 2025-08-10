#!/bin/bash

# Script to run Infer analysis using local installation
# Usage: ./local-run-infer.sh <path-to-file> [additional-infer-options]

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
    echo "Usage: $0 <path-to-file> [additional-infer-options]"
    echo "Examples:"
    echo "  $0 examples/c_hello/example.c"
    echo "  $0 examples/java_hello/Hello.java"
    echo "  $0 examples/c_npe/test01_simple_null.c --pulse-only"
    exit 1
fi

INPUT_FILE="$1"
shift # Remove first argument to pass the rest to infer

# Check if file exists
if [ ! -f "$INPUT_FILE" ]; then
    echo -e "${RED}Error: File '$INPUT_FILE' not found${NC}"
    exit 1
fi

# Get absolute path
INPUT_FILE_ABS=$(cd "$(dirname "$INPUT_FILE")" && pwd)/$(basename "$INPUT_FILE")
FILENAME=$(basename "$INPUT_FILE")
FILE_EXT="${FILENAME##*.}"

echo -e "${BLUE}=== Running Infer Analysis ===${NC}"
echo -e "${GREEN}Input file:${NC} $INPUT_FILE_ABS"
echo -e "${GREEN}File type:${NC} .$FILE_EXT"
echo ""

# Create a temporary working directory
WORK_DIR=$(mktemp -d -t infer-analysis-XXXXXX)
echo -e "${YELLOW}Working directory:${NC} $WORK_DIR"

# Set path to local infer binary BEFORE changing directory
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
INFER_DIR="$SCRIPT_DIR/infer/bin"
export PATH="$INFER_DIR:$PATH"

if [ ! -f "$INFER_DIR/infer" ]; then
    echo -e "${RED}Error: Infer not found at $INFER_DIR/infer${NC}"
    echo "Please ensure Infer is built and installed in the infer/bin directory"
    exit 1
fi

# Copy the input file to working directory
cp "$INPUT_FILE_ABS" "$WORK_DIR/$FILENAME"
cd "$WORK_DIR"

# Determine the compiler based on file extension
case "$FILE_EXT" in
    c)
        COMPILER="clang -c"
        echo -e "${GREEN}Using compiler:${NC} clang"
        ;;
    cpp|cc|cxx)
        COMPILER="clang++ -c"
        echo -e "${GREEN}Using compiler:${NC} clang++"
        ;;
    java)
        COMPILER="javac"
        echo -e "${GREEN}Using compiler:${NC} javac"
        ;;
    m)
        COMPILER="clang -c -fobjc-arc"
        echo -e "${GREEN}Using compiler:${NC} clang (Objective-C)"
        ;;
    *)
        echo -e "${RED}Error: Unsupported file type .$FILE_EXT${NC}"
        echo "Supported types: .c, .cpp, .cc, .cxx, .java, .m"
        rm -rf "$WORK_DIR"
        exit 1
        ;;
esac


# Run Infer
echo ""
echo -e "${BLUE}Running Infer...${NC}"
echo "Command: infer run $@ -- $COMPILER $FILENAME"
echo ""

infer run "$@" -- $COMPILER "$FILENAME"

echo ""
echo -e "${GREEN}=== Analysis Complete ===${NC}"
echo ""

# Show report
echo -e "${BLUE}=== Infer Report ===${NC}"
infer report

# Show summary
echo ""
echo -e "${BLUE}=== Summary ===${NC}"
ISSUES=$(infer report --issues-tests 2>/dev/null | wc -l)
if [ "$ISSUES" -gt 0 ]; then
    echo -e "${YELLOW}Found $ISSUES issue(s)${NC}"
else
    echo -e "${GREEN}No issues found!${NC}"
fi

echo ""
echo -e "${BLUE}=== Files Generated ===${NC}"
echo "Infer output: $WORK_DIR/infer-out/"
echo "Full report: $WORK_DIR/infer-out/report.txt"

echo ""
echo -e "${YELLOW}To clean up temporary files, run:${NC}"
echo "  rm -rf $WORK_DIR"