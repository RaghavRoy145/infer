#!/bin/bash

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color
DIM='\033[2m'

echo -e "${BLUE}=== Building Infer from repair branch ===${NC}"
echo -e "${YELLOW}This will clone and build from github.com/RaghavRoy145/infer (repair branch)${NC}"
echo -e "${DIM}Using pre-built LLVM/Clang to avoid the 73% build failure${NC}"
echo ""

# Check if we're on Apple Silicon
if [[ "$(uname -m)" == "arm64" ]]; then
    echo -e "${YELLOW}Detected Apple Silicon - using linux/amd64 platform for compatibility${NC}"
    PLATFORM_FLAG="--platform linux/amd64"
else
    PLATFORM_FLAG=""
fi

# Build the Docker image
echo -e "${GREEN}Building Docker image...${NC}"
echo -e "${DIM}This will take 20-30 minutes (faster than before due to using system clang)${NC}"

# Build with platform flag if needed - show full output
docker build $PLATFORM_FLAG -t infer-repair . 2>&1 | tee docker-build.log

# Check if build succeeded
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo -e "${RED}Build failed!${NC}"
    echo -e "${YELLOW}Check docker-build.log for details${NC}"
    echo -e "${YELLOW}Last 50 lines of the log:${NC}"
    tail -50 docker-build.log
    exit 1
fi

echo ""
echo -e "${GREEN}✓ Build successful!${NC}"
echo -e "${BLUE}The image 'infer-repair' contains Infer from the repair branch${NC}"
echo ""
echo -e "${YELLOW}To test repair functionality:${NC}"
echo "  docker run -it $PLATFORM_FLAG infer-repair bash"
echo ""
echo "Inside the container, run:"
echo "  ./test_repair.sh"
echo ""
echo "Or test with your own C files:"
echo "  ./run-repair.sh ../../examples/c_npe/test01_simple_null.c"