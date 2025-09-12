#!/bin/bash

# Script to rebuild Infer with system clang (simpler approach)
set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}=== Rebuilding Infer with System Clang ===${NC}"
echo ""

# Use system clang
echo -e "${GREEN}Using system clang:${NC}"
which clang
clang --version | head -1
echo ""

# Clean everything
echo -e "${BLUE}Cleaning old builds...${NC}"
make clean || true
rm -rf facebook-clang-plugins/clang/install
rm -rf facebook-clang-plugins/libtooling/build
rm -rf infer/bin
echo ""

# Set environment for system clang
export CC=/usr/bin/clang
export CXX=/usr/bin/clang++

echo -e "${BLUE}Building Infer (this will take 20-30 minutes)...${NC}"
echo "This will download and build the matching clang/LLVM for the plugins"
echo ""

# Build Infer with clang support
# This will handle the facebook-clang-plugins automatically
./build-infer.sh clang

echo ""
echo -e "${GREEN}✓ Build complete!${NC}"
echo ""
echo "Test with:"
echo "  ./local-run-infer.sh examples/c_hello/example.c"
echo "  ./local-run-repair.sh examples/c_npe/test01_simple_null.c"