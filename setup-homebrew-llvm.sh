#!/bin/bash

# Script to set up consistent LLVM/Clang for Infer build
set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}=== Setting up Homebrew LLVM for Infer ===${NC}"
echo ""

# Check if Homebrew LLVM is installed
if ! brew list llvm &>/dev/null; then
    echo -e "${RED}Error: Homebrew LLVM not installed${NC}"
    echo "Please run: brew install llvm"
    exit 1
fi

LLVM_PREFIX="/opt/homebrew/opt/llvm"
echo -e "${GREEN}Using LLVM from:${NC} $LLVM_PREFIX"
echo -e "${GREEN}LLVM version:${NC} $($LLVM_PREFIX/bin/llvm-config --version)"
echo ""

# Set up environment variables
echo -e "${BLUE}Setting up environment variables...${NC}"
export PATH="$LLVM_PREFIX/bin:$PATH"
export CC="$LLVM_PREFIX/bin/clang"
export CXX="$LLVM_PREFIX/bin/clang++"
export LDFLAGS="-L$LLVM_PREFIX/lib"
export CPPFLAGS="-I$LLVM_PREFIX/include"
export LLVM_CONFIG="$LLVM_PREFIX/bin/llvm-config"

echo "CC=$CC"
echo "CXX=$CXX"
echo "LLVM_CONFIG=$LLVM_CONFIG"
echo ""

# Clean old build artifacts
echo -e "${BLUE}Cleaning old build artifacts...${NC}"
if [ -d "facebook-clang-plugins/clang/install" ]; then
    echo "Removing old clang install..."
    rm -rf facebook-clang-plugins/clang/install
fi

if [ -d "facebook-clang-plugins/libtooling/build" ]; then
    echo "Removing old plugin build..."
    rm -rf facebook-clang-plugins/libtooling/build
fi

# Set up facebook-clang-plugins to use Homebrew LLVM
echo ""
echo -e "${BLUE}Configuring facebook-clang-plugins...${NC}"
cd facebook-clang-plugins/clang

# Create install directory structure
mkdir -p install/bin
mkdir -p install/lib
mkdir -p install/include

# Link Homebrew LLVM into the install directory
echo "Linking Homebrew LLVM..."
ln -sf $LLVM_PREFIX/bin/clang install/bin/clang
ln -sf $LLVM_PREFIX/bin/clang++ install/bin/clang++
ln -sf $LLVM_PREFIX/bin/llvm-config install/bin/llvm-config

# Link lib and include directories properly
rm -rf install/lib install/include
ln -sf $LLVM_PREFIX/lib install/lib
ln -sf $LLVM_PREFIX/include install/include

# Mark as installed
echo "$($LLVM_PREFIX/bin/llvm-config --version)" > installed.version

cd ../..

# Build the plugin
echo ""
echo -e "${BLUE}Building facebook-clang-plugins...${NC}"
cd facebook-clang-plugins
make clean || true

# Build with Homebrew LLVM
CLANG_PREFIX="$LLVM_PREFIX" \
CC="$LLVM_PREFIX/bin/clang" \
CXX="$LLVM_PREFIX/bin/clang++" \
make

cd ..

echo ""
echo -e "${GREEN}✓ Facebook clang plugins configured with Homebrew LLVM${NC}"
echo ""

# Now rebuild Infer
echo -e "${BLUE}Ready to rebuild Infer. Run these commands:${NC}"
echo ""
echo "export PATH=\"$LLVM_PREFIX/bin:\$PATH\""
echo "export CC=\"$LLVM_PREFIX/bin/clang\""
echo "export CXX=\"$LLVM_PREFIX/bin/clang++\""
echo "export LLVM_CONFIG=\"$LLVM_PREFIX/bin/llvm-config\""
echo ""
echo "# Clean and rebuild Infer:"
echo "make clean"
echo "./build-infer.sh clang"
echo ""
echo -e "${YELLOW}Note: The build will take 20-30 minutes${NC}"