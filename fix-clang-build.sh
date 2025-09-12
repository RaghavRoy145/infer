#!/bin/bash

# Script to fix the clang build by disabling iOS simulator runtimes
set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}=== Fixing Clang Build (Disabling iOS Runtimes) ===${NC}"
echo ""

# Clean the failed build
echo -e "${YELLOW}Cleaning failed build...${NC}"
make clean || true
rm -rf /var/folders/gp/g16cpdpx53l91wj7flmwy6q00000gn/T/clang-setup.*
echo ""

# Modify the clang setup script to disable iOS runtimes
echo -e "${BLUE}Patching clang setup script...${NC}"

# Create a modified setup script
cat > facebook-clang-plugins/clang/setup-fixed.sh << 'EOF'
#!/bin/bash
# Modified setup script that disables iOS runtimes

set -e
set -o pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLANG_PREFIX="${CLANG_PREFIX:-$SCRIPT_DIR/install}"
CLANG_SRC="$SCRIPT_DIR/src/download"
BUILD_DIR="${BUILD_DIR:-$(mktemp -d -t clang-setup.XXXXXX)}"

echo "Building clang in $BUILD_DIR"
echo "Will install to $CLANG_PREFIX"

cd "$BUILD_DIR"

# Configure with iOS runtimes disabled
cmake -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_INSTALL_PREFIX="$CLANG_PREFIX" \
  -DLLVM_ENABLE_PROJECTS="clang;openmp" \
  -DLLVM_TARGETS_TO_BUILD="X86;ARM;AArch64" \
  -DCOMPILER_RT_BUILD_IOSSIM_RUNTIMES=OFF \
  -DCOMPILER_RT_BUILD_IOS_RUNTIMES=OFF \
  -DCOMPILER_RT_BUILD_TVOS_RUNTIMES=OFF \
  -DCOMPILER_RT_BUILD_WATCHOS_RUNTIMES=OFF \
  -DCOMPILER_RT_ENABLE_IOS=OFF \
  -DCOMPILER_RT_ENABLE_TVOS=OFF \
  -DCOMPILER_RT_ENABLE_WATCHOS=OFF \
  "$CLANG_SRC/llvm-project/llvm"

# Build
ninja

# Install
ninja install

echo "Clang built successfully!"
EOF

chmod +x facebook-clang-plugins/clang/setup-fixed.sh

echo ""
echo -e "${BLUE}Building Infer with fixed setup...${NC}"
echo ""

# Build with the fixed setup script
export CC=/usr/bin/clang
export CXX=/usr/bin/clang++

# Modify build-infer.sh to use our fixed setup
sed -i.bak 's|./setup.sh|./setup-fixed.sh|g' facebook-clang-plugins/clang/setup.sh 2>/dev/null || true

# Build Infer
./build-infer.sh clang

echo ""
echo -e "${GREEN}✓ Build should complete without iOS runtime errors${NC}"