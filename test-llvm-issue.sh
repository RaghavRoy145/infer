#!/bin/bash

# Script to diagnose LLVM/Clang plugin issues with Infer

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

echo -e "${BLUE}=== Diagnosing LLVM/Clang Plugin Issues ===${NC}"
echo ""

# 1. Check Infer version
echo -e "${GREEN}1. Infer version:${NC}"
infer/bin/infer --version
echo ""

# 2. Check system clang version
echo -e "${GREEN}2. System clang version:${NC}"
clang --version | head -1
echo ""

# 3. Check LLVM version
echo -e "${GREEN}3. LLVM version:${NC}"
if command -v llvm-config &> /dev/null; then
    llvm-config --version
else
    echo "llvm-config not found in PATH"
fi
echo ""

# 4. Check if the plugin exists
PLUGIN_PATH="facebook-clang-plugins/libtooling/build/FacebookClangPlugin.dylib"
echo -e "${GREEN}4. Checking for clang plugin:${NC}"
if [ -f "$PLUGIN_PATH" ]; then
    echo "Plugin found at: $PLUGIN_PATH"
    echo "Plugin size: $(ls -lh "$PLUGIN_PATH" | awk '{print $5}')"
    echo ""
    
    # Check plugin dependencies
    echo -e "${GREEN}5. Plugin dependencies:${NC}"
    otool -L "$PLUGIN_PATH" | head -10
    echo ""
    
    # Check for the missing symbol
    echo -e "${GREEN}6. Checking for the missing symbol:${NC}"
    nm -U "$PLUGIN_PATH" 2>/dev/null | grep -i "DisableABIBreakingChecks" || echo "Symbol not found in plugin"
else
    echo -e "${RED}Plugin not found at: $PLUGIN_PATH${NC}"
    echo "This explains why Infer can't load it!"
fi
echo ""

# 7. Check Infer's expected plugin location
echo -e "${GREEN}7. Where Infer is looking for the plugin:${NC}"
echo "Based on the error, Infer expects it at:"
echo "  infer/bin/../../facebook-clang-plugins/libtooling/build/FacebookClangPlugin.dylib"
echo "Which resolves to:"
echo "  $(cd infer/bin/../.. && pwd)/facebook-clang-plugins/libtooling/build/FacebookClangPlugin.dylib"
echo ""

# 8. Try a simple C file without the plugin
echo -e "${GREEN}8. Testing Infer without plugin (Java-style analysis):${NC}"
cat > test_simple.c << 'EOF'
#include <stdio.h>
int main() {
    int *p = NULL;
    *p = 42;
    return 0;
}
EOF

echo "Created test_simple.c with null pointer dereference"
echo ""

# Try running without the plugin
echo -e "${YELLOW}Attempting to run Infer with --no-clang-biniou-ast flag:${NC}"
infer/bin/infer run --no-clang-biniou-ast -- clang -c test_simple.c 2>&1 | head -20 || true

echo ""
echo -e "${BLUE}=== Diagnosis Summary ===${NC}"
echo "The issue is that Infer is trying to load a clang plugin that either:"
echo "1. Wasn't built (missing FacebookClangPlugin.dylib)"
echo "2. Has LLVM version mismatch (symbol not found error)"
echo "3. Is in the wrong location"
echo ""
echo "To fix this, you need to either:"
echo "a) Rebuild the facebook-clang-plugins with matching LLVM version"
echo "b) Use Infer without C/C++ support (Java only)"
echo "c) Use the Docker version which has everything properly configured"

# Cleanup
rm -f test_simple.c