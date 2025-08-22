#!/bin/bash

# EffFix NPE Bugs Setup Script
# Downloads, extracts, and optionally builds all NPE (Null Pointer Dereference) bugs from EffFix benchmark
# for use with external APR tools

set -e  # Exit on error

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Parse command line arguments
BUILD_PROJECTS=false
WORK_DIR=""
SHOW_HELP=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --build)
            BUILD_PROJECTS=true
            shift
            ;;
        --help|-h)
            SHOW_HELP=true
            shift
            ;;
        *)
            WORK_DIR="$1"
            shift
            ;;
    esac
done

# Show help if requested
if [ "$SHOW_HELP" = true ]; then
    cat << EOF
Usage: $0 [OPTIONS] [WORKSPACE_DIR]

Downloads and optionally builds NPE bugs from EffFix benchmark.

OPTIONS:
    --build     Also build the projects after downloading (takes 1-2 hours)
    --help, -h  Show this help message

ARGUMENTS:
    WORKSPACE_DIR  Directory to store bugs (default: ./npe_bugs_workspace)

EXAMPLES:
    # Download only (fast, ~500MB)
    $0

    # Download and build (slow, ~10GB, requires build tools)
    $0 --build

    # Use custom directory
    $0 --build /path/to/workspace

EOF
    exit 0
fi

# Configuration
SCRIPT_NAME="$(basename "${BASH_SOURCE[0]}")"
WORK_DIR="${WORK_DIR:-./npe_bugs_workspace}"
GITHUB_REPO="https://raw.githubusercontent.com/nus-apr/efffix-benchmark/main"

# Create main working directory
mkdir -p "$WORK_DIR"
WORK_DIR="$(cd "$WORK_DIR" && pwd)"  # Convert to absolute path

echo -e "${GREEN}=== EffFix NPE Bugs Setup Script ===${NC}"
echo "Working directory: $WORK_DIR"
if [ "$BUILD_PROJECTS" = true ]; then
    echo -e "${BLUE}Mode: Download + Build${NC}"
else
    echo -e "${BLUE}Mode: Download only (use --build flag to also build projects)${NC}"
fi
echo ""

# NPE bugs information
declare -A NPE_BUGS=(
    ["null-ptr-1-openssl-1"]="openssl-1:openssl-1-instrumented.tar.gz:crypto/x509/x509_vpm.c:91:92:CC=gcc ./config:make"
    ["null-ptr-2-openssl-1"]="openssl-1:openssl-1-instrumented.tar.gz:crypto/dh/dh_check.c:128:132:CC=gcc ./config:make"
    ["null-ptr-3-openssl-1"]="openssl-1:openssl-1-instrumented.tar.gz:crypto/ocsp/ocsp_ht.c:160:161:CC=gcc ./config:make"
    ["null-ptr-4-openssl-1"]="openssl-1:openssl-1-instrumented.tar.gz:crypto/mem.c:329:331:CC=gcc ./config:make"
    ["null-ptr-5-openssl-1"]="openssl-1:openssl-1-instrumented.tar.gz:ssl/d1_both.c:1181:1183:CC=gcc ./config:make"
    ["null-ptr-6-openssl-3"]="openssl-3:openssl-3-instrumented.tar.gz:apps/lib/s_cb.c:957:959:CC=gcc ./config:make -j32"
    ["null-ptr-7-openssl-3"]="openssl-3:openssl-3-instrumented.tar.gz:apps/s_server.c:3575:3578:CC=gcc ./config:make -j32"
    ["null-ptr-8-openssl-3"]="openssl-3:openssl-3-instrumented.tar.gz:test/params_test.c:100:102:CC=gcc ./config:make -j32"
    ["null-ptr-9-linux-kernel-5"]="linux-kernel-5:SKIP:tools/lib/subcmd/help.c:18:20:make CC=clang defconfig:make CC=clang -j32"
)

# Function to download tarball
download_tarball() {
    local tarball=$1
    local dest_dir=$2
    
    if [ ! -f "$dest_dir/$tarball" ]; then
        echo -e "${YELLOW}  Downloading $tarball...${NC}"
        if command -v wget >/dev/null 2>&1; then
            wget -q -O "$dest_dir/$tarball" "$GITHUB_REPO/source/$tarball" || {
                echo -e "${RED}  Failed to download $tarball${NC}"
                return 1
            }
        elif command -v curl >/dev/null 2>&1; then
            curl -sL -o "$dest_dir/$tarball" "$GITHUB_REPO/source/$tarball" || {
                echo -e "${RED}  Failed to download $tarball${NC}"
                return 1
            }
        else
            echo -e "${RED}  Neither wget nor curl found. Please install one of them.${NC}"
            return 1
        fi
    else
        echo "  $tarball already downloaded"
    fi
    return 0
}

# Function to download and extract a bug
download_bug() {
    local bug_id=$1
    local bug_info=$2
    
    IFS=':' read -r project tarball bug_file src_line sink_line config_cmd build_cmd <<< "$bug_info"
    
    echo -e "${GREEN}Processing $bug_id${NC}"
    echo "  Project: $project"
    echo "  Bug file: $bug_file (lines $src_line-$sink_line)"
    
    local bug_dir="$WORK_DIR/$bug_id"
    mkdir -p "$bug_dir"
    
    # Special case for Linux kernel
    if [ "$tarball" == "SKIP" ]; then
        echo -e "${YELLOW}  Linux kernel requires git clone (large). Setting up directory structure only.${NC}"
        
        # Create info file with instructions
        cat > "$bug_dir/README.txt" <<EOF
Linux Kernel NPE Bug - Manual Setup Required

Bug ID: $bug_id
File: $bug_file
NPE Lines: $src_line -> $sink_line

To setup manually:
1. Clone Linux kernel:
   git clone --depth 1 https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git src
   cd src
   git checkout 5b78ed24e8ec48602c1d6f5a188e58d000c81e2b

2. Configure:
   $config_cmd

3. Build:
   $build_cmd

The NPE bug is in: $bug_file
EOF
        
        # Create bug info file
        cat > "$bug_dir/bug_info.txt" <<EOF
Bug ID: $bug_id
Project: $project
Bug Type: Null Pointer Dereference
Source File: $bug_file
NPE Source Line: $src_line
NPE Sink Line: $sink_line
Configure Command: $config_cmd
Build Command: $build_cmd
Status: Requires manual setup (see README.txt)
EOF
        
        echo -e "${YELLOW}  See $bug_dir/README.txt for manual setup instructions${NC}"
        echo ""
        return 0
    fi
    
    # Download tarball if needed
    if ! download_tarball "$tarball" "$WORK_DIR"; then
        echo -e "${RED}  Skipping $bug_id due to download failure${NC}"
        echo ""
        return 1
    fi
    
    # Extract source
    echo "  Extracting source code..."
    cd "$bug_dir"
    rm -rf src
    mkdir -p src
    tar -xzf "$WORK_DIR/$tarball" -C src --strip-components=1 2>/dev/null || {
        echo -e "${RED}  Failed to extract $tarball${NC}"
        echo ""
        return 1
    }
    
    # Create bug info file
    cat > "$bug_dir/bug_info.txt" <<EOF
Bug ID: $bug_id
Project: $project
Bug Type: Null Pointer Dereference
Source File: $bug_file
NPE Source Line: $src_line
NPE Sink Line: $sink_line
Configure Command: $config_cmd
Build Command: $build_cmd
Status: Source extracted, not built
EOF
    
    echo -e "${GREEN}  ✓ $bug_id source downloaded and extracted${NC}"
    echo "    Source: $bug_dir/src/"
    echo "    Bug location: $bug_dir/src/$bug_file"
    echo ""
    
    return 0
}

# Function to build a bug
build_bug() {
    local bug_id=$1
    local bug_info=$2
    
    IFS=':' read -r project tarball bug_file src_line sink_line config_cmd build_cmd <<< "$bug_info"
    
    # Skip Linux kernel
    if [ "$tarball" == "SKIP" ]; then
        return 0
    fi
    
    local bug_dir="$WORK_DIR/$bug_id"
    
    if [ ! -d "$bug_dir/src" ]; then
        echo -e "${YELLOW}  Source not found for $bug_id, skipping build${NC}"
        return 1
    fi
    
    echo -e "${GREEN}Building $bug_id${NC}"
    
    # Configure the project
    echo "  Configuring project..."
    cd "$bug_dir/src"
    eval "$config_cmd" > ../configure.log 2>&1 || {
        echo -e "${RED}  Configuration failed. Check $bug_dir/configure.log${NC}"
        echo ""
        return 1
    }
    
    # Build the project
    echo "  Building project (this may take a while)..."
    eval "$build_cmd" > ../build.log 2>&1 || {
        echo -e "${YELLOW}  Build had warnings/errors. Check $bug_dir/build.log${NC}"
        # Don't return failure as some projects may have non-critical build issues
    }
    
    # Update bug info file
    sed -i.bak 's/Status: Source extracted, not built/Status: Built successfully/' "$bug_dir/bug_info.txt" 2>/dev/null || \
    sed -i '' 's/Status: Source extracted, not built/Status: Built successfully/' "$bug_dir/bug_info.txt" 2>/dev/null || true
    
    echo -e "${GREEN}  ✓ $bug_id built successfully${NC}"
    echo ""
    
    return 0
}

# Function to check build dependencies
check_build_dependencies() {
    echo -e "${GREEN}Checking build dependencies...${NC}"
    
    local missing_deps=()
    
    # Check for required build tools
    command -v make >/dev/null 2>&1 || missing_deps+=("make")
    command -v gcc >/dev/null 2>&1 || missing_deps+=("gcc")
    command -v perl >/dev/null 2>&1 || missing_deps+=("perl")
    
    if [ ${#missing_deps[@]} -gt 0 ]; then
        echo -e "${YELLOW}Missing build dependencies: ${missing_deps[*]}${NC}"
        echo "Please install them before building."
        
        # Provide installation command for common systems
        if [ -f /etc/debian_version ]; then
            echo "On Debian/Ubuntu, run:"
            echo "  sudo apt-get install build-essential perl"
        elif [ -f /etc/redhat-release ]; then
            echo "On RHEL/CentOS/Fedora, run:"
            echo "  sudo yum groupinstall 'Development Tools'"
            echo "  sudo yum install perl"
        elif [ "$(uname)" == "Darwin" ]; then
            echo "On macOS with Xcode command line tools:"
            echo "  xcode-select --install"
        fi
        
        read -p "Continue anyway? (y/n) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            exit 1
        fi
    else
        echo "All build dependencies are installed."
    fi
    echo ""
}

# Function to check download dependencies
check_download_dependencies() {
    echo -e "${GREEN}Checking download dependencies...${NC}"
    
    if ! command -v wget >/dev/null 2>&1 && ! command -v curl >/dev/null 2>&1; then
        echo -e "${RED}Neither wget nor curl found.${NC}"
        echo "Please install one of them:"
        echo "  Debian/Ubuntu: sudo apt-get install wget"
        echo "  RHEL/CentOS: sudo yum install wget"
        echo "  macOS: brew install wget"
        exit 1
    fi
    
    command -v tar >/dev/null 2>&1 || {
        echo -e "${RED}tar not found. Please install it.${NC}"
        exit 1
    }
    
    echo "Download dependencies satisfied."
    echo ""
}

# Function to create summary
create_summary() {
    local summary_file="$WORK_DIR/setup_summary.txt"
    
    echo -e "${GREEN}Creating summary...${NC}"
    
    cat > "$summary_file" <<EOF
EffFix NPE Bugs Setup Summary
Generated: $(date)
Working Directory: $WORK_DIR
Mode: $([ "$BUILD_PROJECTS" = true ] && echo "Downloaded and Built" || echo "Downloaded Only")

Setup Bugs:
EOF
    
    local downloaded_count=0
    local built_count=0
    local total=0
    
    for bug_id in "${!NPE_BUGS[@]}"; do
        ((total++))
        if [ -d "$WORK_DIR/$bug_id/src" ] || [ -f "$WORK_DIR/$bug_id/README.txt" ]; then
            IFS=':' read -r project tarball bug_file src_line sink_line config_cmd build_cmd <<< "${NPE_BUGS[$bug_id]}"
            
            if [ -f "$WORK_DIR/$bug_id/build.log" ]; then
                echo "  - $bug_id: $bug_file (lines $src_line-$sink_line) [BUILT]" >> "$summary_file"
                ((built_count++))
                ((downloaded_count++))
            elif [ -d "$WORK_DIR/$bug_id/src" ]; then
                echo "  - $bug_id: $bug_file (lines $src_line-$sink_line) [DOWNLOADED]" >> "$summary_file"
                ((downloaded_count++))
            else
                echo "  - $bug_id: $bug_file (lines $src_line-$sink_line) [MANUAL SETUP REQUIRED]" >> "$summary_file"
            fi
        fi
    done
    
    echo "" >> "$summary_file"
    echo "Total: $downloaded_count/$total downloaded, $built_count/$total built" >> "$summary_file"
    
    if [ "$BUILD_PROJECTS" = false ]; then
        echo "" >> "$summary_file"
        echo "To build the projects, run:" >> "$summary_file"
        echo "  $SCRIPT_NAME --build $WORK_DIR" >> "$summary_file"
    fi
    
    echo "Summary saved to: $summary_file"
    echo -e "${GREEN}Complete! Downloaded: $downloaded_count/$total, Built: $built_count/$total${NC}"
}

# Main execution
main() {
    echo "Starting setup process..."
    echo ""
    
    # Phase 1: Download
    echo -e "${BLUE}=== Phase 1: Download ===${NC}"
    check_download_dependencies
    
    # Download each NPE bug
    local total=${#NPE_BUGS[@]}
    local current=0
    for bug_id in "${!NPE_BUGS[@]}"; do    
        #((current++))
        echo -e "${#NPE_BUGS[@]}, ${current}"; 
        echo "[$current/$total] Downloading $bug_id"
        echo "----------------------------------------"
        download_bug "$bug_id" "${NPE_BUGS[$bug_id]}"
    done
    
    # Phase 2: Build (if requested)
    if [ "$BUILD_PROJECTS" = true ]; then
        echo -e "${BLUE}=== Phase 2: Build ===${NC}"
        check_build_dependencies
        
        current=0
        for bug_id in "${!NPE_BUGS[@]}"; do
            ((current++))
            echo "[$current/$total] Building $bug_id"
            echo "----------------------------------------"
            build_bug "$bug_id" "${NPE_BUGS[$bug_id]}"
        done
    else
        echo -e "${YELLOW}=== Build Phase Skipped ===${NC}"
        echo "To build the projects later, run:"
        echo "  $0 --build $WORK_DIR"
        echo ""
    fi
    
    # Create summary
    create_summary
    
    echo ""
    echo -e "${GREEN}=== Setup Complete ===${NC}"
    echo "All NPE bug projects are in: $WORK_DIR"
    
    if [ "$BUILD_PROJECTS" = true ]; then
        echo "Projects have been built and are ready for your APR tool."
    else
        echo "Source code has been downloaded. Run with --build flag to compile."
    fi
    
    echo ""
    echo "Example usage with your APR tool:"
    echo "  cd $WORK_DIR/null-ptr-1-openssl-1/src"
    echo "  your_apr_tool --bug-file crypto/x509/x509_vpm.c --line 91"
}

# Run main function
main
