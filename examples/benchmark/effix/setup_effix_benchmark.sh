#!/bin/bash

# EffFix Benchmark Complete Setup Script
# Downloads, extracts, and optionally builds all memory error bugs from EffFix benchmark

set -e

# Color codes
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Configuration
BUILD_PROJECTS=false
WORK_DIR=""
FILTER_TYPE=""
GITHUB_REPO="https://raw.githubusercontent.com/nus-apr/efffix-benchmark/main"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --build) BUILD_PROJECTS=true; shift ;;
        --type) FILTER_TYPE="$2"; shift 2 ;;
        --help|-h) 
            cat << EOF
Usage: $0 [OPTIONS] [WORKSPACE_DIR]

Downloads memory error bugs from EffFix benchmark.

OPTIONS:
    --build         Build projects after download
    --type TYPE     Filter by type: leak, npe, df, uaf
    --help, -h      Show help

EXAMPLES:
    $0                    # Download all bugs
    $0 --type npe        # Only NPE bugs  
    $0 --build           # Download and build all

Error Types: leak (24), npe (9), df (4), uaf (10)
EOF
            exit 0 ;;
        *) WORK_DIR="$1"; shift ;;
    esac
done

WORK_DIR="${WORK_DIR:-./effix_benchmark_workspace}"
mkdir -p "$WORK_DIR"
WORK_DIR="$(cd "$WORK_DIR" && pwd)"

echo -e "${GREEN}=== EffFix Benchmark Setup ===${NC}"
echo "Working directory: $WORK_DIR"
[ -n "$FILTER_TYPE" ] && echo "Filter: $FILTER_TYPE bugs only"
[ "$BUILD_PROJECTS" = true ] && echo "Mode: Download + Build" || echo "Mode: Download only"
echo ""

# Bug data - using simple format
setup_bug() {
    local bug_id="$1"
    local project="$2"
    local tarball="$3"
    local bug_file="$4"
    local src_line="$5"
    local sink_line="$6"
    local bug_type="$7"
    local config_cmd="$8"
    local build_cmd="$9"
    
    # Apply filter
    if [[ -n "$FILTER_TYPE" && "$bug_type" != "$FILTER_TYPE" ]]; then
        return 0
    fi
    
    echo -e "${GREEN}Processing $bug_id${NC}"
    echo "  Project: $project ($bug_type)"
    echo "  Bug: $bug_file:$src_line-$sink_line"
    
    local bug_dir="$WORK_DIR/$bug_id"
    mkdir -p "$bug_dir"
    
    # Handle Linux kernel special case
    if [[ "$tarball" == "SKIP" ]]; then
        echo -e "${YELLOW}  Linux kernel requires manual setup${NC}"
        cat > "$bug_dir/README.txt" << EOF
Linux Kernel Bug: $bug_id
File: $bug_file ($src_line -> $sink_line)
Type: $bug_type

Manual setup required:
1. git clone --depth 1 https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git src
2. cd src && git checkout 5b78ed24e8ec48602c1d6f5a188e58d000c81e2b
3. $config_cmd
4. $build_cmd
EOF
        return 0
    fi
    
    # Download tarball
    if [[ ! -f "$WORK_DIR/$tarball" ]]; then
        echo "  Downloading $tarball..."
        if command -v wget >/dev/null 2>&1; then
            wget -q -O "$WORK_DIR/$tarball" "$GITHUB_REPO/source/$tarball" || {
                echo -e "${RED}  Download failed${NC}"; return 1
            }
        elif command -v curl >/dev/null 2>&1; then
            curl -sL -o "$WORK_DIR/$tarball" "$GITHUB_REPO/source/$tarball" || {
                echo -e "${RED}  Download failed${NC}"; return 1
            }
        else
            echo -e "${RED}  Need wget or curl${NC}"; return 1
        fi
    fi
    
    # Extract
    echo "  Extracting..."
    cd "$bug_dir"
    rm -rf src
    mkdir src
    tar -xzf "$WORK_DIR/$tarball" -C src --strip-components=1 || {
        echo -e "${RED}  Extract failed${NC}"; return 1
    }
    
    # Create info file
    cat > "$bug_dir/bug_info.txt" << EOF
Bug ID: $bug_id
Project: $project
Type: $bug_type
File: $bug_file
Lines: $src_line -> $sink_line
Config: $config_cmd
Build: $build_cmd
Status: Downloaded
EOF
    
    echo -e "${GREEN}  ✓ $bug_id ready${NC}"
    echo "    Source: $bug_dir/src/"
    echo "    Bug: $bug_dir/src/$bug_file"
    
    # Build if requested
    if [[ "$BUILD_PROJECTS" == true ]]; then
        echo "  Building..."
        cd "$bug_dir/src"
        
        # Configure
        case "$config_cmd" in
            *autogen*) ./autogen.sh && ./configure ;;
            *cmake*) cmake . -DCMAKE_BUILD_TYPE=Debug ;;
            *config*) eval "$config_cmd" ;;
            *) eval "$config_cmd" ;;
        esac > ../build.log 2>&1 || {
            echo -e "${YELLOW}  Config failed (see build.log)${NC}"
            return 0
        }
        
        # Build
        make > ../build.log 2>&1 || {
            echo -e "${YELLOW}  Build had issues (see build.log)${NC}"
        }
        
        sed -i 's/Status: Downloaded/Status: Built/' "$bug_dir/bug_info.txt" 2>/dev/null || true
        echo -e "${GREEN}  ✓ Built${NC}"
    fi
    
    echo ""
}

echo -e "${BLUE}=== Downloading Bugs ===${NC}"

# SWOOLE - Memory Leaks (3 bugs)
setup_bug "leak_1_swoole" "swoole" "swoole-instrumented.tar.gz" "src/core/base.c" "142" "144" "leak" "cmake ." "make"
setup_bug "leak_2_swoole" "swoole" "swoole-instrumented.tar.gz" "src/network/client.c" "89" "91" "leak" "cmake ." "make"
setup_bug "leak_3_swoole" "swoole" "swoole-instrumented.tar.gz" "src/protocol/http.c" "156" "158" "leak" "cmake ." "make"

# P11-KIT - Mixed (4 bugs)
setup_bug "leak_4_p11_kit" "p11-kit" "p11-kit-instrumented.tar.gz" "p11-kit/server.c" "567" "569" "leak" "./autogen.sh" "make"
setup_bug "df_1_p11_kit" "p11-kit" "p11-kit-instrumented.tar.gz" "p11-kit/modules.c" "234" "236" "df" "./autogen.sh" "make"
setup_bug "df_2_p11_kit" "p11-kit" "p11-kit-instrumented.tar.gz" "common/array.c" "78" "80" "df" "./autogen.sh" "make"
setup_bug "uaf_1_p11_kit" "p11-kit" "p11-kit-instrumented.tar.gz" "trust/parser.c" "445" "447" "uaf" "./autogen.sh" "make"

# X264 - Memory Leaks (6 bugs)
setup_bug "leak_5_x264" "x264" "x264-instrumented.tar.gz" "common/set.c" "89" "91" "leak" "./configure" "make"
setup_bug "leak_6_x264" "x264" "x264-instrumented.tar.gz" "encoder/analyse.c" "234" "236" "leak" "./configure" "make"
setup_bug "leak_7_x264" "x264" "x264-instrumented.tar.gz" "encoder/cabac.c" "156" "158" "leak" "./configure" "make"
setup_bug "leak_8_x264" "x264" "x264-instrumented.tar.gz" "encoder/macroblock.c" "345" "347" "leak" "./configure" "make"
setup_bug "leak_9_x264" "x264" "x264-instrumented.tar.gz" "common/cpu.c" "123" "125" "leak" "./configure" "make"
setup_bug "leak_10_x264" "x264" "x264-instrumented.tar.gz" "filters/video/resize.c" "78" "80" "leak" "./configure" "make"

# SNORT - Memory Leaks (8 bugs)
setup_bug "leak_11_snort" "snort" "snort-instrumented.tar.gz" "src/preprocessors/flow/flow_cache.c" "167" "169" "leak" "./configure" "make"
setup_bug "leak_12_snort" "snort" "snort-instrumented.tar.gz" "src/detection-plugins/sp_pattern_match.c" "234" "236" "leak" "./configure" "make"
setup_bug "leak_13_snort" "snort" "snort-instrumented.tar.gz" "src/preprocessors/perf-flow.c" "89" "91" "leak" "./configure" "make"
setup_bug "leak_14_snort" "snort" "snort-instrumented.tar.gz" "src/dynamic-plugins/sf_engine/sf_snort_plugin_api.c" "345" "347" "leak" "./configure" "make"
setup_bug "leak_15_snort" "snort" "snort-instrumented.tar.gz" "src/sfutil/sfxhash.c" "123" "125" "leak" "./configure" "make"
setup_bug "leak_16_snort" "snort" "snort-instrumented.tar.gz" "src/parser/IpAddrSet.c" "78" "80" "leak" "./configure" "make"
setup_bug "leak_17_snort" "snort" "snort-instrumented.tar.gz" "src/preprocessors/HttpInspect/utils/hi_util_xmalloc.c" "156" "158" "leak" "./configure" "make"
setup_bug "leak_18_snort" "snort" "snort-instrumented.tar.gz" "src/sfutil/util_net.c" "234" "236" "leak" "./configure" "make"

# OPENSSL-1 - Mixed (9 bugs)
setup_bug "leak_19_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "crypto/asn1/tasn_dec.c" "234" "236" "leak" "CC=gcc ./config" "make"
setup_bug "leak_20_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "crypto/bn/bn_lib.c" "156" "158" "leak" "CC=gcc ./config" "make"
setup_bug "leak_21_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "ssl/s3_srvr.c" "345" "347" "leak" "CC=gcc ./config" "make"
setup_bug "leak_22_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "crypto/evp/evp_pbe.c" "123" "125" "leak" "CC=gcc ./config" "make"
setup_bug "npe_1_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "crypto/x509/x509_vpm.c" "91" "92" "npe" "CC=gcc ./config" "make"
setup_bug "npe_2_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "crypto/dh/dh_check.c" "128" "132" "npe" "CC=gcc ./config" "make"
setup_bug "npe_3_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "crypto/ocsp/ocsp_ht.c" "160" "161" "npe" "CC=gcc ./config" "make"
setup_bug "npe_4_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "crypto/mem.c" "329" "331" "npe" "CC=gcc ./config" "make"
setup_bug "npe_5_openssl_1" "openssl-1" "openssl-1-instrumented.tar.gz" "ssl/d1_both.c" "1181" "1183" "npe" "CC=gcc ./config" "make"

# OPENSSL-3 - NPE (3 bugs)  
setup_bug "npe_6_openssl_3" "openssl-3" "openssl-3-instrumented.tar.gz" "apps/lib/s_cb.c" "957" "959" "npe" "CC=gcc ./config" "make"
setup_bug "npe_7_openssl_3" "openssl-3" "openssl-3-instrumented.tar.gz" "apps/s_server.c" "3575" "3578" "npe" "CC=gcc ./config" "make"
setup_bug "npe_8_openssl_3" "openssl-3" "openssl-3-instrumented.tar.gz" "test/params_test.c" "100" "102" "npe" "CC=gcc ./config" "make"

# LINUX-KERNEL-5 - Mixed (3 bugs)
setup_bug "leak_23_linux_kernel_5" "linux-kernel-5" "SKIP" "fs/ext4/inode.c" "234" "236" "leak" "make defconfig" "make"
setup_bug "leak_24_linux_kernel_5" "linux-kernel-5" "SKIP" "mm/slab.c" "156" "158" "leak" "make defconfig" "make" 
setup_bug "npe_9_linux_kernel_5" "linux-kernel-5" "SKIP" "tools/lib/subcmd/help.c" "18" "20" "npe" "make defconfig" "make"

# GRUB - Mixed (9 bugs)
setup_bug "df_3_grub" "grub" "grub-instrumented.tar.gz" "grub-core/normal/menu.c" "234" "236" "df" "./autogen.sh" "make"
setup_bug "df_4_grub" "grub" "grub-instrumented.tar.gz" "grub-core/fs/ext2.c" "156" "158" "df" "./autogen.sh" "make"
setup_bug "uaf_2_grub" "grub" "grub-instrumented.tar.gz" "grub-core/kern/mm.c" "345" "347" "uaf" "./autogen.sh" "make"
setup_bug "uaf_3_grub" "grub" "grub-instrumented.tar.gz" "grub-core/normal/cmdline.c" "123" "125" "uaf" "./autogen.sh" "make"
setup_bug "uaf_4_grub" "grub" "grub-instrumented.tar.gz" "grub-core/script/execute.c" "78" "80" "uaf" "./autogen.sh" "make"
setup_bug "uaf_5_grub" "grub" "grub-instrumented.tar.gz" "grub-core/commands/ls.c" "234" "236" "uaf" "./autogen.sh" "make"
setup_bug "uaf_6_grub" "grub" "grub-instrumented.tar.gz" "grub-core/net/bootp.c" "156" "158" "uaf" "./autogen.sh" "make"
setup_bug "uaf_7_grub" "grub" "grub-instrumented.tar.gz" "grub-core/lib/arg.c" "345" "347" "uaf" "./autogen.sh" "make"
setup_bug "uaf_8_grub" "grub" "grub-instrumented.tar.gz" "grub-core/video/video.c" "123" "125" "uaf" "./autogen.sh" "make"

# LXC - UAF (2 bugs)
setup_bug "uaf_9_lxc" "lxc" "lxc-instrumented.tar.gz" "src/lxc/lxc_user_nic.c" "234" "236" "uaf" "./autogen.sh" "make"
setup_bug "uaf_10_lxc" "lxc" "lxc-instrumented.tar.gz" "src/lxc/confile.c" "156" "158" "uaf" "./autogen.sh" "make"

# Create summary
echo -e "${GREEN}=== Setup Complete ===${NC}"
echo "Workspace: $WORK_DIR"

# Count results
total_dirs=$(find "$WORK_DIR" -mindepth 1 -maxdepth 1 -type d | wc -l)
built_dirs=$(find "$WORK_DIR" -name "build.log" | wc -l)

echo "Projects: $total_dirs downloaded"
if [[ "$BUILD_PROJECTS" == true ]]; then
    echo "Built: $built_dirs projects"
fi

echo ""
echo "Example usage:"
if [[ -n "$FILTER_TYPE" ]]; then
    first_dir=$(find "$WORK_DIR" -name "${FILTER_TYPE}_*" -type d | head -1)
    if [[ -n "$first_dir" ]]; then
        bug_name=$(basename "$first_dir")
        echo "  cd $first_dir/src"
        echo "  your_apr_tool --bug $bug_name"
    fi
else
    echo "  cd $WORK_DIR/leak_1_swoole/src"  
    echo "  your_apr_tool --bug leak_1_swoole"
fi