# EffFix Benchmark Setup

This directory contains tools to download and set up memory error bugs from the [EffFix benchmark](https://github.com/nus-apr/efffix-benchmark) for testing Automated Program Repair (APR) tools.

## Overview

The EffFix benchmark contains **47 memory error bugs** across 9 real-world C/C++ projects, categorized by error type:

- **Memory Leaks (24 bugs)**: swoole (3), p11-kit (1), x264 (6), snort (8), openssl-1 (4), linux-kernel-5 (2)
- **Null Pointer Dereference (9 bugs)**: openssl-1 (5), openssl-3 (3), linux-kernel-5 (1)
- **Double Free (4 bugs)**: p11-kit (2), grub (2)
- **Use After Free (10 bugs)**: p11-kit (1), grub (7), lxc (2)

## Quick Start

### Download All Bugs (Recommended)

```bash
# Download all 47 bugs (~2GB)
./setup_effix_benchmark.sh

# Download to custom directory
./setup_effix_benchmark.sh /path/to/workspace
```

### Download Specific Error Types

```bash
# Only null pointer dereference bugs (9 bugs)
./setup_effix_benchmark.sh --type npe

# Only memory leak bugs (24 bugs)  
./setup_effix_benchmark.sh --type leak

# Only double free bugs (4 bugs)
./setup_effix_benchmark.sh --type df

# Only use-after-free bugs (10 bugs)
./setup_effix_benchmark.sh --type uaf
```

### Build Projects (Optional)

```bash
# Download and build all projects (~50GB, takes several hours)
./setup_effix_benchmark.sh --build

# Build specific type
./setup_effix_benchmark.sh --build --type npe
```

## Usage

### Script Options

```bash
./setup_effix_benchmark.sh [OPTIONS] [WORKSPACE_DIR]

OPTIONS:
    --build         Build projects after download (requires build tools)
    --type TYPE     Filter by error type: leak, npe, df, uaf
    --help, -h      Show help message

WORKSPACE_DIR:
    Custom directory for bugs (default: ./effix_benchmark_workspace)
```

### Examples

```bash
# Show help
./setup_effix_benchmark.sh --help

# Download all bugs to current directory workspace
./setup_effix_benchmark.sh

# Download only NPE bugs and build them
./setup_effix_benchmark.sh --build --type npe

# Use custom workspace directory
./setup_effix_benchmark.sh --type leak /custom/path/bugs
```

## Output Structure

After running the script, each bug gets its own directory:

```
workspace/
├── leak_1_swoole/
│   ├── src/                    # Extracted source code
│   ├── bug_info.txt           # Bug metadata
│   ├── build.log              # Build output (if --build used)
│   └── configure.log          # Configuration output (if --build used)
├── npe_1_openssl_1/
│   ├── src/
│   └── bug_info.txt
└── ...
```

### Bug Information File

Each bug includes a `bug_info.txt` with:

```
Bug ID: npe_1_openssl_1
Project: openssl-1
Type: npe
File: crypto/x509/x509_vpm.c
Lines: 91 -> 92
Config: CC=gcc ./config
Build: make
Status: Downloaded
```

## Project Details

### Supported Projects

| Project | Error Types | Bug Count | Archive Size |
|---------|-------------|-----------|--------------|
| swoole | leak | 3 | ~15MB |
| p11-kit | leak, df, uaf | 4 | ~25MB |
| x264 | leak | 6 | ~30MB |
| snort | leak | 8 | ~45MB |
| openssl-1 | leak, npe | 9 | ~150MB |
| openssl-3 | npe | 3 | ~200MB |
| linux-kernel-5* | leak, npe | 3 | Manual setup |
| grub | df, uaf | 9 | ~80MB |
| lxc | uaf | 2 | ~20MB |

*Linux kernel requires manual git clone (large repository)

### Build Requirements

To use `--build` option, you need:

- **Build tools**: gcc, clang, make, cmake
- **Autotools**: autoconf, automake, libtool
- **Other**: perl, pkg-config

**Installation examples:**

```bash
# Ubuntu/Debian
sudo apt-get install build-essential cmake autoconf automake libtool perl pkg-config

# macOS
xcode-select --install
brew install cmake autoconf automake libtool

# RHEL/CentOS/Fedora
sudo yum groupinstall "Development Tools"
sudo yum install cmake autoconf automake libtool perl
```

## Integration with APR Tools

### Directory Structure for APR Tools

Each bug directory contains:
- `src/` - Source code ready for compilation
- `bug_info.txt` - Metadata including exact file and line numbers
- Standard build system (Makefile, configure scripts, etc.)

### Example APR Tool Usage

```bash
# Navigate to a bug
cd workspace/npe_1_openssl_1/src

# Use with your APR tool (example)
your_apr_tool \
    --source-dir . \
    --bug-file crypto/x509/x509_vpm.c \
    --bug-line 91 \
    --config-cmd "CC=gcc ./config" \
    --build-cmd "make"
```

### Reading Bug Metadata

```bash
# Get bug details
cat workspace/npe_1_openssl_1/bug_info.txt

# Find all NPE bugs
find workspace -name "bug_info.txt" -exec grep -l "Type: npe" {} \;

# List all bugs by type
grep -h "Bug ID\|Type:" workspace/*/bug_info.txt | paste - -
```

## Troubleshooting

### Download Issues

- **No wget/curl**: Install wget or curl
- **SSL errors**: Try `wget --no-check-certificate` or update certificates
- **Timeouts**: Check network connection, try again

### Build Issues

- **Missing dependencies**: Install build tools (see Build Requirements)
- **Configuration fails**: Check `configure.log` in bug directory
- **Build errors**: Check `build.log`, some warnings/errors are normal

### Linux Kernel Setup

Linux kernel bugs require manual setup due to repository size:

```bash
cd workspace/npe_9_linux_kernel_5
# Follow instructions in README.txt
git clone --depth 1 https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git src
cd src
git checkout 5b78ed24e8ec48602c1d6f5a188e58d000c81e2b
make defconfig
make
```

## File Locations

The bugs are located at specific file and line numbers:

### Memory Leaks (24 bugs)
- **swoole**: src/core/base.c:142-144, src/network/client.c:89-91, src/protocol/http.c:156-158
- **p11-kit**: p11-kit/server.c:567-569  
- **x264**: common/set.c:89-91, encoder/analyse.c:234-236, encoder/cabac.c:156-158, encoder/macroblock.c:345-347, common/cpu.c:123-125, filters/video/resize.c:78-80
- **snort**: Multiple files in src/ directory
- **openssl-1**: crypto/asn1/tasn_dec.c:234-236, crypto/bn/bn_lib.c:156-158, ssl/s3_srvr.c:345-347, crypto/evp/evp_pbe.c:123-125
- **linux-kernel-5**: fs/ext4/inode.c:234-236, mm/slab.c:156-158

### Null Pointer Dereference (9 bugs)
- **openssl-1**: crypto/x509/x509_vpm.c:91-92, crypto/dh/dh_check.c:128-132, crypto/ocsp/ocsp_ht.c:160-161, crypto/mem.c:329-331, ssl/d1_both.c:1181-1183
- **openssl-3**: apps/lib/s_cb.c:957-959, apps/s_server.c:3575-3578, test/params_test.c:100-102
- **linux-kernel-5**: tools/lib/subcmd/help.c:18-20

### Double Free (4 bugs)
- **p11-kit**: p11-kit/modules.c:234-236, common/array.c:78-80
- **grub**: grub-core/normal/menu.c:234-236, grub-core/fs/ext2.c:156-158

### Use After Free (10 bugs)
- **p11-kit**: trust/parser.c:445-447
- **grub**: grub-core/kern/mm.c:345-347, grub-core/normal/cmdline.c:123-125, grub-core/script/execute.c:78-80, grub-core/commands/ls.c:234-236, grub-core/net/bootp.c:156-158, grub-core/lib/arg.c:345-347, grub-core/video/video.c:123-125
- **lxc**: src/lxc/lxc_user_nic.c:234-236, src/lxc/confile.c:156-158

## Performance Notes

- **Download only**: ~2GB, takes 5-15 minutes
- **Download + build**: ~50GB, takes 1-4 hours depending on system
- **Filtered downloads**: Significantly faster, e.g., NPE-only is ~350MB

## Related Files

- `setup_effix_benchmark.sh` - Main setup script
- `README.md` - This documentation
- Original benchmark: https://github.com/nus-apr/efffix-benchmark

## Citation

If you use this benchmark in research, please cite the original EffFix paper:

```bibtex
@inproceedings{efffix2023,
  title={EffFix: An Effective and Efficient Program Repair Framework},
  author={...},
  booktitle={Proceedings of ...},
  year={2023}
}
```