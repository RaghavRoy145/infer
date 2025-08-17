# NPE Bugs Setup Script for EffFix Benchmark

## Overview

This repository contains a setup script (`setup_npe_bugs.sh`) that automates the process of downloading, extracting, and optionally building all Null Pointer Dereference (NPE) bugs from the EffFix benchmark. This script is designed for researchers and developers who want to apply their own Automated Program Repair (APR) tools to these real-world NPE bugs.

**Important Note**: This script works independently and can be run outside of this repository. It downloads all necessary files directly from GitHub.

## What Does This Script Do?

The script operates in two phases:

### Phase 1: Download (Always runs)
- Downloads pre-instrumented source code tarballs from GitHub
- Extracts complete project source code
- Creates bug information files with exact NPE locations
- Fast operation (~5 minutes, ~500MB download)

### Phase 2: Build (Optional with --build flag)
- Configures each project using its native build system
- Compiles the entire project (not just individual files)
- Validates that projects build successfully
- Slow operation (~1-2 hours, ~10GB disk space)

## NPE Bugs Included

The script sets up 9 NPE bugs from 3 major open-source projects:

| Bug ID | Project | File | NPE Lines | Description |
|--------|---------|------|-----------|-------------|
| null-ptr-1-openssl-1 | OpenSSL 1.x | crypto/x509/x509_vpm.c | 91→92 | X509 verification parameter |
| null-ptr-2-openssl-1 | OpenSSL 1.x | crypto/dh/dh_check.c | 128→132 | DH public key check |
| null-ptr-3-openssl-1 | OpenSSL 1.x | crypto/ocsp/ocsp_ht.c | 160→161 | OCSP request handling |
| null-ptr-4-openssl-1 | OpenSSL 1.x | crypto/mem.c | 329→331 | String duplication |
| null-ptr-5-openssl-1 | OpenSSL 1.x | ssl/d1_both.c | 1181→1183 | DTLS buffer message |
| null-ptr-6-openssl-3 | OpenSSL 3.x | apps/lib/s_cb.c | 957→959 | SSL certificate handling |
| null-ptr-7-openssl-3 | OpenSSL 3.x | apps/s_server.c | 3575→3578 | Session management |
| null-ptr-8-openssl-3 | OpenSSL 3.x | test/params_test.c | 100→102 | Parameter testing |
| null-ptr-9-linux-kernel-5 | Linux Kernel | tools/lib/subcmd/help.c | 18→20 | Command help system |

**Note**: The Linux kernel bug requires manual setup due to repository size (~3GB).

## Prerequisites

### For Download Only (Phase 1)
- `wget` or `curl` - for downloading source tarballs
- `tar` - for extracting archives
- ~500MB free disk space

### For Building (Phase 2)
- `make` - build automation tool
- `gcc` - C compiler
- `perl` - required by OpenSSL build system
- ~10GB free disk space
- Multi-core CPU recommended (builds use parallel compilation)

### Installing Dependencies

**Ubuntu/Debian:**
```bash
# For download only
sudo apt-get update
sudo apt-get install wget

# For building
sudo apt-get install build-essential perl
```

**CentOS/RHEL/Fedora:**
```bash
# For download only
sudo yum install wget

# For building
sudo yum groupinstall "Development Tools"
sudo yum install perl
```

**macOS (with Homebrew):**
```bash
# For download only
brew install wget

# For building (requires Xcode command line tools)
xcode-select --install
```

## Usage

### Quick Start (Download Only)

```bash
# Make the script executable
chmod +x setup_npe_bugs.sh

# Download source code only (fast, ~5 minutes)
./setup_npe_bugs.sh

# Source code will be in ./npe_bugs_workspace/
```

### Download and Build

```bash
# Download AND build all projects (slow, ~1-2 hours)
./setup_npe_bugs.sh --build

# Or specify a custom workspace directory
./setup_npe_bugs.sh --build /path/to/your/workspace
```

### Two-Step Process (Recommended)

```bash
# Step 1: Download sources first
./setup_npe_bugs.sh /my/workspace

# Step 2: Build later when ready (can be run multiple times)
./setup_npe_bugs.sh --build /my/workspace
```

### Command Line Options

```
Usage: setup_npe_bugs.sh [OPTIONS] [WORKSPACE_DIR]

OPTIONS:
    --build     Also build the projects after downloading
    --help, -h  Show help message

ARGUMENTS:
    WORKSPACE_DIR  Directory to store bugs (default: ./npe_bugs_workspace)
```

## Output Directory Structure

After successful execution, your workspace will contain:

```
npe_bugs_workspace/
├── null-ptr-1-openssl-1/
│   ├── src/                    # Complete OpenSSL source code
│   ├── bug_info.txt            # Bug location and build commands
│   ├── configure.log           # Configuration output (if built)
│   └── build.log               # Build output (if built)
├── null-ptr-2-openssl-1/
│   └── ...
├── ...
├── setup_summary.txt           # Summary of all bugs
└── openssl-1-instrumented.tar.gz  # Downloaded tarballs (reused across bugs)
```

## Using with Your APR Tool

### Important: Whole-Project Context

**EffFix and this benchmark operate on entire projects, not individual files.** Each NPE bug exists within a complete, buildable project because:

1. Memory errors often involve inter-procedural relationships across multiple files
2. Proper validation requires checking that fixes don't break other parts of the code
3. Real-world APR must handle complete codebases with build systems

### Integration Example

After setup, each bug directory contains:

1. **Complete buildable source code** in `src/` subdirectory
2. **Bug information** in `bug_info.txt`:
   - Exact file path containing the NPE
   - Source and sink line numbers
   - Build commands for recompilation

```bash
# Example: Apply your APR tool to null-ptr-1-openssl-1
cd npe_bugs_workspace/null-ptr-1-openssl-1/src

# The NPE is in crypto/x509/x509_vpm.c at lines 91-92
your_apr_tool \
  --project-root . \
  --bug-file crypto/x509/x509_vpm.c \
  --bug-lines 91-92 \
  --bug-type NPE

# After repair, rebuild the ENTIRE project to validate
make

# Run your verification
your_verification_tool .
```

### Programmatic Access

Parse bug information for automation:

```bash
# Extract bug details from bug_info.txt
BUG_DIR="npe_bugs_workspace/null-ptr-1-openssl-1"
bug_file=$(grep "Source File:" $BUG_DIR/bug_info.txt | cut -d: -f2- | xargs)
src_line=$(grep "NPE Source Line:" $BUG_DIR/bug_info.txt | cut -d: -f2 | xargs)
sink_line=$(grep "NPE Sink Line:" $BUG_DIR/bug_info.txt | cut -d: -f2 | xargs)
build_cmd=$(grep "Build Command:" $BUG_DIR/bug_info.txt | cut -d: -f2- | xargs)

# Apply your tool
cd $BUG_DIR/src
your_tool --file "$bug_file" --lines "$src_line-$sink_line"

# Rebuild project
eval "$build_cmd"
```

## Build Times and Resources

### Time Estimates
- **Download only**: ~5 minutes (depends on internet speed)
- **OpenSSL 1.x build**: ~5-10 minutes per bug (5 bugs total)
- **OpenSSL 3.x build**: ~10-20 minutes per bug (3 bugs total)
- **Total with build**: ~1-2 hours for all bugs

### Disk Space Requirements
- **Downloaded tarballs**: ~500MB
- **Extracted source**: ~2GB
- **Built projects**: ~10GB total

### Linux Kernel Bug

The Linux kernel bug (null-ptr-9) requires manual setup:

```bash
cd npe_bugs_workspace/null-ptr-9-linux-kernel-5
git clone --depth 1 https://git.kernel.org/pub/scm/linux/kernel/git/torvalds/linux.git src
cd src
git checkout 5b78ed24e8ec48602c1d6f5a188e58d000c81e2b
make CC=clang defconfig
make CC=clang -j32
```

## Troubleshooting

### Download Failures
```bash
# Check internet connection and GitHub accessibility
ping github.com

# Retry (already downloaded files are skipped)
./setup_npe_bugs.sh

# Use curl instead of wget
# The script automatically tries both
```

### Build Failures
```bash
# Check specific build log
cat npe_bugs_workspace/null-ptr-1-openssl-1/build.log

# Try building manually
cd npe_bugs_workspace/null-ptr-1-openssl-1/src
./config
make

# Some warnings are normal for older codebases
```

### Permission Issues
```bash
# Make script executable
chmod +x setup_npe_bugs.sh

# Fix workspace permissions if needed
chmod -R u+rwx npe_bugs_workspace/
```

### Incremental Usage
```bash
# The script is idempotent - safe to run multiple times
# Already downloaded files are skipped
# Failed builds can be retried

# Re-run just the build phase
./setup_npe_bugs.sh --build npe_bugs_workspace/
```

## Advanced Usage

### Download Specific Bugs Only

Edit the script and comment out unwanted bugs in the `NPE_BUGS` array:

```bash
declare -A NPE_BUGS=(
    ["null-ptr-1-openssl-1"]="..."  # Keep this
    # ["null-ptr-2-openssl-1"]="..." # Skip this
)
```

### Custom Build Flags

Modify the script to add debug symbols or optimization:

```bash
# Change in NPE_BUGS array
["null-ptr-1-openssl-1"]="...:CC=gcc ./config --debug:make CFLAGS='-g -O0'"
```

### Parallel Processing

The script processes bugs sequentially. For parallel download/build, modify the script or run multiple instances with different bug subsets.

## Why Whole-Project Analysis?

This benchmark uses complete projects because:

1. **Realistic Testing**: Real bugs exist in complete codebases with dependencies
2. **Inter-procedural Analysis**: NPEs often involve function calls across files
3. **Build System Integration**: Repairs must work with existing build systems
4. **Validation Accuracy**: Changes must not break other parts of the project

For more details on EffFix's whole-project approach, see [efffix_whole_project_explanation.md](efffix_whole_project_explanation.md).

## Support

For issues related to:
- **This script**: Create an issue in this repository
- **EffFix benchmark**: See https://github.com/nus-apr/efffix-benchmark
- **EffFix tool**: See https://github.com/nus-apr/EffFix
- **Specific projects**: Refer to the original project repositories

## Citation

If you use this benchmark in your research, please cite the EffFix paper:

```bibtex
@inproceedings{zhang2024efffix,
  title={Efficient and Effective Repair of Pointer-Manipulating Programs},
  author={Zhang, Yuntong and Shariffdeen, Ridwan and Lawall, Julia and Roychoudhury, Abhik},
  booktitle={International Conference on Software Engineering (ICSE)},
  year={2024}
}
```

## License

This script is provided as-is for research purposes. The underlying projects (OpenSSL, Linux kernel) have their own licenses that must be respected.