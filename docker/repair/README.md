# Infer Repair Docker Setup

This directory contains a Docker setup for running Infer v1.2.0 on Apple Silicon Macs with convenient scripts for analysis.

## Quick Start

1. **Build the Docker image** (one-time setup):
```bash
cd docker/repair
docker build -t infer-repair .
```

2. **Run Infer on a file**:
```bash
# Basic analysis
./run-infer.sh ../../examples/hello.c

# With custom options
./run-infer.sh ../../examples/hello.c --debug
```

3. **Run repair-specific analysis**:
```bash
./run-repair.sh ../../examples/c_npe/demo.c
```

## Scripts

### `run-infer.sh`
General-purpose script for running Infer on any C file.

**Usage:**
```bash
./run-infer.sh <path-to-c-file> [additional-infer-options]
```

**Examples:**
```bash
# Simple analysis
./run-infer.sh ../../examples/hello.c

# With debugging
./run-infer.sh ../../examples/hello.c --debug

# Multiple options
./run-infer.sh ../../examples/c_npe/demo.c --keep-going --debug
```

### `run-repair.sh`
Specialized script for repair functionality testing.

**Usage:**
```bash
./run-repair.sh <path-to-c-file>
```

**What it does:**
- Runs Infer with `--keep-going --debug --pulse-only` options
- Searches for "Repair" in the output
- Shows the analysis results

**Example:**
```bash
./run-repair.sh ../../examples/c_npe/demo.c
```

## Manual Docker Commands

If you prefer to run Docker commands directly:

```bash
# Interactive session
docker run -it -v $PWD/../../examples:/examples:ro infer-repair /bin/bash

# One-liner analysis
docker run --rm -v $PWD/../../examples:/examples:ro infer-repair sh -c "
  cp -r /examples/hello.c /tmp/ && 
  cd /tmp && 
  infer -- clang -c hello.c
"
```

## Notes

- The Docker image uses Ubuntu 22.04 with x86_64 emulation on Apple Silicon
- The warning about platform mismatch is expected and can be ignored
- Files are copied to `/tmp` inside the container to avoid permission issues
- The image includes Infer v1.2.0 pre-built Linux binaries

## Troubleshooting

**"File not found" error**: Make sure the path to your C file is correct relative to where you're running the script.

**"infer-repair image not found"**: Run `docker build -t infer-repair .` in this directory first.

**Performance**: x86_64 emulation on Apple Silicon is slower than native. For production use, consider building Infer from source for ARM64.