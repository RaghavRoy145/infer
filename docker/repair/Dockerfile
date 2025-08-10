# =========================
# Stage 1: Base Builder with all dependencies
# =========================
FROM --platform=linux/amd64 debian:bullseye-slim AS base_builder

ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      autoconf automake bubblewrap bzip2 ca-certificates curl \
      g++ gcc git libc6-dev libgmp-dev libmpfr-dev libsqlite3-dev sqlite3 \
      make opam default-jdk patch patchelf pkg-config python3 python3-distutils \
      rsync unzip wget xz-utils zlib1g-dev \
      clang-11 llvm-11 llvm-11-dev libclang-11-dev ninja-build && \
    rm -rf /var/lib/apt/lists/*

# Install a modern version of CMake
ARG CMAKE_VERSION=3.27.7
RUN wget https://github.com/Kitware/CMake/releases/download/v${CMAKE_VERSION}/cmake-${CMAKE_VERSION}-linux-x86_64.sh && \
    chmod +x cmake-${CMAKE_VERSION}-linux-x86_64.sh && \
    ./cmake-${CMAKE_VERSION}-linux-x86_64.sh --skip-license --prefix=/usr/local && \
    rm cmake-${CMAKE_VERSION}-linux-x86_64.sh

# OCaml switch for Infer
RUN opam init --disable-sandboxing --auto-setup --yes --compiler=4.14.1

# Get Infer source code
WORKDIR /
RUN git clone -b repair --depth 1 https://github.com/RaghavRoy145/infer.git
WORKDIR /infer

# Install OCaml dependencies
RUN eval $(opam env) && opam update
RUN eval $(opam env) && opam install -y dune menhir base cmdliner fmt atd atdgen yojson base64 xmlm core ctypes sqlite3 zarith
RUN eval $(opam env) && opam install -y \
    ppx_blob ppx_compare ppx_deriving ppx_enumerate ppx_expect \
    ppx_fields_conv ppx_sexp_conv ppx_yojson_conv
RUN eval $(opam env) && opam install -y \
    ANSITerminal bheap containers containers-data fpath iter \
    memtrace mtime ounit parmap re sedlex spawn tdigest
RUN eval $(opam env) && opam install -y javalib sawja ocamlgraph

# Optional pins (only if present)
RUN eval $(opam env) && \
    if [ -d "dependencies/ppx_show" ]; then opam pin add -y ppx_show ./dependencies/ppx_show; fi && \
    if [ -d "dependencies/pyml" ]; then opam pin add -y pyml ./dependencies/pyml; fi

# =========================
# Stage 2: Build the Clang Plugins (The slow part)
# =========================
FROM base_builder AS clang_builder
WORKDIR /infer

# Download clang sources for the plugins
RUN ./facebook-clang-plugins/clang/src/prepare_clang_src.sh

# Configure and build the plugins. This layer will be cached after the first successful run.
RUN BUILD_ARGS="-j1" ./facebook-clang-plugins/clang/setup.sh


# =========================
# Stage 3: Build Infer itself
# =========================
FROM base_builder AS final_builder
WORKDIR /infer

# Copy the pre-built clang plugins from the previous stage
COPY --from=clang_builder /infer/facebook-clang-plugins/clang/install /infer/facebook-clang-plugins/clang/install

# Generate configure script
RUN eval $(opam env) && ./autogen.sh

# Configure Infer
RUN eval $(opam env) && \
    export CLANG_PREFIX="$(llvm-config-11 --prefix)" && \
    ./configure --with-fcp-clang=yes

# Build Infer (this is where your next error will likely be)
RUN eval $(opam env) && env -u MAKEFLAGS make -j1 BUILD_MODE=opt

# Install Infer
RUN eval $(opam env) && make install PREFIX=/usr/local


# =========================
# Stage 4: Final Runtime Image
# =========================
FROM --platform=linux/amd64 debian:bullseye-slim

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      clang-11 gcc libc6-dev libgmp10 libmpfr6 libsqlite3-0 zlib1g \
      default-jre-headless python3 python3-distutils && \
    rm -rf /var/lib/apt/lists/*

# Copy the final installed binaries from the final_builder stage
COPY --from=final_builder /usr/local /usr/local

ENV PATH="/usr/local/bin:${PATH}"
ENV INFER_STRICT_MODE=0
ENV INFER_DEBUG=1

WORKDIR /workspace

# Tiny C file for a quick sanity check
RUN echo '#include <stdio.h>' > test_null.c && \
    echo '#include <stdlib.h>' >> test_null.c && \
    echo 'void test_null_deref(){int *p=NULL; *p=42;}' >> test_null.c && \
    echo 'int main(){ test_null_deref(); return 0; }' >> test_null.c

# Simple test helper
RUN echo '#!/bin/bash' > /usr/local/bin/test_repair.sh && \
    echo 'set -e' >> /usr/local/bin/test_repair.sh && \
    echo 'echo "=== Running Infer analysis ==="' >> /usr/local/bin/test_repair.sh && \
    echo 'infer run --pulse-only --debug-level 2 -- clang-11 -c /workspace/test_null.c' >> /usr/local/bin/test_repair.sh && \
    echo 'echo "=== Report ==="' >> /usr/local/bin/test_repair.sh && \
    echo 'infer report' >> /usr/local/bin/test_repair.sh && \
    chmod +x /usr/local/bin/test_repair.sh

CMD ["/bin/bash"]