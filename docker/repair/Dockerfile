FROM --platform=linux/amd64 ubuntu:22.04

LABEL maintainer "Infer team"

# mkdir the man/man1 directory due to Debian bug #863199
RUN apt-get update && \
    mkdir -p /usr/share/man/man1 && \
    apt-get install --yes --no-install-recommends \
      curl \
      libc6-dev \
      openjdk-11-jdk-headless \
      sqlite3 \
      xz-utils \
      zlib1g-dev \
      clang \
      build-essential && \
    rm -rf /var/lib/apt/lists/*

# Download the Linux x86_64 Infer release (since we can't use macOS binaries in Linux container)
RUN INFER_VERSION=v1.2.0; \
    cd /opt && \
    curl -sL \
      https://github.com/facebook/infer/releases/download/${INFER_VERSION}/infer-linux-x86_64-${INFER_VERSION}.tar.xz | \
    tar xJ && \
    rm -f /infer && \
    ln -s ${PWD}/infer-linux-x86_64-$INFER_VERSION /infer

# Install infer
ENV PATH /infer/bin:${PATH}

# Create directory for examples
WORKDIR /infer-examples

# Set environment variable to avoid socket issues
ENV INFER_STRICT_MODE=0