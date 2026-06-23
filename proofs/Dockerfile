# Native ARM64 Lean 4 + Mathlib build environment
# Provides hard memory limits via Docker cgroups
#
FROM ubuntu:22.04

# Avoid interactive prompts
ENV DEBIAN_FRONTEND=noninteractive

# Install dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    cmake \
    python3 \
    python3-pip \
    libgmp-dev \
    && rm -rf /var/lib/apt/lists/*

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none

# Add elan to PATH
ENV PATH="/root/.elan/bin:${PATH}"

# Install Lean 4.26.0
RUN elan toolchain install leanprover/lean4:v4.26.0
RUN elan default leanprover/lean4:v4.26.0

# Verify installation
RUN lean --version

WORKDIR /workspace

# Default command
CMD ["lake", "build"]
