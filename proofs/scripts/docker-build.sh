#!/usr/bin/env bash
#
# Docker-based Lean build with hard memory limits
# Uses Linux cgroups inside Docker for actual memory enforcement
#
# Usage:
#   ./proofs/scripts/docker-build.sh [target]
#
# Environment variables:
#   LEAN_MEMORY_LIMIT  - Memory limit in MB (default: 32768 = 32GB)
#   LEAN_BUILD_TIMEOUT - Build timeout (default: 60m)
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOFS_DIR="$(dirname "$SCRIPT_DIR")"
REPO_ROOT="$(dirname "$PROOFS_DIR")"

# Configuration
MEMORY_LIMIT="${LEAN_MEMORY_LIMIT:-32768}"  # 32GB default
TIMEOUT="${LEAN_BUILD_TIMEOUT:-60m}"
TARGET="${1:-}"
IMAGE="lean4-arm64:v4.26.0"

echo "=== Docker Lean Build ==="
echo "Memory limit: ${MEMORY_LIMIT}MB (hard enforced via cgroups)"
echo "Timeout: ${TIMEOUT}"
echo "Target: ${TARGET:-all}"
echo ""

# Check Docker
if ! command -v docker &>/dev/null; then
    echo "ERROR: Docker is not installed"
    exit 1
fi

# Check if Docker daemon is running
if ! docker info &>/dev/null; then
    echo "ERROR: Docker daemon is not running"
    echo "Please start Docker Desktop"
    exit 1
fi

# Check if image exists, build if needed
if ! docker image inspect "$IMAGE" &>/dev/null; then
    echo "Building Lean Docker image (first time only)..."
    docker build -t "$IMAGE" "$PROOFS_DIR"
    echo ""
fi

echo "Starting Docker build..."
echo ""

# Run in Docker with hard memory limit
CONTAINER_NAME="lean-build-$$"

docker run --rm \
    --memory="${MEMORY_LIMIT}m" \
    --memory-swap="${MEMORY_LIMIT}m" \
    --cpus="$(( $(sysctl -n hw.ncpu) / 2 ))" \
    -v "${REPO_ROOT}:/workspace:delegated" \
    -w /workspace/proofs \
    --name "$CONTAINER_NAME" \
    "$IMAGE" \
    /bin/bash -c "lake build ${TARGET}" 2>&1 &

BUILD_PID=$!

# Monitor with timeout (Docker memory limit handles the hard cutoff)
TIMEOUT_SECS=$(echo "$TIMEOUT" | sed 's/m/*60/;s/h/*3600/;s/s//' | bc)
ELAPSED=0
while kill -0 $BUILD_PID 2>/dev/null; do
    sleep 5
    ELAPSED=$((ELAPSED + 5))
    if [ $((ELAPSED % 30)) -eq 0 ]; then
        echo "[${ELAPSED}s] Building..."
    fi
    if [ $ELAPSED -gt $TIMEOUT_SECS ]; then
        echo "Timeout exceeded, stopping container..."
        docker stop "$CONTAINER_NAME" 2>/dev/null || true
        exit 124
    fi
done

set +e
wait $BUILD_PID 2>/dev/null
EXIT_CODE=$?
set -e

if [ $EXIT_CODE -eq 0 ]; then
    echo ""
    echo "=== Build succeeded ==="
elif [ $EXIT_CODE -eq 124 ]; then
    echo ""
    echo "=== Build timed out after ${TIMEOUT} ==="
    exit 1
elif [ $EXIT_CODE -eq 137 ]; then
    echo ""
    echo "=== Build killed - exceeded ${MEMORY_LIMIT}MB memory limit ==="
    echo "The proof consumed too much memory and was terminated by Docker."
    exit 1
else
    echo ""
    echo "=== Build failed with exit code ${EXIT_CODE} ==="
    exit $EXIT_CODE
fi
