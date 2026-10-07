#!/usr/bin/env bash
#
# Docker-based Lean build with hard memory limits
# Uses Linux cgroups inside Docker for actual memory enforcement
#
# Usage:
#   ./proofs/scripts/docker-build.sh [target]
#   ./proofs/scripts/docker-build.sh --repair-cache   # repair corrupt oleans, then exit
#
# Environment variables:
#   LEAN_MEMORY_LIMIT  - Memory limit in MB (default: 32768 = 32GB)
#   LEAN_BUILD_TIMEOUT - Build timeout (default: 60m)
#   LEAN_SKIP_CACHE    - Skip Mathlib cache download (default: false)
#   LEAN_NUM_THREADS   - Optional Lean/Lake task concurrency (e.g. 2 on memory-limited hosts)
#
# Opt-in overrides (all unset by default; defaults reproduce the behaviour above).
# Used by the remote Lean builder (research/problems/erdos-85-wip-01/lean_builder/):
#   LEAN_REPO_ROOT     - Repo checkout to mount at /workspace (default: this script's repo)
#   LEAN_CACHE_VOLUME  - Docker volume for proofs/.lake/build (default: lean-mathlib-cache);
#                        e.g. a per-branch volume so concurrent branches don't invalidate
#                        each other's project oleans while still sharing Mathlib packages
#   LEAN_CPU_LIMIT     - Docker --cpus value (default: half the host CPUs)
#   LEAN_EXTRA_MOUNTS  - Colon-separated host dirs bind-mounted READ-ONLY at the SAME
#                        absolute path inside the container, e.g. for modules that
#                        `include_str` LRAT files by absolute host path:
#                        LEAN_EXTRA_MOUNTS=/Volumes/Stripe/lean-genius/artifacts
#   LEAN_DOCKER_CMD    - Replace the build command run in /workspace/proofs
#                        (e.g. "lake env lean Proofs/Foo.lean"); TARGET is then ignored
#
# Recovering from exit-135 / SIGBUS ("unexpected end of input") corruption:
#   The shared Mathlib volumes can retain truncated oleans after an OOM-killed
#   build, poisoning every subsequent build that imports the module. Run the
#   first-line, in-place repair (Option B, `lake exe cache get!`):
#       ./proofs/scripts/docker-build.sh --repair-cache
#   which delegates to proofs/scripts/docker-repair-cache.sh. See that script
#   and proofs/scripts/DOCKER-BUILD-RUNBOOK.md for the fallback volume reset.
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOFS_DIR="$(dirname "$SCRIPT_DIR")"
REPO_ROOT="$(dirname "$PROOFS_DIR")"

# --repair-cache: delegate to the standalone repair script (first-line Option B,
# in-place `lake exe cache get!` force-refresh) and exit. Does NOT touch the
# normal build path. Any extra args (e.g. --nuke) are forwarded to the repair
# script, so `--repair-cache --nuke` runs the guarded full volume reset.
if [[ "${1:-}" == "--repair-cache" ]]; then
    shift
    exec "${SCRIPT_DIR}/docker-repair-cache.sh" "$@"
fi

# Configuration
MEMORY_LIMIT="${LEAN_MEMORY_LIMIT:-32768}"  # 32GB default
TIMEOUT="${LEAN_BUILD_TIMEOUT:-60m}"
SKIP_CACHE="${LEAN_SKIP_CACHE:-false}"
TARGET="${1:-}"
IMAGE="lean4-arm64:v4.31.0"
CACHE_VOLUME="${LEAN_CACHE_VOLUME:-lean-mathlib-cache}"
# Shared Mathlib SOURCE checkout (.lake/packages, ~6.8GB). Without this, every
# worktree's bind-mounted /workspace accumulates its own 6.8GB copy of the
# identical pinned Mathlib source on the host — dozens of worktrees × 6.8GB was
# repeatedly filling the disk to 100% and corrupting Docker's containerd store,
# taking down all builds. All worktrees branch from main and pin the same
# mathlib rev, so one shared volume is correct; on a rare mathlib bump `lake`
# detects the manifest mismatch and re-resolves into the volume (self-healing),
# exactly as the already-shared CACHE_VOLUME (.lake/build) handles rev changes.
PACKAGES_VOLUME="lean-mathlib-packages"

detect_host_cpus() {
    local host_cpus
    if command -v nproc >/dev/null 2>&1; then
        host_cpus=$(nproc 2>/dev/null || echo 2)
    else
        host_cpus=$(sysctl -n hw.ncpu 2>/dev/null || echo 2)
    fi

    if [[ ! "$host_cpus" =~ ^[0-9]+$ || "$host_cpus" -lt 1 ]]; then
        host_cpus=2
    fi

    local build_cpus=$((host_cpus / 2))
    if [[ "$build_cpus" -lt 1 ]]; then
        build_cpus=1
    fi
    echo "$build_cpus"
}

CPU_LIMIT="${LEAN_CPU_LIMIT:-$(detect_host_cpus)}"
REPO_ROOT="${LEAN_REPO_ROOT:-$REPO_ROOT}"

EXTRA_MOUNT_ARGS=()
if [[ -n "${LEAN_EXTRA_MOUNTS:-}" ]]; then
    IFS=':' read -r -a _extra_dirs <<< "$LEAN_EXTRA_MOUNTS"
    for _d in "${_extra_dirs[@]}"; do
        [[ -z "$_d" ]] && continue
        if [[ "$_d" != /* || ! -d "$_d" ]]; then
            echo "ERROR: LEAN_EXTRA_MOUNTS entry must be an existing absolute directory: $_d"
            exit 1
        fi
        EXTRA_MOUNT_ARGS+=(-v "${_d}:${_d}:ro")
    done
fi

echo "=== Docker Lean Build ==="
echo "Memory limit: ${MEMORY_LIMIT}MB (hard enforced via cgroups)"
echo "Timeout: ${TIMEOUT}"
echo "CPU limit: ${CPU_LIMIT}"
echo "Target: ${TARGET:-all}"
[[ -n "${LEAN_CACHE_VOLUME:-}" ]] && echo "Build volume: ${CACHE_VOLUME}"
[[ -n "${LEAN_EXTRA_MOUNTS:-}" ]] && echo "Extra read-only mounts: ${LEAN_EXTRA_MOUNTS}"
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

# Create persistent volume for Mathlib cache if it doesn't exist
if ! docker volume inspect "$CACHE_VOLUME" &>/dev/null 2>&1; then
    echo "Creating persistent Mathlib cache volume..."
    docker volume create "$CACHE_VOLUME"
fi

# Create persistent volume for the shared Mathlib source checkout (.lake/packages)
if ! docker volume inspect "$PACKAGES_VOLUME" &>/dev/null 2>&1; then
    echo "Creating persistent Mathlib packages volume..."
    docker volume create "$PACKAGES_VOLUME"
fi

# Build command - download cache first if not skipped
if [ "$SKIP_CACHE" = "true" ]; then
    BUILD_CMD="lake build ${TARGET}"
else
    BUILD_CMD="lake exe cache get && lake build ${TARGET}"
fi
if [[ -n "${LEAN_DOCKER_CMD:-}" ]]; then
    BUILD_CMD="$LEAN_DOCKER_CMD"
    echo "Command: ${BUILD_CMD}"
fi

echo "Starting Docker build..."
echo ""

# Run in Docker with hard memory limit and persistent cache volume
CONTAINER_NAME="lean-build-$$"
BUILD_PID=""
CLEANED_UP=false

# Forward the task limit explicitly: host environment variables otherwise do
# not enter the container, and a CPU quota alone does not limit Lake's jobs.
if [[ -n "${LEAN_NUM_THREADS:-}" ]]; then
    if [[ ! "$LEAN_NUM_THREADS" =~ ^[1-9][0-9]*$ ]]; then
        echo "ERROR: LEAN_NUM_THREADS must be a positive integer"
        exit 1
    fi
fi

cleanup() {
    local exit_code="${1:-$?}"

    if [ "$CLEANED_UP" = "true" ]; then
        exit "$exit_code"
    fi
    CLEANED_UP=true
    trap - INT TERM HUP EXIT

    docker stop --time=5 "$CONTAINER_NAME" >/dev/null 2>&1 || true
    docker rm -f "$CONTAINER_NAME" >/dev/null 2>&1 || true

    if [ -n "$BUILD_PID" ] && kill -0 "$BUILD_PID" 2>/dev/null; then
        kill "$BUILD_PID" 2>/dev/null || true
        wait "$BUILD_PID" 2>/dev/null || true
    fi

    exit "$exit_code"
}

trap 'cleanup 130' INT
trap 'cleanup 143' TERM
trap 'cleanup 129' HUP
trap 'cleanup $?' EXIT

docker run --rm \
    --env LEAN_NUM_THREADS \
    --memory="${MEMORY_LIMIT}m" \
    --memory-swap="${MEMORY_LIMIT}m" \
    --cpus="$CPU_LIMIT" \
    -v "${REPO_ROOT}:/workspace:delegated" \
    -v "${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated" \
    -v "${PACKAGES_VOLUME}:/workspace/proofs/.lake/packages:delegated" \
    ${EXTRA_MOUNT_ARGS[@]+"${EXTRA_MOUNT_ARGS[@]}"} \
    -w /workspace/proofs \
    --name "$CONTAINER_NAME" \
    "$IMAGE" \
    /bin/bash -c "$BUILD_CMD" 2>&1 &

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
