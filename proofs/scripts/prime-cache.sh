#!/usr/bin/env bash
#
# prime-cache.sh - One-time host setup: build the Lean Docker image and
# download the Mathlib olean cache into the shared Docker volumes.
#
# WHY THIS EXISTS (issue #43620)
# -------------------------------
# On a freshly cloned host, the FIRST docker-build.sh invocation has to
# (1) build the lean4-arm64 image (installs elan + the Lean 4.31.0 toolchain,
# network-heavy) and (2) run `lake exe cache get` (downloads several GB of
# prebuilt Mathlib oleans). Both are one-time, multi-minute steps. An
# autonomous/headless agent session that starts this work, treats it as
# backgroundable, and ends its turn loses the download when the parent
# process exits -- the session reports "no work done" even though it
# "started" the build (see #38065, #38684, #39061). This script does the
# one-time priming explicitly, in the foreground, so an operator (not an
# unattended agent) absorbs the wait once per host.
#
# Idempotent / resumable: safe to re-run. `docker build` reuses already-built
# layers; `lake exe cache get` skips files it already has. Interrupting this
# script (Ctrl-C, host reboot) and re-running it picks up from wherever the
# image build / cache download left off.
#
# Usage:
#   ./proofs/scripts/prime-cache.sh
#
# Env vars:
#   LEAN_BUILD_TIMEOUT   - Docker image build timeout (default: 30m)
#   LEAN_CACHE_TIMEOUT   - `lake exe cache get` timeout (default: 45m)
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOFS_DIR="$(dirname "$SCRIPT_DIR")"
REPO_ROOT="$(dirname "$PROOFS_DIR")"

# Must match docker-build.sh
IMAGE="lean4-arm64:v4.31.0"
CACHE_VOLUME="lean-mathlib-cache"
PACKAGES_VOLUME="lean-mathlib-packages"

BUILD_TIMEOUT="${LEAN_BUILD_TIMEOUT:-30m}"
CACHE_TIMEOUT="${LEAN_CACHE_TIMEOUT:-45m}"

to_secs() { echo "$1" | sed 's/m/*60/;s/h/*3600/;s/s//' | bc; }

echo "=== Lean Genius: one-time host cache prime ==="
echo ""

if ! command -v docker &>/dev/null; then
    echo "ERROR: Docker is not installed" >&2
    exit 1
fi
if ! docker info &>/dev/null; then
    echo "ERROR: Docker daemon is not running. Please start Docker Desktop." >&2
    exit 1
fi

# --- Step 1/3: build the Lean image (installs elan + toolchain) ---
STEP_START=$(date +%s)
if docker image inspect "$IMAGE" &>/dev/null; then
    echo "[1/3] Docker image ${IMAGE} already present - skipping build."
else
    echo "[1/3] Building Docker image ${IMAGE} (installs elan + Lean toolchain, first time only)..."
    docker build -t "$IMAGE" "$PROOFS_DIR" &
    BUILD_PID=$!
    ELAPSED=0
    TIMEOUT_SECS=$(to_secs "$BUILD_TIMEOUT")
    while kill -0 "$BUILD_PID" 2>/dev/null; do
        sleep 5
        ELAPSED=$((ELAPSED + 5))
        if [ $((ELAPSED % 30)) -eq 0 ]; then
            echo "    [${ELAPSED}s] still building image..."
        fi
        if [ "$ELAPSED" -gt "$TIMEOUT_SECS" ]; then
            echo "ERROR: image build exceeded ${BUILD_TIMEOUT} - killing." >&2
            kill "$BUILD_PID" 2>/dev/null || true
            exit 124
        fi
    done
    set +e
    wait "$BUILD_PID"
    BUILD_EXIT=$?
    set -e
    if [ "$BUILD_EXIT" -ne 0 ]; then
        echo "ERROR: docker build failed (exit ${BUILD_EXIT}). Re-run this script to resume - already-built layers are reused." >&2
        exit "$BUILD_EXIT"
    fi
fi
echo "    done ($(( $(date +%s) - STEP_START ))s elapsed)"
echo ""

# --- Step 2/3: create the persistent volumes ---
echo "[2/3] Ensuring persistent Mathlib volumes exist..."
docker volume inspect "$CACHE_VOLUME" &>/dev/null || docker volume create "$CACHE_VOLUME" >/dev/null
docker volume inspect "$PACKAGES_VOLUME" &>/dev/null || docker volume create "$PACKAGES_VOLUME" >/dev/null
echo "    ${CACHE_VOLUME}, ${PACKAGES_VOLUME} ready."
echo ""

# --- Step 3/3: download the Mathlib olean cache into the volumes ---
STEP_START=$(date +%s)
echo "[3/3] Downloading Mathlib cache (lake exe cache get, several GB, first time only)..."
CONTAINER_NAME="lean-cache-prime-$$"
docker run --rm \
    -v "${REPO_ROOT}:/workspace:delegated" \
    -v "${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated" \
    -v "${PACKAGES_VOLUME}:/workspace/proofs/.lake/packages:delegated" \
    -w /workspace/proofs \
    --name "$CONTAINER_NAME" \
    "$IMAGE" \
    /bin/bash -c "lake exe cache get" &
CACHE_PID=$!
ELAPSED=0
TIMEOUT_SECS=$(to_secs "$CACHE_TIMEOUT")
while kill -0 "$CACHE_PID" 2>/dev/null; do
    sleep 5
    ELAPSED=$((ELAPSED + 5))
    if [ $((ELAPSED % 30)) -eq 0 ]; then
        echo "    [${ELAPSED}s] still downloading cache..."
    fi
    if [ "$ELAPSED" -gt "$TIMEOUT_SECS" ]; then
        echo "ERROR: cache download exceeded ${CACHE_TIMEOUT} - stopping container." >&2
        docker stop "$CONTAINER_NAME" 2>/dev/null || true
        exit 124
    fi
done
set +e
wait "$CACHE_PID"
CACHE_EXIT=$?
set -e
if [ "$CACHE_EXIT" -ne 0 ]; then
    echo "ERROR: lake exe cache get failed (exit ${CACHE_EXIT}). Re-run this script to resume - already-cached files are skipped." >&2
    exit "$CACHE_EXIT"
fi
echo "    done ($(( $(date +%s) - STEP_START ))s elapsed)"
echo ""

echo "=== Host cache primed ==="
echo "This host is ready for ./proofs/scripts/docker-build.sh - normal builds"
echo "will now only fetch incremental cache updates, not the full download."
