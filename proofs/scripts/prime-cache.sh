#!/usr/bin/env bash
#
# prime-cache.sh - One-time host setup: build the Lean Docker image and download
# the pinned Mathlib checkout + olean cache into the shared Docker volumes.
#
# WHY THIS EXISTS (issue #43620)
# -------------------------------
# On a freshly cloned host the FIRST docker-build.sh invocation has to
# (1) build the lean4-arm64 image (installs elan + the Lean 4.31.0 toolchain,
# ~4.5 GB) and (2) run `lake exe cache get` (downloads the pinned Mathlib
# checkout and prebuilt oleans, ~8 GB in the shared volume). Both are one-time,
# multi-GB, multi-minute steps. An autonomous/headless agent session that starts
# this work, treats it as backgroundable, and ends its turn LOSES the download
# when the process exits -- the session reports "no work done" even though it
# "started" the build (see #38065, #38684, #39061). This script does the priming
# explicitly, in the foreground, so an operator (not an unattended agent)
# absorbs the wait once per host.
#
# IDEMPOTENT / RESUMABLE: safe to re-run. `docker build` reuses already-built
# layers; `lake exe cache get` skips files it already has. Interrupting this
# script (Ctrl-C, host reboot) and re-running it picks up from wherever the image
# build / cache download left off.
#
# Usage:
#   ./proofs/scripts/prime-cache.sh              # prime this host (foreground)
#   ./proofs/scripts/prime-cache.sh --check       # preflight only: is it primed?
#   ./proofs/scripts/prime-cache.sh --dry-run     # print the plan, change nothing
#
# Env vars:
#   LEAN_IMAGE_TIMEOUT   - Docker image build timeout (default: 30m)
#   LEAN_CACHE_TIMEOUT   - `lake exe cache get` timeout (default: 60m)
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOFS_DIR="$(dirname "$SCRIPT_DIR")"
REPO_ROOT="$(dirname "$PROOFS_DIR")"

# Must match docker-build.sh
IMAGE="lean4-arm64:v4.31.0"
CACHE_VOLUME="lean-mathlib-cache"
PACKAGES_VOLUME="lean-mathlib-packages"

IMAGE_TIMEOUT="${LEAN_IMAGE_TIMEOUT:-30m}"
CACHE_TIMEOUT="${LEAN_CACHE_TIMEOUT:-60m}"
DRY_RUN=false

for arg in "$@"; do
    case "$arg" in
        --check)
            # Preflight only -- delegates to the shared checker so there is one
            # definition of "primed" for docker-build.sh and for operators.
            exec "${SCRIPT_DIR}/check-cache-primed.sh"
            ;;
        --dry-run) DRY_RUN=true ;;
        -h|--help) sed -n '2,32p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
        *) echo "prime-cache.sh: unknown argument: $arg" >&2; exit 2 ;;
    esac
done

to_secs() { echo "$1" | sed 's/m/*60/;s/h/*3600/;s/s//' | bc; }

# Run a long command with a bounded wait and periodic progress, then return its
# exit status (124 on timeout). Never backgrounds past the end of this script.
run_bounded() {
    local label="$1" timeout_spec="$2" container_name="$3"
    shift 3
    "$@" &
    local pid=$! elapsed=0 timeout_secs
    timeout_secs="$(to_secs "$timeout_spec")"
    while kill -0 "$pid" 2>/dev/null; do
        sleep 5
        elapsed=$((elapsed + 5))
        if [ $((elapsed % 30)) -eq 0 ]; then
            echo "    [${elapsed}s] still ${label}..."
        fi
        if [ "$elapsed" -gt "$timeout_secs" ]; then
            echo "ERROR: ${label} exceeded ${timeout_spec} - stopping." >&2
            [ -n "$container_name" ] && docker stop "$container_name" >/dev/null 2>&1 || true
            kill "$pid" 2>/dev/null || true
            wait "$pid" 2>/dev/null || true
            return 124
        fi
    done
    local rc=0
    set +e
    wait "$pid"
    rc=$?
    set -e
    return "$rc"
}

echo "=== Lean Genius: one-time host cache prime ==="
echo "Expect roughly 15 GB on disk when complete (image ~4.5 GB, Mathlib"
echo "checkout + oleans ~8 GB, project build cache ~2.5 GB) and tens of minutes"
echo "on a fast connection the first time. Re-runs are near-instant."
if [ "$DRY_RUN" = "true" ]; then
    echo "(--dry-run: nothing will be built or downloaded)"
fi
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
elif [ "$DRY_RUN" = "true" ]; then
    echo "[1/3] WOULD build Docker image ${IMAGE} from ${PROOFS_DIR} (~4.5 GB)."
else
    echo "[1/3] Building Docker image ${IMAGE} (installs elan + Lean toolchain, first time only)..."
    if ! run_bounded "building image" "$IMAGE_TIMEOUT" "" docker build -t "$IMAGE" "$PROOFS_DIR"; then
        echo "ERROR: docker build failed. Re-run this script to resume - already-built layers are reused." >&2
        exit 1
    fi
fi
echo "    done ($(( $(date +%s) - STEP_START ))s elapsed)"
echo ""

# --- Step 2/3: create the persistent volumes ---
echo "[2/3] Ensuring persistent Mathlib volumes exist..."
for vol in "$CACHE_VOLUME" "$PACKAGES_VOLUME"; do
    if docker volume inspect "$vol" &>/dev/null; then
        echo "    ${vol} already exists."
    elif [ "$DRY_RUN" = "true" ]; then
        echo "    WOULD create volume ${vol}."
    else
        docker volume create "$vol" >/dev/null
        echo "    created ${vol}."
    fi
done
echo ""

# --- Step 3/3: download the Mathlib checkout + olean cache into the volumes ---
STEP_START=$(date +%s)
CONTAINER_NAME="lean-cache-prime-$$"
if [ "$DRY_RUN" = "true" ]; then
    echo "[3/3] WOULD run 'lake exe cache get' in ${IMAGE} with ${REPO_ROOT} mounted"
    echo "      at /workspace and the two volumes mounted over proofs/.lake/{build,packages}."
    echo ""
    echo "=== --dry-run complete (no changes made) ==="
    exit 0
fi
echo "[3/3] Downloading Mathlib checkout + olean cache (lake exe cache get)..."
if ! run_bounded "downloading cache" "$CACHE_TIMEOUT" "$CONTAINER_NAME" \
    docker run --rm \
        -v "${REPO_ROOT}:/workspace:delegated" \
        -v "${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated" \
        -v "${PACKAGES_VOLUME}:/workspace/proofs/.lake/packages:delegated" \
        -w /workspace/proofs \
        --name "$CONTAINER_NAME" \
        "$IMAGE" \
        /bin/bash -c "lake exe cache get"; then
    echo "ERROR: lake exe cache get failed. Re-run this script to resume - already-cached files are skipped." >&2
    exit 1
fi
echo "    done ($(( $(date +%s) - STEP_START ))s elapsed)"
echo ""

echo "=== Host cache primed ==="
echo "Verify any time with:  ./proofs/scripts/check-cache-primed.sh"
echo "This host is ready for ./proofs/scripts/docker-build.sh - normal builds"
echo "now only fetch incremental cache updates, not the full download."
