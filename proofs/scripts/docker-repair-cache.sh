#!/usr/bin/env bash
#
# Repair the shared Mathlib Docker volumes after olean corruption.
#
# WHY THIS EXISTS
# ---------------
# docker-build.sh mounts two PERSISTENT named volumes shared across every
# concurrent build container:
#   - lean-mathlib-cache    -> /workspace/proofs/.lake/build
#   - lean-mathlib-packages -> /workspace/proofs/.lake/packages
# When a build container is OOM-killed (hits the --memory cgroup limit) mid-write
# to an .olean/.trace file, the volume can retain a TRUNCATED (often zero-byte)
# file. Any subsequent build — even an unrelated, previously-green target — that
# imports the truncated module then fails with SIGBUS (exit 135) when Lean mmaps
# it, with the telltale "offset 0: unexpected end of input". Because the volumes
# are shared fleet-wide, one OOM'd build poisons every concurrent/future build
# until the specific corrupt file(s) are repaired or the volume is reset.
#
# RECOVERY STRATEGY
# -----------------
# Option B (default, first-line): `lake exe cache get!` — the bang variant
#   force-restores/overwrites individual corrupt/truncated oleans from the
#   upstream Mathlib cache WITHOUT deleting the volume. Each corrupt file is
#   clobbered with a good copy; non-corrupt files are left alone. This is the
#   recovery that repeatedly cleared exit-135/SIGBUS and "invalid header" errors
#   for the research fleet across 2026-07-07/08 without any `docker volume rm`.
#   Cheap, no maintenance window, degrades gracefully under concurrent load.
#
# Option A (fallback, --nuke): `docker volume rm` both volumes for a guaranteed
#   clean slate. Only appropriate when Option B does not converge (rare
#   volume-level metadata corruption, not just individual olean files). This
#   forces a full re-download for the NEXT build (minutes-to-tens-of-minutes),
#   so it MUST run in a true zero-container window — this script hard-guards it.
#
# USAGE
#   ./proofs/scripts/docker-repair-cache.sh            # Option B (force cache get!)
#   ./proofs/scripts/docker-repair-cache.sh --nuke     # Option A (delete volumes)
#   ./proofs/scripts/docker-repair-cache.sh --help
#
# SAFETY PRECONDITION for --nuke:
#   `docker ps -a --filter name=lean-build` must show ZERO containers. A build
#   container starting between the check and the `rm` could be poisoned or lose
#   its volume out from under it, so --nuke refuses to proceed if ANY
#   lean-build-* container (running or stopped) exists.
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROOFS_DIR="$(dirname "$SCRIPT_DIR")"
REPO_ROOT="$(dirname "$PROOFS_DIR")"

# Must match docker-build.sh
IMAGE="lean4-arm64:v4.26.0"
CACHE_VOLUME="lean-mathlib-cache"
PACKAGES_VOLUME="lean-mathlib-packages"

MODE="cache-get"  # default: Option B

usage() {
    # Print the header comment block (line 2 through the first non-comment
    # line), so the help text tracks header edits without a fixed line range.
    awk 'NR > 1 && !/^#/ { exit } NR > 1 { sub(/^# ?/, ""); print }' "${BASH_SOURCE[0]}"
    exit "${1:-0}"
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --nuke|--volume-rm|--reset)
            MODE="nuke"
            ;;
        -h|--help)
            usage 0
            ;;
        *)
            echo "ERROR: unknown argument: $1" >&2
            usage 1
            ;;
    esac
    shift
done

# ---------------------------------------------------------------------------
# Preflight: Docker available
# ---------------------------------------------------------------------------
if ! command -v docker &>/dev/null; then
    echo "ERROR: Docker is not installed" >&2
    exit 1
fi
if ! docker info &>/dev/null; then
    echo "ERROR: Docker daemon is not running. Please start Docker Desktop." >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# Count in-flight build containers (running or stopped) for safety gating.
# ---------------------------------------------------------------------------
build_container_count() {
    docker ps -a --filter name=lean-build --format '{{.Names}}' 2>/dev/null \
        | grep -c . || true
}

CONTAINER_COUNT="$(build_container_count)"

echo "=== Mathlib Docker Volume Repair ==="
echo "Mode:                 ${MODE}"
echo "Cache volume:         ${CACHE_VOLUME}"
echo "Packages volume:      ${PACKAGES_VOLUME}"
echo "lean-build containers: ${CONTAINER_COUNT}"
echo ""

if [[ "$MODE" == "nuke" ]]; then
    # -----------------------------------------------------------------------
    # Option A: docker volume rm (guaranteed clean slate).
    # HARD SAFETY GATE: zero lean-build-* containers must exist.
    # -----------------------------------------------------------------------
    if [[ "$CONTAINER_COUNT" -ne 0 ]]; then
        echo "REFUSING to delete shared volumes: ${CONTAINER_COUNT} lean-build container(s) present." >&2
        echo "Deleting volumes now could poison or strand an in-flight build." >&2
        echo "" >&2
        echo "Wait for a true zero-container window, verify with:" >&2
        echo "  docker ps -a --filter name=lean-build" >&2
        echo "then re-run: $0 --nuke" >&2
        exit 2
    fi

    echo "Zero build containers confirmed. Deleting shared Mathlib volumes..."
    echo "(The next docker-build.sh run will recreate both volumes and do a full"
    echo " 'lake exe cache get && lake build' from empty — a large one-time cost.)"
    echo ""
    # Volumes may legitimately not exist yet; don't fail the whole script on that.
    docker volume rm "$CACHE_VOLUME" 2>/dev/null \
        && echo "  removed ${CACHE_VOLUME}" \
        || echo "  ${CACHE_VOLUME} not present (nothing to remove)"
    docker volume rm "$PACKAGES_VOLUME" 2>/dev/null \
        && echo "  removed ${PACKAGES_VOLUME}" \
        || echo "  ${PACKAGES_VOLUME} not present (nothing to remove)"
    echo ""
    echo "=== Volumes reset. Next build will repopulate them from empty. ==="
    exit 0
fi

# ---------------------------------------------------------------------------
# Option B (default): lake exe cache get! — in-place force-refresh.
#
# Safe to run even while other agents build: each corrupt file is overwritten
# with a good copy, non-corrupt files are left alone. No volume deletion.
# ---------------------------------------------------------------------------
if [[ "$CONTAINER_COUNT" -ne 0 ]]; then
    echo "NOTE: ${CONTAINER_COUNT} lean-build container(s) are running."
    echo "      'lake exe cache get!' is safe to run concurrently (per-file overwrite),"
    echo "      so proceeding. (Use --nuke only in a zero-container window.)"
    echo ""
fi

# Ensure the image exists (mirror docker-build.sh behavior).
if ! docker image inspect "$IMAGE" &>/dev/null; then
    echo "Building Lean Docker image (first time only)..."
    docker build -t "$IMAGE" "$PROOFS_DIR"
    echo ""
fi

# Ensure volumes exist so the mount targets are valid.
docker volume inspect "$CACHE_VOLUME"    &>/dev/null || docker volume create "$CACHE_VOLUME"    >/dev/null
docker volume inspect "$PACKAGES_VOLUME" &>/dev/null || docker volume create "$PACKAGES_VOLUME" >/dev/null

CONTAINER_NAME="lean-repair-$$"

run_cache_get() {
    docker run --rm \
        -v "${REPO_ROOT}:/workspace:delegated" \
        -v "${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated" \
        -v "${PACKAGES_VOLUME}:/workspace/proofs/.lake/packages:delegated" \
        -w /workspace/proofs \
        --name "$CONTAINER_NAME" \
        "$IMAGE" \
        /bin/bash -c "lake exe cache get!"
}

# Try up to 2 attempts before recommending Option A fallback.
ATTEMPT=0
MAX_ATTEMPTS=2
while :; do
    ATTEMPT=$((ATTEMPT + 1))
    echo "Attempt ${ATTEMPT}/${MAX_ATTEMPTS}: 'lake exe cache get!' (force-overwrite corrupt oleans)..."
    if run_cache_get; then
        echo ""
        echo "=== Cache force-refresh succeeded. Re-run your build to confirm exit 0: ==="
        echo "    ./proofs/scripts/docker-build.sh Proofs.ElementaryQuadraticReciprocityOQ03OQ02"
        exit 0
    fi

    echo ""
    echo "Attempt ${ATTEMPT} did not succeed."
    if [[ "$ATTEMPT" -ge "$MAX_ATTEMPTS" ]]; then
        echo ""
        echo "=== 'lake exe cache get!' did not converge after ${MAX_ATTEMPTS} attempts. ===" >&2
        echo "This can indicate volume-level (not just per-file) corruption." >&2
        echo "Fall back to Option A (full volume reset) in a ZERO-container window:" >&2
        echo "  docker ps -a --filter name=lean-build   # must be empty" >&2
        echo "  $0 --nuke" >&2
        exit 3
    fi
    echo "Retrying..."
    echo ""
done
