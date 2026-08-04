#!/usr/bin/env bash
#
# check-cache-primed.sh - Fast, read-only preflight: is this host's Mathlib
# Docker cache primed? (issue #43620)
#
# Exits 0 silently if the cache is primed. Exits 1 with a clear instruction
# if it is cold - the caller (docker-build.sh, or a builder agent deciding
# whether it's safe to start a build) must NOT try to prime the cache
# itself: that is a multi-minute, network-heavy operation that has to run in
# the foreground as a one-time host setup step
# (./proofs/scripts/prime-cache.sh), never backgrounded inside an agent turn.
#
# Usage:
#   ./proofs/scripts/check-cache-primed.sh
#
set -euo pipefail

# Must match docker-build.sh
IMAGE="lean4-arm64:v4.31.0"
CACHE_VOLUME="lean-mathlib-cache"
PACKAGES_VOLUME="lean-mathlib-packages"

cold() {
    echo "COLD CACHE: $1" >&2
    echo "" >&2
    echo "This host has not been primed for Lean/Mathlib Docker builds yet." >&2
    echo "Run the one-time setup below in the FOREGROUND (several GB / several" >&2
    echo "minutes on a fresh host) before attempting any build:" >&2
    echo "    ./proofs/scripts/prime-cache.sh" >&2
    echo "" >&2
    echo "Do NOT run this as a backgrounded step inside an agent session -" >&2
    echo "the download is silently abandoned when the session ends." >&2
    exit 1
}

command -v docker &>/dev/null || cold "Docker is not installed"
docker info &>/dev/null || cold "Docker daemon is not running"
docker image inspect "$IMAGE" &>/dev/null || cold "image ${IMAGE} has not been built"
docker volume inspect "$CACHE_VOLUME" &>/dev/null || cold "volume ${CACHE_VOLUME} does not exist"
docker volume inspect "$PACKAGES_VOLUME" &>/dev/null || cold "volume ${PACKAGES_VOLUME} does not exist"

# Cheap non-empty check: mount the packages volume read-only and count entries.
PACKAGE_COUNT="$(docker run --rm -v "${PACKAGES_VOLUME}:/data:ro" "$IMAGE" \
    /bin/bash -c 'ls -A /data 2>/dev/null | wc -l' 2>/dev/null | tr -d ' ')"
[ "${PACKAGE_COUNT:-0}" -gt 0 ] || cold "volume ${PACKAGES_VOLUME} is empty"

echo "OK: Mathlib Docker cache is primed."
