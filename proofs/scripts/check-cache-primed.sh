#!/usr/bin/env bash
#
# check-cache-primed.sh - Fast, read-only preflight: is this host's Lean/Mathlib
# Docker cache primed? (issue #43620)
#
# Exits 0 if the cache is primed, 1 with a clear instruction if it is cold. The
# caller (docker-build.sh, or an agent deciding whether it is safe to start a
# build) must NOT try to prime the cache itself: that is a multi-GB,
# network-heavy operation which has to run in the foreground as a one-time host
# setup step (./proofs/scripts/prime-cache.sh), never backgrounded inside an
# agent turn -- the download is silently abandoned when the session ends.
#
# Usage:
#   ./proofs/scripts/check-cache-primed.sh            # full check
#   ./proofs/scripts/check-cache-primed.sh --fast     # metadata only, no container
#   ./proofs/scripts/check-cache-primed.sh --quiet    # exit status only
#
# Modes:
#   (default)  Checks docker availability, the image, both volumes, AND that the
#              packages volume actually holds the Mathlib checkout. The last
#              check starts one short-lived container (~1s).
#   --fast     Metadata only (docker CLI + daemon + `docker image inspect` +
#              `docker volume inspect`). No container is started, so this adds
#              no measurable time to a build. This is what docker-build.sh uses:
#              it catches the real cold-host case (nothing exists yet) without
#              paying a container start on every single build.
#
set -euo pipefail

# Must match docker-build.sh
IMAGE="lean4-arm64:v4.31.0"
CACHE_VOLUME="lean-mathlib-cache"
PACKAGES_VOLUME="lean-mathlib-packages"

FAST=false
QUIET=false
for arg in "$@"; do
    case "$arg" in
        --fast) FAST=true ;;
        --quiet|-q) QUIET=true ;;
        -h|--help) sed -n '2,30p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
        *) echo "check-cache-primed.sh: unknown argument: $arg" >&2; exit 2 ;;
    esac
done

cold() {
    if [ "$QUIET" = "true" ]; then
        exit 1
    fi
    cat >&2 <<COLDMSG
COLD CACHE: $1

This host has not been primed for Lean/Mathlib Docker builds yet. Run the
one-time host setup below in the FOREGROUND before attempting any build:

    ./proofs/scripts/prime-cache.sh

It downloads the Lean toolchain image and the pinned Mathlib checkout plus
olean cache (~15 GB on disk; tens of minutes on a fast connection the first
time). It is idempotent and resumable, so re-running it after an interruption
picks up where it left off.

Do NOT run it as a backgrounded step inside an autonomous/headless agent
session: the download is abandoned when the session ends, which is exactly
the stall this check exists to prevent (issue #43620). See CONTRIBUTING.md
-> "One-time host cache prime".
COLDMSG
    exit 1
}

command -v docker &>/dev/null || cold "Docker is not installed"
docker info &>/dev/null || cold "Docker daemon is not running"
docker image inspect "$IMAGE" &>/dev/null || cold "image ${IMAGE} has not been built"
docker volume inspect "$CACHE_VOLUME" &>/dev/null || cold "volume ${CACHE_VOLUME} does not exist"
docker volume inspect "$PACKAGES_VOLUME" &>/dev/null || cold "volume ${PACKAGES_VOLUME} does not exist"

if [ "$FAST" = "true" ]; then
    [ "$QUIET" = "true" ] || echo "OK: Lean/Mathlib Docker image and cache volumes are present (--fast check)."
    exit 0
fi

# Cheap non-empty check: mount the packages volume read-only and count entries.
# `lake exe cache get` unpacks the pinned Mathlib checkout + oleans in here, so
# an existing-but-empty volume (created by hand, or wiped by a cache reset) is
# just as cold as a missing one.
PACKAGE_COUNT="$(docker run --rm -v "${PACKAGES_VOLUME}:/data:ro" "$IMAGE" \
    /bin/bash -c 'ls -A /data 2>/dev/null | wc -l' 2>/dev/null | tr -d ' ')"
[ "${PACKAGE_COUNT:-0}" -gt 0 ] || cold "volume ${PACKAGES_VOLUME} is empty"

[ "$QUIET" = "true" ] || echo "OK: Lean/Mathlib Docker cache is primed (${PACKAGE_COUNT} entries in ${PACKAGES_VOLUME})."
