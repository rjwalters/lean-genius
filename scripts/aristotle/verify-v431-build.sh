#!/bin/bash
#
# verify-v431-build.sh - Gate an Aristotle-integrated proof on an in-container
#                        v4.31 build (exit-0), the same gate migration
#                        increments used.
#
# WHY: the Aristotle backend elaborates against its vendored Mathlib v4.28 and
# reports its OWN success signal. We do NOT trust that signal across the version
# gap (#38622). A returned proof only counts as verified once it builds against
# our v4.31 pin inside the sanctioned Docker wrapper. This script is that gate.
#
# It delegates to ./proofs/scripts/docker-build.sh (NEVER bare `lake build`,
# which can OOM the host — see CLAUDE.md). docker-build.sh targets whatever pin
# `main` currently carries (v4.31.0 post-flip #38066), so this gate is
# automatically "the current pin" with no hard-coded version here.
#
# Usage:
#   ./verify-v431-build.sh proofs/Proofs/Foo.lean   # accepts a file path
#   ./verify-v431-build.sh Proofs.Foo               # or a module target
#
# Exit codes:
#   0  build succeeded (exit-0) -> caller may mark the proof verified
#   1  build FAILED               -> caller must NOT mark verified
#   3  gate skipped (ARISTOTLE_SKIP_BUILD_GATE=1) -> caller marks "pending",
#      never "verified"
#
# Environment:
#   ARISTOTLE_SKIP_BUILD_GATE=1  Skip the heavy build and return 3 (pending).
#                                Used by the retrieve/integrate loop when a
#                                60-min build per proof is not wanted inline;
#                                the standalone gate is then run later by the
#                                Aristotle agent / daemon before the gallery
#                                entry is marked verified.
#   LEAN_MEMORY_LIMIT, LEAN_BUILD_TIMEOUT  Passed through to docker-build.sh.
#   ARISTOTLE_VERIFY_LOG         Optional path to append the build log tail to.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
DOCKER_BUILD="$PROJECT_ROOT/proofs/scripts/docker-build.sh"

if [[ -t 1 ]]; then
    RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'; CYAN='\033[0;36m'; NC='\033[0m'
else
    RED=''; GREEN=''; YELLOW=''; CYAN=''; NC=''
fi

if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <proofs/Proofs/Foo.lean | Proofs.Foo>" >&2
    exit 1
fi

arg="$1"

# Derive the Lake module target `Proofs.<Stem>` from a path or accept a target.
target=""
if [[ "$arg" == *.lean ]]; then
    stem="$(basename "$arg" .lean)"
    target="Proofs.$stem"
elif [[ "$arg" == Proofs.* ]]; then
    target="$arg"
else
    target="Proofs.$arg"
fi

# Skip escape: return "pending" without running the heavy build.
if [[ "${ARISTOTLE_SKIP_BUILD_GATE:-0}" == "1" ]]; then
    echo -e "${YELLOW}v4.31 build gate SKIPPED${NC} for $target (ARISTOTLE_SKIP_BUILD_GATE=1)" >&2
    echo -e "${YELLOW}Proof is UNVERIFIED on the v4.31 pin — run this gate before marking verified.${NC}" >&2
    exit 3
fi

if [[ ! -x "$DOCKER_BUILD" ]]; then
    echo -e "${RED}ERROR:${NC} docker-build wrapper not found/executable: $DOCKER_BUILD" >&2
    echo -e "${YELLOW}Refusing to mark verified without the sanctioned build wrapper.${NC}" >&2
    exit 1
fi

echo -e "${CYAN}v4.31 build gate:${NC} $DOCKER_BUILD $target" >&2

log_tmp="$(mktemp "${TMPDIR:-/tmp}/aristotle-v431-build-XXXXXX.log")"
rc=0
"$DOCKER_BUILD" "$target" >"$log_tmp" 2>&1 || rc=$?

if [[ -n "${ARISTOTLE_VERIFY_LOG:-}" ]]; then
    {
        echo "=== $(date -u +%FT%TZ) $target rc=$rc ==="
        tail -40 "$log_tmp"
    } >> "$ARISTOTLE_VERIFY_LOG" 2>/dev/null || true
fi

if [[ "$rc" -eq 0 ]]; then
    echo -e "${GREEN}v4.31 build PASSED${NC} for $target" >&2
    rm -f "$log_tmp"
    exit 0
fi

echo -e "${RED}v4.31 build FAILED${NC} for $target (rc=$rc)" >&2
echo -e "${YELLOW}--- build log tail ---${NC}" >&2
tail -25 "$log_tmp" >&2 || true
echo -e "${YELLOW}Do NOT mark this proof verified. Repair remaining v4.28->v4.31 drift" >&2
echo -e "${YELLOW}(research/toolchain-v4.31-rename-map.md §2/§3/§5) and re-run the gate.${NC}" >&2
rm -f "$log_tmp"
exit 1
