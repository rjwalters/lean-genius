#!/bin/bash
#
# profile-build.sh - Measure per-stage wall-clock time for `pnpm build`.
#
# Purpose:
#   The deploy pipeline (scripts/deploy/sync-and-deploy.sh) caps `pnpm build`
#   at BUILD_TIMEOUT (default 20m). This script measures where the time is
#   actually going across the five stages of the build chain so the cap can be
#   re-evaluated mechanically rather than reactively.
#
# Usage:
#   ./scripts/deploy/profile-build.sh
#   ./scripts/deploy/profile-build.sh --json   # machine-readable output
#
# Output:
#   Per-stage wall-clock seconds + total. JSON form is suitable for trend
#   tracking (e.g., commit to research/quality-history or paste into the
#   issue tracker).
#
# Reference profile (HEAD a4f83c7b055, 2026-05-27, M-series macOS):
#   annotations:build  3.21s
#   research:build     1.08s
#   research:enrich    2.80s
#   tsc -b             8.55s
#   vite build        17.64s
#   total             ~35s   (vs 1200s cap = ~34x headroom)
#
# Re-run before bumping BUILD_TIMEOUT or splitting the build into staged caps.

set -euo pipefail

JSON_OUTPUT=false
if [[ "${1:-}" == "--json" ]]; then
    JSON_OUTPUT=true
fi

# Find repo root (same logic as sync-and-deploy.sh)
find_repo_root() {
    local dir="$PWD"
    while [[ "$dir" != "/" ]]; do
        if [[ -d "$dir/.git" ]] || [[ -f "$dir/.git" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    return 1
}

REPO_ROOT="$(find_repo_root)"
cd "$REPO_ROOT"

export NODE_OPTIONS="${NODE_OPTIONS:-} --max-old-space-size=8192"

# Capture wall-clock seconds for a command using bash's $SECONDS counter,
# which is portable across macOS (BSD) and Linux (GNU) shells.
time_stage() {
    local label="$1"
    shift
    local start=$SECONDS
    if "$@" > /tmp/profile-build-stage.log 2>&1; then
        local elapsed=$((SECONDS - start))
        if ! $JSON_OUTPUT; then
            printf "  %-22s %5ds  OK\n" "$label" "$elapsed" >&2
        fi
        echo "$elapsed"
    else
        local rc=$?
        local elapsed=$((SECONDS - start))
        if ! $JSON_OUTPUT; then
            printf "  %-22s %5ds  FAIL (exit %d)\n" "$label" "$elapsed" "$rc" >&2
            echo "    --- last 20 lines of stage log ---" >&2
            tail -20 /tmp/profile-build-stage.log | sed 's/^/    /' >&2
        fi
        echo "$elapsed"
        return "$rc"
    fi
}

if ! $JSON_OUTPUT; then
    echo "Profiling pnpm build (per-stage wall-clock seconds)..."
    echo "  Repo:       $REPO_ROOT"
    echo "  HEAD:       $(git rev-parse --short HEAD) $(git log -1 --format='%s' | cut -c1-60)"
    echo "  NODE_OPTIONS=$NODE_OPTIONS"
    echo
fi

total_start=$SECONDS

annotations_s=$(time_stage "annotations:build" pnpm annotations:build)
research_build_s=$(time_stage "research:build" pnpm research:build)
research_enrich_s=$(time_stage "research:enrich" pnpm research:enrich)
tsc_s=$(time_stage "tsc -b" npx tsc -b)
vite_s=$(time_stage "vite build" npx vite build)

total_s=$((SECONDS - total_start))

if $JSON_OUTPUT; then
    cat <<EOF
{
  "head": "$(git rev-parse HEAD)",
  "head_short": "$(git rev-parse --short HEAD)",
  "node_options": "$NODE_OPTIONS",
  "stages": {
    "annotations:build": $annotations_s,
    "research:build": $research_build_s,
    "research:enrich": $research_enrich_s,
    "tsc -b": $tsc_s,
    "vite build": $vite_s
  },
  "total_seconds": $total_s,
  "build_timeout_default_seconds": 1200,
  "headroom_ratio": $(awk "BEGIN { printf \"%.1f\", 1200 / ($total_s > 0 ? $total_s : 1) }")
}
EOF
else
    echo
    printf "  %-22s %5ds  TOTAL\n" "" "$total_s"
    echo
    # Compute headroom ratio vs default 20m cap (1200s).
    headroom=$(awk "BEGIN { printf \"%.1fx\", 1200 / ($total_s > 0 ? $total_s : 1) }")
    echo "  Default BUILD_TIMEOUT = 20m (1200s). Headroom: ${headroom}."
fi
