#!/bin/bash
#
# wedge-check.sh - Detect a wedged Aristotle pipeline (local-only, no API calls)
#
# Usage:
#   ./wedge-check.sh          # Print wedge reasons (if any)
#   ./wedge-check.sh --quiet  # No output, exit code only
#
# Exit codes:
#   0 = pipeline healthy
#   1 = pipeline wedged (reasons printed to stdout, one per line)
#
# Wedge conditions (issue #43006 — the pipeline was silently stuck for 10+
# days while health checks showed the agent session as RUNNING):
#
#   1. Untracked finished server projects. submit-batch.sh's backlog guard
#      records the untracked IDLE-project count in
#      .loom/state/aristotle-wedged on every submission attempt (and removes
#      the file when the count is 0). Any count > 0 is surfaced here.
#
#   2. No terminal job transition in ARISTOTLE_WEDGE_DAYS days (default 7).
#      check-jobs.sh / retrieve-integrate.sh touch
#      .loom/state/aristotle-last-terminal whenever a job reaches a terminal
#      state (completed / integrated / failed / expired / stale). If jobs are
#      in flight but nothing has terminated within the window, the pipeline
#      is not flowing.
#
#   3. Stale in-flight job: any job still status=="submitted" whose submitted
#      timestamp is older than ARISTOTLE_WEDGE_DAYS days. Server projects
#      finish (or expire) well within that window, so a submitted job that
#      old means status polling / retrieval is broken. This condition needs
#      no marker file, so it detects wedges even before the instrumented
#      scripts have ever run.
#
# State files live under ${REPO_ROOT:-$PROJECT_ROOT}/.loom/state — the same
# resolution used by aristotle-agent.sh, so an agent running in a worktree
# (with REPO_ROOT exported by launch-agent.sh) and `launch.sh health` running
# in the main checkout read the same files.
#
# Consumers: scripts/lean/launch.sh (cmd_health), aristotle-agent.sh (--status).

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

STATE_DIR="${REPO_ROOT:-$PROJECT_ROOT}/.loom/state"
WEDGE_FILE="$STATE_DIR/aristotle-wedged"
LAST_TERMINAL_FILE="$STATE_DIR/aristotle-last-terminal"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"

WEDGE_DAYS="${ARISTOTLE_WEDGE_DAYS:-7}"

QUIET=false
[[ "${1:-}" == "--quiet" || "${1:-}" == "-q" ]] && QUIET=true

reasons=()

# --- Condition 1: untracked finished server projects -----------------------
if [[ -f "$WEDGE_FILE" ]]; then
    untracked=$(jq -r '.untracked_idle // 0' "$WEDGE_FILE" 2>/dev/null || echo 0)
    [[ "$untracked" =~ ^[0-9]+$ ]] || untracked=0
    detected_at=$(jq -r '.detected_at // "unknown"' "$WEDGE_FILE" 2>/dev/null || echo "unknown")
    if [[ "$untracked" -gt 0 ]]; then
        reasons+=("$untracked untracked finished (IDLE) server project(s) — recovery pipeline may be broken (recorded $detected_at; run ./scripts/aristotle/retrieve-integrate.sh)")
    fi
fi

# Epoch helper for ISO-8601 UTC timestamps (BSD and GNU date).
iso_to_epoch() {
    local ts="$1"
    date -u -j -f "%Y-%m-%dT%H:%M:%SZ" "$ts" +%s 2>/dev/null \
        || date -u -d "$ts" +%s 2>/dev/null \
        || echo ""
}

now_epoch=$(date -u +%s)
window_sec=$((WEDGE_DAYS * 86400))

# Count in-flight jobs once; conditions 2 and 3 only matter when work is
# supposedly flowing (submitted > 0). An empty pipeline is idle, not wedged.
submitted_count=0
if [[ -f "$JOBS_FILE" ]]; then
    submitted_count=$(jq '[.jobs[] | select(.status == "submitted")] | length' "$JOBS_FILE" 2>/dev/null || echo 0)
    [[ "$submitted_count" =~ ^[0-9]+$ ]] || submitted_count=0
fi

# --- Condition 2: no terminal transition in the window ----------------------
if [[ "$submitted_count" -gt 0 && -f "$LAST_TERMINAL_FILE" ]]; then
    last_epoch=$(stat -f '%m' "$LAST_TERMINAL_FILE" 2>/dev/null || stat -c '%Y' "$LAST_TERMINAL_FILE" 2>/dev/null || echo "")
    if [[ -n "$last_epoch" ]] && (( now_epoch - last_epoch > window_sec )); then
        days_ago=$(( (now_epoch - last_epoch) / 86400 ))
        reasons+=("no job reached a terminal state in ${days_ago}d (threshold: ${WEDGE_DAYS}d) while $submitted_count job(s) are in flight")
    fi
fi

# --- Condition 3: stale in-flight jobs --------------------------------------
if [[ "$submitted_count" -gt 0 ]]; then
    stale_count=0
    oldest_ts=""
    while IFS= read -r ts; do
        [[ -z "$ts" || "$ts" == "unknown" ]] && continue
        ep=$(iso_to_epoch "$ts")
        [[ -n "$ep" ]] || continue
        if (( now_epoch - ep > window_sec )); then
            stale_count=$((stale_count + 1))
            if [[ -z "$oldest_ts" ]]; then
                oldest_ts="$ts"
            fi
        fi
    done < <(jq -r '.jobs[] | select(.status == "submitted") | .submitted // "unknown"' "$JOBS_FILE" 2>/dev/null | sort)
    if [[ "$stale_count" -gt 0 ]]; then
        reasons+=("$stale_count job(s) stuck in status=submitted for >${WEDGE_DAYS}d (oldest: ${oldest_ts:-unknown}) — status polling/retrieval may be broken")
    fi
fi

if [[ ${#reasons[@]} -eq 0 ]]; then
    exit 0
fi

if [[ "$QUIET" != true ]]; then
    for r in "${reasons[@]}"; do
        echo "$r"
    done
fi
exit 1
