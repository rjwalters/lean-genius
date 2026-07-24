#!/bin/bash
#
# aristotle-agent.sh - Aristotle queue management agent (deterministic)
#
# Usage:
#   ./aristotle-agent.sh              # Run one cycle
#   ./aristotle-agent.sh --loop       # Run continuously
#   ./aristotle-agent.sh --interval N # Loop interval in minutes (default: 30)
#   ./aristotle-agent.sh --target N   # Target active jobs (default: 10)
#   ./aristotle-agent.sh --status     # Show current status
#
# This agent runs entirely as a shell script (no Claude needed):
#   1. Checks status of submitted jobs
#   2. Retrieves and integrates completed solutions
#   3. Commits integrated proofs and creates/updates PR
#   4. Submits new files to maintain target active count
#
# Stop signals:
#   .loom/signals/stop-aristotle  - Stop this agent
#   .loom/signals/stop-all        - Stop all agents
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"
SIGNALS_DIR="$PROJECT_ROOT/.loom/signals"
BRANCH_NAME="feature/aristotle-integrations"

# Persistent state directory at repo root (survives worktree recreation)
# When running in a worktree, REPO_ROOT may be set by launch-agent.sh
REPO_ROOT="${REPO_ROOT:-$PROJECT_ROOT}"
PERSIST_DIR="$REPO_ROOT/.loom/state"
PERSIST_JOBS="$PERSIST_DIR/aristotle-jobs.json"

# Scale-to-zero markers (issue #22471).
#
# When the agent detects there is no work and the idle threshold has elapsed,
# it touches SCALED_TO_ZERO_MARKER and gracefully exits. The daemon's
# /status, /health, and dynamic spawn logic check this marker to:
#   - report SCALED_TO_ZERO instead of UNKNOWN when no tmux session exists
#   - skip respawn until candidates>0 or pending>0 reappear
#
# LAST_CYCLE_FILE records the wall-clock timestamp of the most recent
# work-bearing cycle (any cycle that found candidates>0 or pending>0).
# This drives the "1 hour since last work" idle check across agent restarts.
#
# RATE_LIMIT_FILE is the contract from issue #22469 (capacity backoff).
# The file body (first line) holds a UTC ISO-8601 timestamp written by
# submit-batch.sh::write_rate_limit_cooldown(). While now < timestamp, the
# cooldown is active and this agent treats it as an idle reason.
SCALED_TO_ZERO_MARKER="$PERSIST_DIR/aristotle-scaled-to-zero"
LAST_CYCLE_FILE="$PERSIST_DIR/aristotle-last-cycle"
RATE_LIMIT_FILE="$PERSIST_DIR/aristotle-rate-limit-until"

# Idle threshold: minutes since the last work-bearing cycle before scale-to-zero.
# 60 minutes is the conservative starting point from issue #22471.
ARISTOTLE_IDLE_THRESHOLD_MINUTES="${ARISTOTLE_IDLE_THRESHOLD_MINUTES:-60}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

# Defaults
LOOP_MODE=false
INTERVAL_MINUTES="${ARISTOTLE_INTERVAL:-30}"
TARGET_ACTIVE="${ARISTOTLE_TARGET:-10}"
SHOW_STATUS=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --loop) LOOP_MODE=true; shift ;;
        --interval) INTERVAL_MINUTES="$2"; shift 2 ;;
        --target) TARGET_ACTIVE="$2"; shift 2 ;;
        --status) SHOW_STATUS=true; shift ;;
        -h|--help)
            echo "Usage: $0 [--loop] [--interval N] [--target N] [--status]"
            echo ""
            echo "Options:"
            echo "  --loop        Run continuously"
            echo "  --interval N  Loop interval in minutes (default: 30)"
            echo "  --target N    Target active jobs (default: 10)"
            echo "  --status      Show current status and exit"
            exit 0
            ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# Check for stop signals
check_stop_signal() {
    if [[ -f "$SIGNALS_DIR/stop-aristotle" ]] || [[ -f "$SIGNALS_DIR/stop-all" ]]; then
        echo -e "${YELLOW}Stop signal received. Exiting.${NC}"
        return 0
    fi
    return 1
}

# Check for wake signal (early wakeup from sleep)
check_wake_signal() {
    if [[ -f "$SIGNALS_DIR/wake-aristotle" ]] || [[ -f "$SIGNALS_DIR/wake-all" ]]; then
        rm -f "$SIGNALS_DIR/wake-aristotle" "$SIGNALS_DIR/wake-all" 2>/dev/null || true
        echo -e "${GREEN}Wake signal received. Starting cycle early.${NC}"
        return 0
    fi
    return 1
}

# Check whether a rate-limit cooldown is currently active (issue #22469
# capacity backoff). The contract (set by submit-batch.sh, see PR #22487):
# $RATE_LIMIT_FILE's first line holds a UTC ISO-8601 timestamp
# (e.g. "2026-06-05T12:34:56Z"). While now < that timestamp, the cooldown
# is active. If the file is missing, empty, or contains an unparseable
# value, this returns 1 (not rate-limited) — fail safe so a corrupt file
# never blocks scale-to-zero.
is_rate_limited() {
    [[ -f "$RATE_LIMIT_FILE" ]] || return 1

    local until_raw
    until_raw=$(head -n1 "$RATE_LIMIT_FILE" 2>/dev/null | tr -d '[:space:]')
    [[ -n "$until_raw" ]] || return 1

    local until_epoch=""
    # macOS BSD date and GNU date have different flags; try both.
    # The `-u` flag interprets the timestamp as UTC (matches now_epoch).
    # This mirrors submit-batch.sh::check_rate_limit_cooldown().
    if date -u -j -f "%Y-%m-%dT%H:%M:%SZ" "$until_raw" +%s >/dev/null 2>&1; then
        until_epoch=$(date -u -j -f "%Y-%m-%dT%H:%M:%SZ" "$until_raw" +%s 2>/dev/null)
    elif date -u -d "$until_raw" +%s >/dev/null 2>&1; then
        until_epoch=$(date -u -d "$until_raw" +%s 2>/dev/null)
    fi

    [[ -n "$until_epoch" ]] || return 1

    local now_epoch
    now_epoch=$(date -u +%s)
    [[ "$until_epoch" -gt "$now_epoch" ]]
}

# Record that a work-bearing cycle just ran. The mtime of $LAST_CYCLE_FILE
# is the canonical "last activity" timestamp for the idle threshold check.
record_work_cycle() {
    mkdir -p "$PERSIST_DIR"
    touch "$LAST_CYCLE_FILE"
}

# Return 0 (true) if the agent should scale to zero this cycle.
#
# Conditions (all must hold):
#   1. find-candidates.sh --count returns 0 (no work to submit)
#   2. No "submitted" jobs in aristotle-jobs.json (nothing to poll)
#   3. Either:
#       a. $ARISTOTLE_IDLE_THRESHOLD_MINUTES minutes have elapsed since
#          the last work-bearing cycle, OR
#       b. A rate-limit cooldown is active (no point continuing to spin)
#
# Prints a human-readable reason to stderr on success.
should_scale_to_zero() {
    local candidates submitted
    candidates=$("$SCRIPT_DIR/find-candidates.sh" --count 2>/dev/null || echo "0")
    candidates="${candidates//[^0-9]/}"
    candidates="${candidates:-0}"

    if [[ -f "$JOBS_FILE" ]]; then
        submitted=$(jq '[.jobs[] | select(.status == "submitted")] | length' "$JOBS_FILE" 2>/dev/null || echo "0")
    else
        submitted=0
    fi

    # Rate-limit fast path: if backoff is active and there's no in-flight
    # work to poll, scale down immediately regardless of idle threshold.
    if is_rate_limited && [[ "$submitted" -eq 0 ]]; then
        echo "Scale-to-zero: rate-limit cooldown active and no pending jobs" >&2
        return 0
    fi

    # Standard idle: need candidates=0 AND submitted=0.
    if [[ "$candidates" -gt 0 ]] || [[ "$submitted" -gt 0 ]]; then
        return 1
    fi

    # Both queues empty. Has enough time passed since last real work?
    local last_epoch now_epoch elapsed_min threshold_sec
    if [[ -f "$LAST_CYCLE_FILE" ]]; then
        last_epoch=$(stat -f '%m' "$LAST_CYCLE_FILE" 2>/dev/null || stat -c '%Y' "$LAST_CYCLE_FILE" 2>/dev/null || echo "0")
    else
        # No baseline — first run with the scale-to-zero feature. Seed
        # the file so we start the idle clock from now rather than
        # immediately scaling to zero.
        record_work_cycle
        return 1
    fi

    now_epoch=$(date +%s)
    threshold_sec=$((ARISTOTLE_IDLE_THRESHOLD_MINUTES * 60))
    elapsed_min=$(( (now_epoch - last_epoch) / 60 ))

    if (( now_epoch - last_epoch >= threshold_sec )); then
        echo "Scale-to-zero: idle ${elapsed_min}m >= ${ARISTOTLE_IDLE_THRESHOLD_MINUTES}m threshold (candidates=0, submitted=0)" >&2
        return 0
    fi

    return 1
}

# Mark the agent as scaled-to-zero and gracefully exit. The daemon will
# poll for new candidates and respawn us when work appears.
scale_to_zero_exit() {
    local reason="$1"
    mkdir -p "$PERSIST_DIR"

    # Write marker with reason + timestamp so /status can surface context.
    local ts
    ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    cat > "$SCALED_TO_ZERO_MARKER" <<EOF
{
  "scaled_at": "$ts",
  "reason": "$reason",
  "idle_threshold_minutes": $ARISTOTLE_IDLE_THRESHOLD_MINUTES
}
EOF

    echo ""
    echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${YELLOW}Aristotle scaling to zero${NC}"
    echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${YELLOW}Reason: $reason${NC}"
    echo -e "${YELLOW}Marker:  $SCALED_TO_ZERO_MARKER${NC}"
    echo -e "${YELLOW}The daemon will respawn us when candidates > 0 or pending > 0.${NC}"
    echo ""

    # Persist jobs file one last time so we don't lose state across the gap.
    persist_jobs_file || true

    exit 0
}

# Show status
show_status() {
    echo -e "${CYAN}=== Aristotle Agent Status ===${NC}"
    echo ""

    if [[ ! -f "$JOBS_FILE" ]]; then
        echo "No jobs file found"
        return
    fi

    local total=$(jq '.jobs | length' "$JOBS_FILE")
    local submitted=$(jq '[.jobs[] | select(.status == "submitted")] | length' "$JOBS_FILE")
    local completed=$(jq '[.jobs[] | select(.status == "completed")] | length' "$JOBS_FILE")
    local integrated=$(jq '[.jobs[] | select(.status == "integrated")] | length' "$JOBS_FILE")
    local failed=$(jq '[.jobs[] | select(.status == "failed" or .status == "build_failed")] | length' "$JOBS_FILE")
    local expired=$(jq '[.jobs[] | select(.status == "expired")] | length' "$JOBS_FILE")

    echo "Total jobs: $total"
    echo ""
    echo "  Submitted (active): $submitted"
    echo "  Completed (pending integration): $completed"
    echo "  Integrated: $integrated"
    echo "  Failed: $failed"
    echo "  Expired: $expired"
    echo ""
    echo "Target active: $TARGET_ACTIVE"

    local candidates=$("$SCRIPT_DIR/find-candidates.sh" --count 2>/dev/null || echo "?")
    echo "Candidates remaining: $candidates"

    # Wedge detection (issue #43006): flag a stuck pipeline in the status
    # block instead of leaving it to a buried submit-batch.sh log line.
    if [[ -x "$SCRIPT_DIR/wedge-check.sh" ]]; then
        local wedge_reasons
        if wedge_reasons=$("$SCRIPT_DIR/wedge-check.sh" 2>/dev/null); then
            echo -e "Pipeline health: ${GREEN}OK${NC}"
        else
            echo -e "Pipeline health: ${RED}WEDGED${NC}"
            while IFS= read -r reason; do
                [[ -z "$reason" ]] && continue
                echo -e "  ${YELLOW}- $reason${NC}"
            done <<< "$wedge_reasons"
        fi
    fi
}

# Commit integrated proofs and create/update PR
commit_and_pr() {
    # Check if there are changes to commit
    local changed_proofs
    changed_proofs=$(git -C "$PROJECT_ROOT" diff --name-only -- proofs/Proofs/ research/aristotle-jobs.json 2>/dev/null || true)

    if [[ -z "$changed_proofs" ]]; then
        echo -e "  ${YELLOW}No new integrations to commit${NC}"
        return 0
    fi

    # Collect which problems were integrated
    local problem_list=""
    local count=0
    while IFS= read -r file; do
        [[ -z "$file" ]] && continue
        if [[ "$file" == proofs/Proofs/Erdos* ]]; then
            local name
            name=$(basename "$file" .lean | sed 's/Problem$//' | sed 's/Erdos/erdos-/')
            if [[ -n "$problem_list" ]]; then
                problem_list="$problem_list, $name"
            else
                problem_list="$name"
            fi
            ((++count))
        fi
    done <<< "$changed_proofs"

    if [[ "$count" -eq 0 ]]; then
        echo -e "  ${YELLOW}No proof files changed${NC}"
        return 0
    fi

    echo -e "  ${BLUE}Committing $count integrated proof(s): $problem_list${NC}"

    # Stage proof files and jobs tracker
    git -C "$PROJECT_ROOT" add proofs/Proofs/ research/aristotle-jobs.json 2>/dev/null || true

    # Commit
    local commit_msg="Integrate Aristotle proofs: $problem_list"
    git -C "$PROJECT_ROOT" commit -m "$commit_msg" 2>/dev/null || {
        echo -e "  ${YELLOW}Nothing to commit${NC}"
        return 0
    }

    echo -e "  ${GREEN}Committed${NC}"

    # Push to branch
    git -C "$PROJECT_ROOT" push -u origin "$BRANCH_NAME" 2>/dev/null || {
        echo -e "  ${RED}Push failed${NC}"
        return 1
    }
    echo -e "  ${GREEN}Pushed to $BRANCH_NAME${NC}"

    # Create or update PR
    local existing_pr
    existing_pr=$(gh pr list --head "$BRANCH_NAME" --state open --json number --jq '.[0].number' 2>/dev/null || true)

    if [[ -n "$existing_pr" && "$existing_pr" != "null" ]]; then
        echo -e "  ${GREEN}PR #$existing_pr already open${NC}"
    else
        local pr_url
        pr_url=$(gh pr create \
            --title "Integrate Aristotle proofs: $problem_list" \
            --body "$(cat <<EOF
## Summary
- Automated Aristotle proof integration
- Problems: $problem_list
- Proofs with reduced sorry counts integrated from Aristotle proof search

## Test plan
- [ ] Verify proof files compile
- [ ] Check sorry counts are reduced

Generated by deterministic Aristotle agent
EOF
)" \
            --label "aristotle-integration" \
            --head "$BRANCH_NAME" 2>/dev/null) || {
            echo -e "  ${RED}PR creation failed${NC}"
            return 1
        }
        echo -e "  ${GREEN}Created PR: $pr_url${NC}"
    fi

    return 0
}

# Persist jobs file to repo root state directory (survives worktree recreation)
persist_jobs_file() {
    if [[ ! -f "$JOBS_FILE" ]]; then
        return 0
    fi

    mkdir -p "$PERSIST_DIR"

    # Only persist if the file has actually changed
    if [[ -f "$PERSIST_JOBS" ]] && diff -q "$JOBS_FILE" "$PERSIST_JOBS" >/dev/null 2>&1; then
        return 0
    fi

    cp "$JOBS_FILE" "$PERSIST_JOBS"
    echo -e "  ${GREEN}Persisted jobs file to $PERSIST_JOBS${NC}"
}

# Run one cycle of the agent
run_cycle() {
    local cycle_start=$(date +%s)

    echo ""
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BLUE}Aristotle Agent Cycle - $(date)${NC}"
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""

    # Capture pre-cycle submitted count so we can detect "had work to
    # poll" even if the cycle drains all submitted jobs to completion
    # (issue #22471 idle bookkeeping).
    local _submitted_before=0
    if [[ -f "$JOBS_FILE" ]]; then
        _submitted_before=$(jq '[.jobs[] | select(.status == "submitted")] | length' "$JOBS_FILE" 2>/dev/null || echo "0")
    fi

    # Step 1: Check job status
    echo -e "${CYAN}[1/4] Checking job status...${NC}"
    if ! "$SCRIPT_DIR/check-jobs.sh" --update 2>&1; then
        echo -e "${YELLOW}WARNING: check-jobs.sh failed — continuing with stale status${NC}"
    fi
    echo ""

    # Step 2: Retrieve and integrate completed
    echo -e "${CYAN}[2/4] Retrieving completed solutions...${NC}"
    local retrieve_exit=0
    "$SCRIPT_DIR/retrieve-integrate.sh" 2>&1 || retrieve_exit=$?
    if [[ "$retrieve_exit" -ne 0 ]]; then
        echo -e "${YELLOW}WARNING: retrieve-integrate.sh exited with code $retrieve_exit — some jobs may not have been processed${NC}"
    fi
    echo ""

    # Step 3: Commit and create/update PR for integrated proofs
    echo -e "${CYAN}[3/4] Committing integrations...${NC}"
    commit_and_pr || true
    echo ""

    # Step 4: Submit new files to maintain target
    # Run from PROJECT_ROOT so relative file paths (proofs/Proofs/*.lean) resolve correctly
    echo -e "${CYAN}[4/4] Submitting new files...${NC}"
    (cd "$PROJECT_ROOT" && "$SCRIPT_DIR/submit-batch.sh" --target "$TARGET_ACTIVE" 2>/dev/null) || true
    echo ""

    # Summary
    local cycle_end=$(date +%s)
    local duration=$((cycle_end - cycle_start))

    echo -e "${GREEN}Cycle complete in ${duration}s${NC}"
    show_status

    # If this cycle had any work — pre-existing jobs to poll OR new jobs
    # submitted — update the "last work" timestamp. This drives the idle
    # threshold check in should_scale_to_zero (issue #22471). We re-read
    # the jobs file post-cycle rather than calling find-candidates.sh
    # again, because the cycle's submit-batch step already drained the
    # candidate queue into submitted jobs if any existed.
    local _submitted_after=0
    if [[ -f "$JOBS_FILE" ]]; then
        _submitted_after=$(jq '[.jobs[] | select(.status == "submitted")] | length' "$JOBS_FILE" 2>/dev/null || echo "0")
    fi
    if [[ "$_submitted_before" -gt 0 ]] || [[ "$_submitted_after" -gt 0 ]]; then
        record_work_cycle
    fi

    # Persist jobs file to survive worktree recreation
    persist_jobs_file
}

# Main logic
main() {
    if [[ "$SHOW_STATUS" == true ]]; then
        show_status
        exit 0
    fi

    # Check API key
    if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
        if [[ -f "$HOME/.aristotle_key" ]]; then
            export ARISTOTLE_API_KEY=$(cat "$HOME/.aristotle_key")
        else
            echo -e "${RED}ERROR: ARISTOTLE_API_KEY not set${NC}" >&2
            exit 1
        fi
    fi

    if [[ "$LOOP_MODE" == true ]]; then
        echo -e "${CYAN}Starting Aristotle Agent in loop mode (deterministic)${NC}"
        echo "Interval: ${INTERVAL_MINUTES} minutes"
        echo "Target: ${TARGET_ACTIVE} active jobs"
        echo "Idle threshold (scale-to-zero): ${ARISTOTLE_IDLE_THRESHOLD_MINUTES} minutes"
        echo ""

        # Fresh launch clears any stale scale-to-zero marker — the act of
        # starting the agent means the daemon (or operator) decided there
        # is work to do, so we should not immediately re-report as scaled.
        mkdir -p "$PERSIST_DIR"
        rm -f "$SCALED_TO_ZERO_MARKER" 2>/dev/null || true

        local cycle_num=0
        while true; do
            # Check stop signal before each cycle
            if check_stop_signal; then
                exit 0
            fi

            # Scale-to-zero idle check (issue #22471). Runs before each
            # cycle so we don't waste a full cycle's wall-clock budget
            # just to discover the queue is empty.
            local _scale_reason
            if _scale_reason=$(should_scale_to_zero 2>&1 >/dev/null); then
                scale_to_zero_exit "$_scale_reason"
            fi

            ((++cycle_num))
            echo -e "${CYAN}[Cycle $cycle_num]${NC}"
            run_cycle

            # Check stop signal after cycle too
            if check_stop_signal; then
                exit 0
            fi

            echo ""
            echo -e "${YELLOW}Sleeping for ${INTERVAL_MINUTES} minutes...${NC}"
            echo "(Next cycle at $(date -v+${INTERVAL_MINUTES}M '+%H:%M:%S' 2>/dev/null || date -d "+${INTERVAL_MINUTES} minutes" '+%H:%M:%S'))"

            # Sleep in small increments to check stop/wake signals
            local sleep_seconds=$((INTERVAL_MINUTES * 60))
            local slept=0
            while [[ $slept -lt $sleep_seconds ]]; do
                sleep 30
                ((slept+=30))
                if check_stop_signal; then
                    exit 0
                fi
                if check_wake_signal; then
                    break
                fi
            done
        done
    else
        run_cycle
    fi
}

main
