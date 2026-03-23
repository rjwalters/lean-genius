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
            ((count++))
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

    # Persist jobs file to survive worktree recreation
    persist_jobs_file
}

# Main logic
main() {
    # Check API key
    if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
        if [[ -f "$HOME/.aristotle_key" ]]; then
            export ARISTOTLE_API_KEY=$(cat "$HOME/.aristotle_key")
        else
            echo -e "${RED}ERROR: ARISTOTLE_API_KEY not set${NC}" >&2
            exit 1
        fi
    fi

    if [[ "$SHOW_STATUS" == true ]]; then
        show_status
        exit 0
    fi

    if [[ "$LOOP_MODE" == true ]]; then
        echo -e "${CYAN}Starting Aristotle Agent in loop mode (deterministic)${NC}"
        echo "Interval: ${INTERVAL_MINUTES} minutes"
        echo "Target: ${TARGET_ACTIVE} active jobs"
        echo ""

        local cycle_num=0
        while true; do
            # Check stop signal before each cycle
            if check_stop_signal; then
                exit 0
            fi

            ((cycle_num++))
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
