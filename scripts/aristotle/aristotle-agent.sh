#!/bin/bash
#
# aristotle-agent.sh - Aristotle queue management agent
#
# Usage:
#   ./aristotle-agent.sh              # Run one cycle
#   ./aristotle-agent.sh --loop       # Run continuously
#   ./aristotle-agent.sh --interval N # Loop interval in minutes (default: 30)
#   ./aristotle-agent.sh --target N   # Target active jobs (default: 20)
#   ./aristotle-agent.sh --status     # Show current status
#
# This agent:
#   1. Checks status of submitted jobs
#   2. Retrieves and integrates completed solutions
#   3. Submits new files to maintain target active count
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"

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
TARGET_ACTIVE="${ARISTOTLE_TARGET:-20}"
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
            echo "  --target N    Target active jobs (default: 20)"
            echo "  --status      Show current status and exit"
            exit 0
            ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

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

    echo "Total jobs: $total"
    echo ""
    echo "  Submitted (active): $submitted"
    echo "  Completed (pending integration): $completed"
    echo "  Integrated: $integrated"
    echo "  Failed: $failed"
    echo ""
    echo "Target active: $TARGET_ACTIVE"

    local candidates=$("$SCRIPT_DIR/find-candidates.sh" --count 2>/dev/null || echo "?")
    echo "Candidates remaining: $candidates"
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
    echo -e "${CYAN}[1/3] Checking job status...${NC}"
    "$SCRIPT_DIR/check-jobs.sh" --update 2>/dev/null || true
    echo ""

    # Step 2: Retrieve and integrate completed
    echo -e "${CYAN}[2/3] Retrieving completed solutions...${NC}"
    "$SCRIPT_DIR/retrieve-integrate.sh" 2>/dev/null || true
    echo ""

    # Step 3: Submit new files to maintain target
    echo -e "${CYAN}[3/3] Submitting new files...${NC}"
    "$SCRIPT_DIR/submit-batch.sh" --target "$TARGET_ACTIVE" 2>/dev/null || true
    echo ""

    # Summary
    local cycle_end=$(date +%s)
    local duration=$((cycle_end - cycle_start))

    echo -e "${GREEN}Cycle complete in ${duration}s${NC}"
    show_status
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
        echo -e "${CYAN}Starting Aristotle Agent in loop mode${NC}"
        echo "Interval: ${INTERVAL_MINUTES} minutes"
        echo "Target: ${TARGET_ACTIVE} active jobs"
        echo ""
        echo "Press Ctrl+C to stop"

        while true; do
            run_cycle

            echo ""
            echo -e "${YELLOW}Sleeping for ${INTERVAL_MINUTES} minutes...${NC}"
            echo "(Next cycle at $(date -v+${INTERVAL_MINUTES}M '+%H:%M:%S' 2>/dev/null || date -d "+${INTERVAL_MINUTES} minutes" '+%H:%M:%S'))"

            sleep $((INTERVAL_MINUTES * 60))
        done
    else
        run_cycle
    fi
}

main
