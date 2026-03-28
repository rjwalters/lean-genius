#!/bin/bash
#
# launch-agent.sh - Launch the tester agent
#
# A singleton agent that periodically tests random proof pages on the live site
# by clicking the dice button and verifying pages load without errors.
# Failures are reported as GitHub issues.
#
# This is a script-based agent (no LLM) — it runs test-random-proofs.sh in a loop.
#
# Usage:
#   ./launch-agent.sh              Launch tester (default 30min interval, 20 proofs/cycle)
#   ./launch-agent.sh --stop       Stop the tester
#   ./launch-agent.sh --status     Check tester status
#   ./launch-agent.sh --attach     Attach to tester session
#   ./launch-agent.sh --logs       Tail tester logs
#
# Environment:
#   TESTER_INTERVAL    - Interval in minutes between test cycles (default: 30)
#   TESTER_COUNT       - Number of proofs to test per cycle (default: 20)
#   TESTER_URL         - Base URL to test (default: https://leangenius.org)

set -euo pipefail

# Find repo root
find_repo_root() {
    local dir="$PWD"
    while [[ "$dir" != "/" ]]; do
        if [[ -d "$dir/.git" ]] || [[ -f "$dir/.git" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    echo "Error: Not in a git repository" >&2
    return 1
}

REPO_ROOT="$(find_repo_root)"
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
SESSION_NAME="tester-agent"
LOG_FILE="$LOGS_DIR/tester-agent.log"
INTERVAL="${TESTER_INTERVAL:-60}"
COUNT="${TESTER_COUNT:-20}"
BASE_URL="${TESTER_URL:-https://leangenius.org}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

print_error() { echo -e "${RED}✗ $1${NC}"; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_info() { echo -e "${BLUE}ℹ $1${NC}"; }
print_warning() { echo -e "${YELLOW}! $1${NC}"; }

# Log with timestamp
log() {
    local msg="$*"
    local ts
    ts=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    echo "[$ts] $msg" >> "$LOG_FILE"
    echo "[$ts] $msg"
}

# Check dependencies
check_deps() {
    local missing=()
    command -v tmux >/dev/null 2>&1 || missing+=("tmux")
    command -v npx >/dev/null 2>&1 || missing+=("npx")
    command -v gh >/dev/null 2>&1 || missing+=("gh")

    if [[ ${#missing[@]} -gt 0 ]]; then
        print_error "Missing dependencies: ${missing[*]}"
        exit 1
    fi
}

# The main test loop (runs inside tmux)
run_loop() {
    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR"

    log "Tester agent starting (interval=${INTERVAL}m, count=${COUNT}, url=${BASE_URL})"

    while true; do
        # Check for stop signals
        if [[ -f "$SIGNALS_DIR/stop-tester" ]] || [[ -f "$SIGNALS_DIR/stop-all" ]]; then
            log "Stop signal received. Exiting."
            rm -f "$SIGNALS_DIR/stop-tester"
            exit 0
        fi

        # Run test cycle
        log "Starting test cycle: ${COUNT} random proofs"
        if "$REPO_ROOT/scripts/test/test-random-proofs.sh" --count "$COUNT" --url "$BASE_URL" >> "$LOG_FILE" 2>&1; then
            log "Test cycle complete: all proofs OK"
        else
            local exit_code=$?
            if [[ $exit_code -eq 1 ]]; then
                log "Test cycle complete: some proofs failed (issues filed)"
            else
                log "Test cycle error (exit code: $exit_code)"
            fi
        fi

        # Wait for next cycle (check stop signal every 30s during sleep)
        log "Next cycle in ${INTERVAL} minutes..."
        local wait_seconds=$((INTERVAL * 60))
        local elapsed=0
        while [[ $elapsed -lt $wait_seconds ]]; do
            # Check stop signal during sleep
            if [[ -f "$SIGNALS_DIR/stop-tester" ]] || [[ -f "$SIGNALS_DIR/stop-all" ]]; then
                log "Stop signal received during sleep. Exiting."
                rm -f "$SIGNALS_DIR/stop-tester"
                exit 0
            fi
            # Check wake signal
            if [[ -f "$SIGNALS_DIR/wake-tester-agent" ]] || [[ -f "$SIGNALS_DIR/wake-all" ]]; then
                log "Wake signal received, starting next cycle early"
                rm -f "$SIGNALS_DIR/wake-tester-agent"
                rm -f "$SIGNALS_DIR/wake-all"
                break
            fi
            sleep 30
            elapsed=$((elapsed + 30))
        done
    done
}

# Launch the tester agent
launch_agent() {
    check_deps
    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR"

    # Remove any existing stop signal
    rm -f "$SIGNALS_DIR/stop-tester"

    # Kill existing session if any
    tmux kill-session -t "$SESSION_NAME" 2>/dev/null || true

    print_info "Launching tester agent..."
    print_info "Interval: $INTERVAL minutes"
    print_info "Proofs per cycle: $COUNT"
    print_info "URL: $BASE_URL"

    # Launch in tmux — run the loop function directly
    tmux new-session -d -s "$SESSION_NAME" -c "$REPO_ROOT" \
        "$REPO_ROOT/scripts/test/launch-agent.sh --run-loop"

    print_success "Launched tester agent"
    echo ""
    echo "Commands:"
    echo "  ./scripts/test/launch-agent.sh --status     Check status"
    echo "  ./scripts/test/launch-agent.sh --attach     Attach to session"
    echo "  ./scripts/test/launch-agent.sh --logs       Tail logs"
    echo "  ./scripts/test/launch-agent.sh --stop       Stop agent"
}

# Stop the tester
stop_agent() {
    print_info "Stopping tester agent..."

    # Create stop signal for graceful shutdown
    mkdir -p "$SIGNALS_DIR"
    touch "$SIGNALS_DIR/stop-tester"

    # Give it a moment to notice
    sleep 2

    # Kill the session
    if tmux kill-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Stopped tester agent"
    else
        print_info "No tester session found"
    fi

    # Clean up signal
    rm -f "$SIGNALS_DIR/stop-tester"
}

# Graceful stop (create signal file only, don't kill session)
graceful_stop() {
    mkdir -p "$SIGNALS_DIR"
    touch "$SIGNALS_DIR/stop-tester"
}

# Check status
check_status() {
    echo "=== Tester Status ==="
    echo ""

    if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Tester is running"
        echo ""
        echo "Session: $SESSION_NAME"
        echo "Log file: $LOG_FILE"
        echo "Interval: $INTERVAL minutes"
        echo "Proofs/cycle: $COUNT"
        echo "URL: $BASE_URL"

        if [[ -f "$LOG_FILE" ]]; then
            echo ""
            echo "Recent activity:"
            tail -5 "$LOG_FILE" 2>/dev/null || echo "  (no logs yet)"
        fi
    else
        print_info "Tester is not running"
    fi
}

# Attach to session
attach_session() {
    if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_error "No tester session found"
        exit 1
    fi

    tmux attach-session -t "$SESSION_NAME"
}

# Tail logs
tail_logs() {
    if [[ ! -f "$LOG_FILE" ]]; then
        print_error "No log file found: $LOG_FILE"
        exit 1
    fi

    tail -f "$LOG_FILE"
}

# Main command dispatch
case "${1:-}" in
    --run-loop)
        # Internal: called by tmux session to run the main loop
        run_loop
        ;;
    --stop|-s)
        stop_agent
        ;;
    --graceful-stop)
        graceful_stop
        ;;
    --status)
        check_status
        ;;
    --attach|-a)
        attach_session
        ;;
    --logs|-l)
        tail_logs
        ;;
    --help|-h)
        cat << EOF
Tester Agent Launcher

Launches an autonomous script-based agent that periodically tests random
proof pages on the live site by clicking the dice button and verifying
each page loads without errors. Failures are reported as GitHub issues.

No worktree needed — this is read-only testing, no git changes.

Usage:
  ./launch-agent.sh              Launch tester (default 30min interval)
  ./launch-agent.sh --stop       Stop the tester
  ./launch-agent.sh --status     Check tester status
  ./launch-agent.sh --attach     Attach to tester session
  ./launch-agent.sh --logs       Tail tester logs
  ./launch-agent.sh --help       Show this help

Environment Variables:
  TESTER_INTERVAL   Interval in minutes between test cycles (default: 30)
  TESTER_COUNT      Number of proofs to test per cycle (default: 20)
  TESTER_URL        Base URL to test (default: https://leangenius.org)

Examples:
  ./launch-agent.sh                        # Start with defaults
  TESTER_INTERVAL=15 ./launch-agent.sh     # Test every 15 minutes
  TESTER_COUNT=50 ./launch-agent.sh        # Test 50 proofs per cycle
  ./launch-agent.sh --attach               # Watch the agent work
EOF
        ;;
    "")
        launch_agent
        ;;
    *)
        print_error "Unknown option: $1"
        echo "Run '$0 --help' for usage"
        exit 1
        ;;
esac
