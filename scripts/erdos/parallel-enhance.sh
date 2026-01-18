#!/bin/bash
#
# parallel-enhance.sh - Launch multiple Erdős stub enhancement agents
#
# Usage:
#   ./parallel-enhance.sh                    # Launch 3 agents (default)
#   ./parallel-enhance.sh 5                  # Launch 5 agents
#   ./parallel-enhance.sh --status           # Show agent status
#   ./parallel-enhance.sh --stop             # Stop all agents
#   ./parallel-enhance.sh --logs <N>         # Tail logs for agent N
#
# Each agent runs in its own tmux session with a unique ENHANCER_ID.
# Agents work autonomously: claim stub → enhance → commit → repeat.

set -euo pipefail

# Configuration
DEFAULT_AGENTS=3
MAX_AGENTS=8
SESSION_PREFIX="erdos-enhancer"
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
ROLE_FILE="$REPO_ROOT/.loom/roles/erdos-enhancer.md"
LOGS_DIR="$REPO_ROOT/.loom/logs"
CLAIM_TTL=90  # Minutes

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

print_info() { echo -e "${BLUE}ℹ $1${NC}"; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_warning() { echo -e "${YELLOW}⚠ $1${NC}"; }
print_error() { echo -e "${RED}✗ $1${NC}" >&2; }

# Check dependencies
check_deps() {
    local missing=()

    if ! command -v tmux &> /dev/null; then
        missing+=("tmux")
    fi

    if ! command -v claude &> /dev/null; then
        missing+=("claude (Claude Code CLI)")
    fi

    if [[ ${#missing[@]} -gt 0 ]]; then
        print_error "Missing dependencies: ${missing[*]}"
        echo "Please install the missing dependencies and try again."
        exit 1
    fi
}

# Get list of running agent sessions
get_running_agents() {
    tmux list-sessions 2>/dev/null | grep "^$SESSION_PREFIX" | cut -d: -f1 || true
}

# Show status of all agents
show_status() {
    echo "=== Erdős Enhancement Agents ==="
    echo ""

    local running
    running=$(get_running_agents)

    if [[ -z "$running" ]]; then
        echo "No agents currently running."
        echo ""
        echo "Start agents with: $0 [count]"
    else
        echo "Running agents:"
        while IFS= read -r session; do
            local agent_num="${session#$SESSION_PREFIX-}"
            local log_file="$LOGS_DIR/$session.log"
            local last_activity=""

            if [[ -f "$log_file" ]]; then
                # Get last meaningful line from log
                last_activity=$(tail -20 "$log_file" 2>/dev/null | grep -v "^$" | tail -1 | head -c 80)
            fi

            echo "  $session: ${last_activity:-running}"
        done <<< "$running"
    fi

    echo ""

    # Show claim status
    echo "=== Stub Claims ==="
    "$REPO_ROOT/scripts/erdos/claim-stub.sh" status 2>/dev/null || echo "  (claim system not initialized)"
}

# Stop all agents
stop_agents() {
    local running
    running=$(get_running_agents)

    if [[ -z "$running" ]]; then
        print_info "No agents running"
        return 0
    fi

    echo "Stopping agents..."
    while IFS= read -r session; do
        tmux kill-session -t "$session" 2>/dev/null && \
            print_success "Stopped $session" || \
            print_warning "Failed to stop $session"
    done <<< "$running"

    # Cleanup stale claims
    print_info "Cleaning up claims..."
    "$REPO_ROOT/scripts/erdos/claim-stub.sh" cleanup 2>/dev/null || true
}

# Tail logs for a specific agent
tail_logs() {
    local agent_num="$1"
    local log_file="$LOGS_DIR/$SESSION_PREFIX-$agent_num.log"

    if [[ ! -f "$log_file" ]]; then
        print_error "Log file not found: $log_file"
        exit 1
    fi

    print_info "Tailing logs for agent $agent_num (Ctrl+C to stop)"
    tail -f "$log_file"
}

# Attach to agent session
attach_agent() {
    local agent_num="$1"
    local session="$SESSION_PREFIX-$agent_num"

    if ! tmux has-session -t "$session" 2>/dev/null; then
        print_error "Agent $agent_num is not running"
        exit 1
    fi

    print_info "Attaching to $session (Ctrl+B D to detach)"
    tmux attach -t "$session"
}

# Launch agents
launch_agents() {
    local count="${1:-$DEFAULT_AGENTS}"

    if [[ $count -gt $MAX_AGENTS ]]; then
        print_warning "Limiting to $MAX_AGENTS agents (requested $count)"
        count=$MAX_AGENTS
    fi

    # Check existing agents
    local running
    running=$(get_running_agents | wc -l | tr -d ' ')

    if [[ $running -gt 0 ]]; then
        print_warning "$running agent(s) already running"
        echo "Use '$0 --stop' to stop them first, or '$0 --status' to view"
        exit 1
    fi

    # Create logs directory
    mkdir -p "$LOGS_DIR"

    # Ensure claim system is initialized
    mkdir -p "$REPO_ROOT/research/stub-claims"
    if [[ ! -f "$REPO_ROOT/research/stub-claims/completed.json" ]]; then
        echo '{"completed": []}' > "$REPO_ROOT/research/stub-claims/completed.json"
    fi

    print_info "Launching $count enhancement agents..."
    echo ""

    for i in $(seq 1 "$count"); do
        local session="$SESSION_PREFIX-$i"
        local log_file="$LOGS_DIR/$session.log"
        local enhancer_id="enhancer-$i"

        # Create tmux session
        tmux new-session -d -s "$session" -c "$REPO_ROOT"

        # Set environment variables
        tmux send-keys -t "$session" "export ENHANCER_ID='$enhancer_id'" Enter
        tmux send-keys -t "$session" "export CLAIM_TTL='$CLAIM_TTL'" Enter

        # Start Claude Code with the erdos-enhancer prompt
        # Log output to file
        local prompt="You are an Erdős stub enhancer agent. Your ID is $enhancer_id.

Read your role instructions at .loom/roles/erdos-enhancer.md and begin the enhancement loop.

Start by running:
1. ./scripts/erdos/claim-stub.sh status
2. ./scripts/erdos/claim-stub.sh cleanup
3. ./scripts/erdos/claim-stub.sh claim-random

Then enhance the claimed stub following the role instructions. After completing one stub, claim and enhance the next one. Continue until no more stubs are available."

        tmux send-keys -t "$session" "claude --dangerously-skip-permissions \"$prompt\" 2>&1 | tee -a '$log_file'" Enter

        print_success "Launched $session (log: $log_file)"
    done

    echo ""
    print_success "All agents launched!"
    echo ""
    echo "Commands:"
    echo "  $0 --status        Show agent status"
    echo "  $0 --logs N        Tail logs for agent N"
    echo "  $0 --attach N      Attach to agent N session"
    echo "  $0 --stop          Stop all agents"
}

# Main command dispatch
case "${1:-}" in
    --status|-s)
        show_status
        ;;
    --stop)
        stop_agents
        ;;
    --logs|-l)
        if [[ -z "${2:-}" ]]; then
            print_error "Usage: $0 --logs <agent-number>"
            exit 1
        fi
        tail_logs "$2"
        ;;
    --attach|-a)
        if [[ -z "${2:-}" ]]; then
            print_error "Usage: $0 --attach <agent-number>"
            exit 1
        fi
        attach_agent "$2"
        ;;
    --help|-h)
        cat << EOF
Parallel Erdős Stub Enhancement

Launch multiple Claude Code agents to enhance gallery stubs concurrently.

Usage:
  $0 [count]            Launch N agents (default: 3, max: 8)
  $0 --status           Show running agents and claims
  $0 --stop             Stop all agents
  $0 --logs N           Tail logs for agent N
  $0 --attach N         Attach to agent N's tmux session
  $0 --help             Show this help

How it works:
  1. Each agent runs in a tmux session
  2. Agents claim stubs atomically (no duplicates)
  3. Each agent: claim → enhance → commit → repeat
  4. Logs saved to .loom/logs/

Examples:
  $0                    # Launch 3 agents
  $0 5                  # Launch 5 agents
  $0 --status           # Check progress
  $0 --logs 1           # Watch agent 1
  $0 --attach 2         # Interact with agent 2

Monitoring:
  # Watch all agent logs
  tail -f .loom/logs/erdos-enhancer-*.log

  # Check claim status
  ./scripts/erdos/claim-stub.sh status

  # View git log for commits
  git log --oneline -20

Requirements:
  - tmux
  - claude (Claude Code CLI)
  - Node.js (for find-stubs.ts)

Notes:
  - Agents commit directly to main branch
  - Use --stop before shutting down to release claims
  - Stale claims auto-expire after $CLAIM_TTL minutes
EOF
        ;;
    "")
        check_deps
        launch_agents "$DEFAULT_AGENTS"
        ;;
    *)
        if [[ "$1" =~ ^[0-9]+$ ]]; then
            check_deps
            launch_agents "$1"
        else
            print_error "Unknown command: $1"
            echo "Run '$0 --help' for usage"
            exit 1
        fi
        ;;
esac
