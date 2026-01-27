#!/bin/bash
#
# parallel-enhance.sh - Launch multiple Erdős stub enhancement agents in isolated worktrees
#
# Usage:
#   ./parallel-enhance.sh                    # Launch 3 agents (default)
#   ./parallel-enhance.sh 5                  # Launch 5 agents
#   ./parallel-enhance.sh --status           # Show agent status
#   ./parallel-enhance.sh --stop             # Stop all agents
#   ./parallel-enhance.sh --logs <N>         # Tail logs for agent N
#   ./parallel-enhance.sh --cleanup          # Remove all enhancer worktrees
#
# Each agent runs in its own git worktree with a dedicated branch.
# Agents work autonomously: claim stub → enhance → commit → push → create PR → repeat.

set -euo pipefail

# Configuration
DEFAULT_AGENTS=3
MAX_AGENTS=8
SESSION_PREFIX="erdos-enhancer"
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WORKTREES_DIR="$REPO_ROOT/.loom/worktrees"
ROLE_FILE="$REPO_ROOT/.lean/roles/erdos-enhancer.md"
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
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

    if ! command -v gh &> /dev/null; then
        missing+=("gh (GitHub CLI)")
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

# Create worktree for an agent
create_agent_worktree() {
    local agent_num="$1"
    local worktree_path="$WORKTREES_DIR/enhancer-$agent_num"
    local branch_name="feature/enhancer-$agent_num"

    # Remove existing worktree if it exists
    if [[ -d "$worktree_path" ]]; then
        print_info "Removing existing worktree for agent $agent_num..."
        git worktree remove "$worktree_path" --force 2>/dev/null || rm -rf "$worktree_path"
    fi

    # Delete existing branch if it exists (force fresh start)
    git branch -D "$branch_name" 2>/dev/null || true

    # Create fresh worktree with new branch from main
    print_info "Creating worktree for agent $agent_num..."
    git worktree add "$worktree_path" -b "$branch_name" main

    # Initialize submodules if needed
    if [[ -f "$worktree_path/.gitmodules" ]]; then
        (cd "$worktree_path" && git submodule update --init --recursive 2>/dev/null) || true
    fi

    # Symlink .lake for fast Lean builds
    if [[ -d "$REPO_ROOT/proofs/.lake" ]] && [[ -d "$worktree_path/proofs" ]]; then
        rm -rf "$worktree_path/proofs/.lake"
        ln -s "$REPO_ROOT/proofs/.lake" "$worktree_path/proofs/.lake"
    fi

    echo "$worktree_path"
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
            local worktree_path="$WORKTREES_DIR/enhancer-$agent_num"
            local branch=""

            if [[ -d "$worktree_path" ]]; then
                branch=$(cd "$worktree_path" && git branch --show-current 2>/dev/null || echo "unknown")
            fi

            echo "  $session: worktree=$worktree_path branch=$branch"
        done <<< "$running"
    fi

    echo ""

    # Show claim status
    echo "=== Stub Claims ==="
    "$REPO_ROOT/scripts/erdos/claim-stub.sh" status 2>/dev/null || echo "  (claim system not initialized)"

    echo ""

    # Show worktrees
    echo "=== Worktrees ==="
    git worktree list | grep enhancer || echo "  (no enhancer worktrees)"

    # Show stop signal status
    echo ""
    echo "=== Stop Signals ==="
    if [[ -f "$SIGNALS_DIR/stop-all" ]]; then
        print_warning "STOP-ALL signal pending - agents will stop after current work"
    else
        local has_individual=false
        for sig in "$SIGNALS_DIR"/stop-enhancer-*; do
            if [[ -f "$sig" ]]; then
                has_individual=true
                local agent_num=$(basename "$sig" | sed 's/stop-enhancer-//')
                print_warning "STOP signal pending for enhancer-$agent_num"
            fi
        done
        if [[ "$has_individual" == "false" ]]; then
            echo "  (no stop signals pending)"
        fi
    fi
}

# Signal agents to stop gracefully (finish current work first)
signal_graceful_stop() {
    local agent_num="${1:-all}"

    mkdir -p "$SIGNALS_DIR"

    if [[ "$agent_num" == "all" ]]; then
        touch "$SIGNALS_DIR/stop-all"
        print_success "Signaled all agents to stop after completing current work"
        echo ""
        echo "Agents will:"
        echo "  1. Finish current stub enhancement"
        echo "  2. Commit, push, and create PR"
        echo "  3. Exit cleanly"
        echo ""
        echo "Monitor with: $0 --status"
        echo "Force stop:   $0 --stop"
    else
        touch "$SIGNALS_DIR/stop-enhancer-$agent_num"
        print_success "Signaled enhancer-$agent_num to stop after completing current work"
    fi
}

# Clear stop signals
clear_stop_signals() {
    rm -f "$SIGNALS_DIR/stop-all" 2>/dev/null || true
    rm -f "$SIGNALS_DIR/stop-enhancer-"* 2>/dev/null || true
}

# Check if stop signal exists for an agent
has_stop_signal() {
    local agent_num="$1"
    [[ -f "$SIGNALS_DIR/stop-all" ]] || [[ -f "$SIGNALS_DIR/stop-enhancer-$agent_num" ]]
}

# Stop all agents (force)
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

    # Clear any stop signals
    clear_stop_signals

    # Cleanup stale claims
    print_info "Cleaning up claims..."
    "$REPO_ROOT/scripts/erdos/claim-stub.sh" cleanup 2>/dev/null || true
}

# Cleanup all enhancer worktrees
cleanup_worktrees() {
    echo "Cleaning up enhancer worktrees..."

    # First stop any running agents
    stop_agents

    # Remove worktrees
    for i in $(seq 1 $MAX_AGENTS); do
        local worktree_path="$WORKTREES_DIR/enhancer-$i"
        local branch_name="feature/enhancer-$i"

        if [[ -d "$worktree_path" ]]; then
            print_info "Removing worktree: $worktree_path"
            git worktree remove "$worktree_path" --force 2>/dev/null || rm -rf "$worktree_path"
        fi

        # Delete branch
        git branch -D "$branch_name" 2>/dev/null && \
            print_info "Deleted branch: $branch_name" || true
    done

    # Prune worktree references
    git worktree prune

    print_success "Cleanup complete"
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

# Send continue signal to agents (resumes after API limits)
send_continue() {
    local agent_num="${1:-all}"
    local sent=0

    if [[ "$agent_num" == "all" ]]; then
        for session in $(get_running_agents); do
            tmux send-keys -t "$session" "continue" Enter 2>/dev/null && \
                print_success "Sent continue to $session" && ((sent++)) || \
                print_warning "Could not send to $session"
        done
    else
        local session="$SESSION_PREFIX-$agent_num"
        if tmux has-session -t "$session" 2>/dev/null; then
            tmux send-keys -t "$session" "continue" Enter 2>/dev/null && \
                print_success "Sent continue to $session" && ((sent++)) || \
                print_warning "Could not send to $session"
        else
            print_error "Agent $agent_num is not running"
            exit 1
        fi
    fi

    if [[ $sent -eq 0 ]]; then
        print_warning "No agents to send continue signal to"
    else
        echo "Sent continue to $sent agent(s). They should resume work shortly."
    fi
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

    # Create directories
    mkdir -p "$LOGS_DIR"
    mkdir -p "$WORKTREES_DIR"
    mkdir -p "$SIGNALS_DIR"

    # Clear any old stop signals
    clear_stop_signals

    # Ensure claim system is initialized
    mkdir -p "$REPO_ROOT/research/stub-claims"
    if [[ ! -f "$REPO_ROOT/research/stub-claims/completed.json" ]]; then
        echo '{"completed": []}' > "$REPO_ROOT/research/stub-claims/completed.json"
    fi

    # Ensure we're on main and up to date
    print_info "Updating main branch..."
    git checkout main 2>/dev/null || true
    git pull origin main 2>/dev/null || true

    print_info "Launching $count enhancement agents with isolated worktrees..."
    echo ""

    for i in $(seq 1 "$count"); do
        local session="$SESSION_PREFIX-$i"
        local log_file="$LOGS_DIR/$session.log"
        local enhancer_id="enhancer-$i"

        # Create isolated worktree for this agent
        local worktree_path
        worktree_path=$(create_agent_worktree "$i")

        # Create tmux session starting in the worktree
        tmux new-session -d -s "$session" -c "$worktree_path"

        # Set environment variables
        tmux send-keys -t "$session" "export ENHANCER_ID='$enhancer_id'" Enter
        tmux send-keys -t "$session" "export CLAIM_TTL='$CLAIM_TTL'" Enter
        tmux send-keys -t "$session" "export REPO_ROOT='$REPO_ROOT'" Enter

        # Write prompt to file (avoids tmux multiline issues)
        local prompt_file="$LOGS_DIR/$session-prompt.md"
        cat > "$prompt_file" << PROMPT_EOF
# Erdős Stub Enhancer Agent $enhancer_id

You are working in an isolated git worktree with your own branch.

**Your worktree:** $worktree_path
**Your branch:** feature/enhancer-$i
**Claim script:** \$REPO_ROOT/scripts/erdos/claim-stub.sh

## Quick Start

1. Read the full instructions: \`cat .lean/roles/erdos-enhancer.md\`
2. **Check for stop signal before each iteration:**
   \`[[ -f \$REPO_ROOT/.loom/signals/stop-all ]] && echo "Stopping" && exit 0\`
3. Claim a stub: \`\$REPO_ROOT/scripts/erdos/claim-stub.sh claim-random-any\`
4. Enhance it (Lean proof, meta.json, annotations.json)
5. Build: \`pnpm build\`
6. Commit: \`git add -A && git commit -m "Enhance Erdős #N: Title"\`
7. Push: \`git push -u origin feature/enhancer-$i\`
8. Create PR: \`gh pr create --title "Enhance Erdős #N" --body "Stub enhancement" --label erdos-enhancement\`
9. Mark complete: \`\$REPO_ROOT/scripts/erdos/claim-stub.sh complete N\`
10. Reset for next: \`git checkout main && git pull && git checkout -B feature/enhancer-$i main\`
11. Repeat from step 2

Start now by running step 1 to read the full instructions, then claim and enhance a stub.
PROMPT_EOF

        # Start Claude Code with simple prompt pointing to instructions
        # Uses wrapper script for resilient error handling and retry logic
        local simple_prompt="You are $enhancer_id. Read $prompt_file for your instructions, then start the enhancement workflow."
        local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
        tmux send-keys -t "$session" "$wrapper_script --prompt '$simple_prompt' --log '$log_file' --max-retries 5" Enter

        print_success "Launched $session (worktree: $worktree_path)"
    done

    echo ""
    print_success "All agents launched in isolated worktrees!"
    echo ""
    echo "Each agent has:"
    echo "  - Its own worktree in .loom/worktrees/enhancer-N"
    echo "  - Its own branch: feature/enhancer-N"
    echo "  - Creates PRs instead of committing to main"
    echo ""
    echo "Commands:"
    echo "  $0 --status        Show agent status and worktrees"
    echo "  $0 --attach N      Attach to agent N's tmux session"
    echo "  $0 --stop          Stop all agents"
    echo "  $0 --cleanup       Remove all enhancer worktrees"
}

# Main command dispatch
case "${1:-}" in
    --status|-s)
        show_status
        ;;
    --continue|-c)
        send_continue "${2:-all}"
        ;;
    --stop)
        stop_agents
        ;;
    --graceful-stop|-g)
        signal_graceful_stop "${2:-all}"
        ;;
    --cleanup)
        cleanup_worktrees
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
Parallel Erdős Stub Enhancement (with Worktree Isolation)

Launch multiple Claude Code agents to enhance gallery stubs concurrently.
Each agent works in its own git worktree with a dedicated branch.

Usage:
  $0 [count]            Launch N agents (default: 3, max: 8)
  $0 --status           Show running agents, worktrees, and claims
  $0 --continue         Resume all agents after API limits reset
  $0 --continue N       Resume agent N specifically
  $0 --graceful-stop    Signal agents to stop after current work
  $0 --graceful-stop N  Signal agent N to stop after current work
  $0 --stop             Force stop all agents immediately
  $0 --cleanup          Stop agents and remove all enhancer worktrees
  $0 --attach N         Attach to agent N's tmux session
  $0 --help             Show this help

How it works:
  1. Each agent gets its own worktree: .loom/worktrees/enhancer-N
  2. Each agent works on its own branch: feature/enhancer-N
  3. Agents claim stubs atomically (no duplicates)
  4. Each agent: claim → enhance → commit → push → create PR → repeat
  5. PRs can be reviewed and merged independently

Examples:
  $0                    # Launch 3 agents
  $0 5                  # Launch 5 agents
  $0 --status           # Check progress
  $0 --attach 2         # Interact with agent 2
  $0 --cleanup          # Clean up everything

Monitoring:
  # Check claim status
  ./scripts/erdos/claim-stub.sh status

  # List PRs from enhancers
  gh pr list --label erdos-enhancement

  # View git worktrees
  git worktree list

Requirements:
  - tmux
  - claude (Claude Code CLI)
  - gh (GitHub CLI)
  - Node.js (for find-stubs.ts)

Notes:
  - Agents create PRs instead of committing to main
  - Use --cleanup to remove worktrees when done
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
