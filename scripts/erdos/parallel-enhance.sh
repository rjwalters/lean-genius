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

        # Create the prompt
        local prompt="You are Erdős stub enhancer agent $enhancer_id working in an isolated git worktree.

Your worktree: $worktree_path
Your branch: feature/enhancer-$i

WORKFLOW:
1. Claim: \$REPO_ROOT/scripts/erdos/claim-stub.sh claim-random
2. Enhance the claimed stub:
   - Rewrite proofs/Proofs/Erdos{N}Problem.lean
   - Update src/data/proofs/erdos-{n}/meta.json
   - Create src/data/proofs/erdos-{n}/annotations.json
3. Build: pnpm build
4. Commit: git add -A && git commit -m 'Enhance Erdős #{N}: Title'
5. Push: git push -u origin feature/enhancer-$i
6. PR: gh pr create --title 'Enhance Erdős #{N}' --body 'Stub enhancement' --label 'erdos-enhancement'
7. Complete: \$REPO_ROOT/scripts/erdos/claim-stub.sh complete {N}
8. Reset branch for next stub: git checkout main && git pull origin main && git checkout -B feature/enhancer-$i main
9. Repeat from step 1

Read .loom/roles/erdos-enhancer.md for detailed enhancement guidelines.
Start now with step 1."

        # Start Claude Code
        tmux send-keys -t "$session" "claude --dangerously-skip-permissions \"$prompt\" 2>&1 | tee '$log_file'" Enter

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
    --stop)
        stop_agents
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
  $0 --stop             Stop all agents
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
