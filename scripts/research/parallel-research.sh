#!/bin/bash
#
# parallel-research.sh - Launch parallel research agents
#
# Usage:
#   ./parallel-research.sh [count]           Launch N agents (default: 2, max: 5)
#   ./parallel-research.sh --status          Show running agents and claims
#   ./parallel-research.sh --graceful-stop   Signal agents to stop after current work
#   ./parallel-research.sh --stop            Force stop all agents immediately
#   ./parallel-research.sh --cleanup         Stop agents and remove worktrees
#   ./parallel-research.sh --attach N        Attach to agent N's tmux session
#
# Each agent works in its own git worktree with a dedicated branch.

set -euo pipefail

# Find repo root
find_repo_root() {
    local dir="$PWD"
    while [[ "$dir" != "/" ]]; do
        if [[ -d "$dir/.git" ]]; then
            echo "$dir"
            return 0
        fi
        dir="$(dirname "$dir")"
    done
    echo "Error: Not in a git repository" >&2
    return 1
}

REPO_ROOT="$(find_repo_root)"
WORKTREES_DIR="$REPO_ROOT/.loom/worktrees"
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
CLAIM_SCRIPT="$REPO_ROOT/scripts/research/claim-problem.sh"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

print_error() { echo -e "${RED}✗ $1${NC}"; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_info() { echo -e "${BLUE}ℹ $1${NC}"; }
print_warning() { echo -e "${YELLOW}⚠ $1${NC}"; }

# Check dependencies
check_deps() {
    local missing=()
    command -v tmux >/dev/null 2>&1 || missing+=("tmux")
    command -v claude >/dev/null 2>&1 || missing+=("claude")
    command -v gh >/dev/null 2>&1 || missing+=("gh")
    command -v jq >/dev/null 2>&1 || missing+=("jq")

    if [[ ${#missing[@]} -gt 0 ]]; then
        print_error "Missing dependencies: ${missing[*]}"
        exit 1
    fi
}

# Create worktree for an agent
create_worktree() {
    local agent_num="$1"
    local worktree_path="$WORKTREES_DIR/researcher-$agent_num"
    local branch_name="feature/researcher-$agent_num"

    if [[ -d "$worktree_path" ]]; then
        print_info "Worktree already exists: $worktree_path"
        return 0
    fi

    # Try to create worktree
    git worktree add "$worktree_path" -b "$branch_name" main 2>/dev/null || {
        # Branch might exist, try to use it
        git worktree add "$worktree_path" "$branch_name" 2>/dev/null || {
            # Remove and recreate branch
            git branch -D "$branch_name" 2>/dev/null || true
            git worktree add "$worktree_path" -b "$branch_name" main
        }
    }

    # Symlink .lake for fast Lean builds
    if [[ -d "$REPO_ROOT/proofs/.lake" ]] && [[ -d "$worktree_path/proofs" ]]; then
        rm -rf "$worktree_path/proofs/.lake" 2>/dev/null || true
        ln -s "$REPO_ROOT/proofs/.lake" "$worktree_path/proofs/.lake"
    fi
}

# Create prompt file for agent
create_prompt_file() {
    local agent_num="$1"
    local worktree_path="$WORKTREES_DIR/researcher-$agent_num"
    local prompt_file="$LOGS_DIR/researcher-$agent_num-prompt.md"

    cat > "$prompt_file" << EOF
# Research Agent Instructions

You are **researcher-$agent_num**. Your mission is to make meaningful progress on Lean theorem proving problems.

## Environment

- RESEARCHER_ID: researcher-$agent_num
- REPO_ROOT: $REPO_ROOT
- WORKTREE: $worktree_path
- CLAIM_TTL: 90 (minutes)

## Your Workflow

1. **Check for stop signal** before each iteration
2. **Check Aristotle results** for any completed proofs
3. **Claim a problem** using: \`$REPO_ROOT/scripts/research/claim-problem.sh claim-random\`
4. **Run one research iteration** following the research methodology
5. **Commit and push** your progress
6. **Create a PR** with your findings
7. **Update problem status** and release claim
8. **Repeat**

## Stop Signal Check

Before claiming each new problem:
\`\`\`bash
if [[ -f "$REPO_ROOT/.loom/signals/stop-all" ]] || \\
   [[ -f "$REPO_ROOT/.loom/signals/stop-researcher-$agent_num" ]]; then
    echo "Stop signal received. Exiting gracefully."
    exit 0
fi
\`\`\`

## Working Directory

Always work in your worktree:
\`\`\`bash
cd $worktree_path
\`\`\`

## Commands Reference

\`\`\`bash
# Claim a problem (knowledge-prioritized)
$REPO_ROOT/scripts/research/claim-problem.sh claim-random

# Check status
$REPO_ROOT/scripts/research/claim-problem.sh status

# Update problem status
$REPO_ROOT/scripts/research/claim-problem.sh update <problem-id> <status>

# Release claim
$REPO_ROOT/scripts/research/claim-problem.sh release <problem-id>
\`\`\`

## Start Now

Begin by:
1. Reading the researcher role: \`cat $REPO_ROOT/.loom/roles/researcher.md\`
2. Checking current status: \`$REPO_ROOT/scripts/research/claim-problem.sh status\`
3. Starting your research loop

Good luck, researcher-$agent_num!
EOF

    echo "$prompt_file"
}

# Launch a single agent
launch_agent() {
    local agent_num="$1"
    local worktree_path="$WORKTREES_DIR/researcher-$agent_num"
    local log_file="$LOGS_DIR/researcher-$agent_num.log"
    local session_name="researcher-$agent_num"

    # Create worktree
    print_info "Creating worktree for agent $agent_num..."
    create_worktree "$agent_num"

    # Create prompt file
    local prompt_file
    prompt_file=$(create_prompt_file "$agent_num")

    # Kill existing session if any
    tmux kill-session -t "$session_name" 2>/dev/null || true

    # Launch in tmux
    tmux new-session -d -s "$session_name" -c "$worktree_path" \
        "claude --dangerously-skip-permissions \"You are researcher-$agent_num. Read $prompt_file for your instructions, then start the research workflow.\" 2>&1 | tee -a $log_file"

    print_success "Launched $session_name (worktree: $worktree_path)"
}

# Launch multiple agents
launch_agents() {
    local count="${1:-2}"

    # Validate count
    if [[ $count -lt 1 || $count -gt 5 ]]; then
        print_error "Agent count must be between 1 and 5 (got: $count)"
        exit 1
    fi

    check_deps
    mkdir -p "$WORKTREES_DIR" "$LOGS_DIR" "$SIGNALS_DIR"

    # Update main branch first
    print_info "Updating main branch..."
    git fetch origin main 2>/dev/null || true
    git checkout main 2>/dev/null || true
    git pull origin main 2>/dev/null || true

    print_info "Launching $count research agents with isolated worktrees..."
    echo ""

    for i in $(seq 1 "$count"); do
        launch_agent "$i"
    done

    echo ""
    print_success "All agents launched in isolated worktrees!"
    echo ""
    echo "Each agent has:"
    echo "  - Its own worktree in .loom/worktrees/researcher-N"
    echo "  - Its own branch: feature/researcher-N"
    echo "  - Creates PRs for research progress"
    echo ""
    echo "Commands:"
    echo "  ./scripts/research/parallel-research.sh --status        Show agent status"
    echo "  ./scripts/research/parallel-research.sh --attach N      Attach to agent N"
    echo "  ./scripts/research/parallel-research.sh --graceful-stop Stop gracefully"
    echo "  ./scripts/research/parallel-research.sh --stop          Force stop all"
}

# Show status
show_status() {
    echo "=== Research Agents ==="
    echo ""

    # List running agents
    local running=0
    for session in $(tmux list-sessions -F '#{session_name}' 2>/dev/null | grep '^researcher-' || true); do
        local agent_num="${session#researcher-}"
        local worktree="$WORKTREES_DIR/researcher-$agent_num"
        local branch="feature/researcher-$agent_num"
        echo "  $session: worktree=$worktree branch=$branch"
        ((running++))
    done

    if [[ $running -eq 0 ]]; then
        echo "  (no agents running)"
    fi

    echo ""
    echo "=== Problem Claims ==="
    "$CLAIM_SCRIPT" status 2>/dev/null || echo "  (unable to get claim status)"

    echo ""
    echo "=== Worktrees ==="
    git worktree list | grep researcher || echo "  (no researcher worktrees)"

    echo ""
    echo "=== Stop Signals ==="
    if [[ -f "$SIGNALS_DIR/stop-all" ]]; then
        print_warning "STOP-ALL signal pending - agents will stop after current work"
    else
        local has_signal=false
        for signal in "$SIGNALS_DIR"/stop-researcher-*; do
            if [[ -f "$signal" ]]; then
                local agent_name
                agent_name=$(basename "$signal" | sed 's/stop-//')
                print_warning "Stop signal pending for $agent_name"
                has_signal=true
            fi
        done
        if [[ "$has_signal" == "false" ]]; then
            echo "  (no stop signals pending)"
        fi
    fi
}

# Signal agents to stop gracefully
signal_graceful_stop() {
    local agent_num="${1:-all}"
    mkdir -p "$SIGNALS_DIR"

    if [[ "$agent_num" == "all" ]]; then
        touch "$SIGNALS_DIR/stop-all"
        print_success "Signaled all agents to stop after completing current work"
        echo "Agents will finish their current research session before exiting."
    else
        touch "$SIGNALS_DIR/stop-researcher-$agent_num"
        print_success "Signaled researcher-$agent_num to stop after completing current work"
    fi
}

# Force stop all agents
force_stop() {
    print_info "Force stopping all research agents..."

    for session in $(tmux list-sessions -F '#{session_name}' 2>/dev/null | grep '^researcher-' || true); do
        tmux kill-session -t "$session" 2>/dev/null && \
            print_success "Stopped $session" || \
            print_warning "Could not stop $session"
    done

    # Clean up signals
    rm -f "$SIGNALS_DIR"/stop-all "$SIGNALS_DIR"/stop-researcher-* 2>/dev/null || true

    # Clean up stale claims
    "$CLAIM_SCRIPT" cleanup 2>/dev/null || true
}

# Cleanup everything
cleanup_all() {
    force_stop

    print_info "Removing researcher worktrees..."
    for worktree in "$WORKTREES_DIR"/researcher-*; do
        if [[ -d "$worktree" ]]; then
            git worktree remove "$worktree" --force 2>/dev/null && \
                print_success "Removed $worktree" || \
                print_warning "Could not remove $worktree"
        fi
    done

    git worktree prune 2>/dev/null || true
    print_success "Cleanup complete"
}

# Attach to agent session
attach_to_agent() {
    local agent_num="$1"
    local session_name="researcher-$agent_num"

    if ! tmux has-session -t "$session_name" 2>/dev/null; then
        print_error "No session found: $session_name"
        exit 1
    fi

    tmux attach-session -t "$session_name"
}

# Main command dispatch
case "${1:-}" in
    --status|-s)
        show_status
        ;;
    --graceful-stop)
        signal_graceful_stop "${2:-all}"
        ;;
    --stop)
        force_stop
        ;;
    --cleanup)
        cleanup_all
        ;;
    --attach|-a)
        if [[ -z "${2:-}" ]]; then
            print_error "Usage: $0 --attach <agent-number>"
            exit 1
        fi
        attach_to_agent "$2"
        ;;
    --help|-h)
        cat << EOF
Parallel Research Agents (with Worktree Isolation)

Launch multiple Claude Code agents to work on research problems concurrently.
Each agent works in its own git worktree with a dedicated branch.

Usage:
  ./parallel-research.sh [count]            Launch N agents (default: 2, max: 5)
  ./parallel-research.sh --status           Show running agents and claims
  ./parallel-research.sh --graceful-stop    Signal agents to stop after current work
  ./parallel-research.sh --graceful-stop N  Signal agent N to stop
  ./parallel-research.sh --stop             Force stop all agents immediately
  ./parallel-research.sh --cleanup          Stop agents and remove worktrees
  ./parallel-research.sh --attach N         Attach to agent N's tmux session
  ./parallel-research.sh --help             Show this help

How it works:
  1. Each agent gets its own worktree: .loom/worktrees/researcher-N
  2. Each agent works on its own branch: feature/researcher-N
  3. Agents claim problems atomically (knowledge-prioritized)
  4. Each agent: claim → research → commit → push → create PR → repeat
  5. PRs can be reviewed and merged independently

Examples:
  ./parallel-research.sh              # Launch 2 agents (default)
  ./parallel-research.sh 3            # Launch 3 agents
  ./parallel-research.sh --status     # Check progress
  ./parallel-research.sh --attach 1   # Watch agent 1 work
  ./parallel-research.sh --graceful-stop  # Stop after current work

Monitoring:
  # Check claim status
  ./scripts/research/claim-problem.sh status

  # List PRs from researchers
  gh pr list --label research

  # View agent logs
  tail -f .loom/logs/researcher-1.log
EOF
        ;;
    [0-9]*)
        launch_agents "$1"
        ;;
    "")
        launch_agents 2
        ;;
    *)
        print_error "Unknown command: $1"
        echo "Run '$0 --help' for usage"
        exit 1
        ;;
esac
