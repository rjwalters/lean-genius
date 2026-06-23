#!/bin/bash
#
# parallel-enrich.sh - Launch multiple proof enrichment agents in isolated worktrees
#
# Usage:
#   ./parallel-enrich.sh                    # Launch 2 agents (default)
#   ./parallel-enrich.sh 3                  # Launch 3 agents
#   ./parallel-enrich.sh --status           # Show agent status
#   ./parallel-enrich.sh --stop             # Stop all agents
#   ./parallel-enrich.sh --logs <N>         # Tail logs for agent N
#   ./parallel-enrich.sh --cleanup          # Remove all enricher worktrees
#
# Each agent runs in its own git worktree with a dedicated branch.
# Agents work autonomously: claim target → enrich → commit → push → create PR → repeat.

set -euo pipefail

# Configuration
DEFAULT_AGENTS=2
MAX_AGENTS=5
SESSION_PREFIX="enricher"
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
WORKTREES_DIR="$REPO_ROOT/.loom/worktrees"
ROLE_FILE="$REPO_ROOT/.lean/roles/enricher.md"
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
CLAIM_TTL=90  # Minutes

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

print_info() { echo -e "${BLUE}i $1${NC}"; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_warning() { echo -e "${YELLOW}! $1${NC}"; }
print_error() { echo -e "${RED}x $1${NC}" >&2; }

# Shared worktree reclaim helper (remove_own_worktree, guards 1-5).
# shellcheck source=lib/worktree-cleanup.sh
source "$REPO_ROOT/scripts/lib/worktree-cleanup.sh"

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
    local worktree_path="$WORKTREES_DIR/enricher-$agent_num"
    local branch_name="feature/enricher-$agent_num"

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

    echo "$worktree_path"
}

# Show status of all agents
show_status() {
    echo "=== Proof Enrichment Agents ==="
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
            local worktree_path="$WORKTREES_DIR/enricher-$agent_num"
            local branch=""

            if [[ -d "$worktree_path" ]]; then
                branch=$(cd "$worktree_path" && git branch --show-current 2>/dev/null || echo "unknown")
            fi

            echo "  $session: worktree=$worktree_path branch=$branch"
        done <<< "$running"
    fi

    echo ""

    # Show claim status
    echo "=== Enrichment Claims ==="
    "$REPO_ROOT/scripts/enricher/claim-target.sh" status 2>/dev/null || echo "  (claim system not initialized)"

    echo ""

    # Show worktrees
    echo "=== Worktrees ==="
    git worktree list | grep enricher || echo "  (no enricher worktrees)"

    # Show stop signal status
    echo ""
    echo "=== Stop Signals ==="
    if [[ -f "$SIGNALS_DIR/stop-all" ]]; then
        print_warning "STOP-ALL signal pending - agents will stop after current work"
    else
        local has_individual=false
        for sig in "$SIGNALS_DIR"/stop-enricher-*; do
            if [[ -f "$sig" ]]; then
                has_individual=true
                local agent_num=$(basename "$sig" | sed 's/stop-enricher-//')
                print_warning "STOP signal pending for enricher-$agent_num"
            fi
        done
        if [[ "$has_individual" == "false" ]]; then
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
    else
        touch "$SIGNALS_DIR/stop-enricher-$agent_num"
        print_success "Signaled enricher-$agent_num to stop after completing current work"
    fi
}

# Clear stop signals
clear_stop_signals() {
    rm -f "$SIGNALS_DIR/stop-all" 2>/dev/null || true
    rm -f "$SIGNALS_DIR/stop-enricher-"* 2>/dev/null || true
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
    "$REPO_ROOT/scripts/enricher/claim-target.sh" cleanup 2>/dev/null || true

    # Reclaim the now-idle worktrees. The sessions are killed above, so each
    # enricher-N worktree is idle; the shared guards preserve any that are
    # dirty / unpushed-or-unbacked / locked / current-checkout. Previously only
    # the explicit --cleanup path removed worktrees, leaking them on --stop.
    reclaim_worktrees
}

# Reclaim each enricher-N worktree using the shared safety guards. A dirty,
# unpushed/unbacked, locked, busy, or current-checkout worktree is preserved.
# Idempotent and quiet when there is nothing to remove.
reclaim_worktrees() {
    for i in $(seq 1 "$MAX_AGENTS"); do
        local worktree_path="$WORKTREES_DIR/enricher-$i"
        [[ -d "$worktree_path" ]] || continue
        remove_own_worktree "$worktree_path"
    done
    git worktree prune 2>/dev/null || true
}

# Cleanup all enricher worktrees
cleanup_worktrees() {
    echo "Cleaning up enricher worktrees..."

    # First stop any running agents (this also reclaims idle worktrees via the
    # shared guards).
    stop_agents

    # Reclaim any worktrees that survived stop_agents (e.g. no agent was
    # running), and delete their fully-backed-up branches.
    for i in $(seq 1 "$MAX_AGENTS"); do
        local worktree_path="$WORKTREES_DIR/enricher-$i"
        local branch_name="feature/enricher-$i"

        if [[ -d "$worktree_path" ]]; then
            remove_own_worktree "$worktree_path"
        fi

        # Delete branch only if its worktree was actually reclaimed (git refuses
        # to delete a branch still checked out in a worktree). A preserved
        # worktree keeps its branch.
        if [[ ! -d "$worktree_path" ]]; then
            git branch -D "$branch_name" 2>/dev/null && \
                print_info "Deleted branch: $branch_name" || true
        fi
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
    mkdir -p "$SIGNALS_DIR"

    # Clear any old stop signals
    clear_stop_signals

    # Ensure claim system is initialized
    mkdir -p "$REPO_ROOT/.lean/state/enrichment-claims"

    # Ensure tracker exists
    if [[ ! -f "$REPO_ROOT/src/data/proofs/enrichment-tracker.json" ]]; then
        echo '{"version": 1, "entries": {}}' > "$REPO_ROOT/src/data/proofs/enrichment-tracker.json"
    fi

    # Ensure we're on main and up to date
    print_info "Updating main branch..."
    git checkout main 2>/dev/null || true
    git pull origin main 2>/dev/null || true

    print_info "Launching $count enrichment agents with isolated worktrees..."
    echo ""

    for i in $(seq 1 "$count"); do
        local session="$SESSION_PREFIX-$i"
        local log_file="$LOGS_DIR/$session.log"
        local enricher_id="enricher-$i"

        # Create isolated worktree for this agent
        local worktree_path
        worktree_path=$(create_agent_worktree "$i")

        # Create tmux session starting in the worktree
        tmux new-session -d -s "$session" -c "$worktree_path"

        # Set environment variables
        tmux send-keys -t "$session" "export ENRICHER_ID='$enricher_id'" Enter
        tmux send-keys -t "$session" "export CLAIM_TTL='$CLAIM_TTL'" Enter
        tmux send-keys -t "$session" "export REPO_ROOT='$REPO_ROOT'" Enter
        # Honour ENRICHER_CLAUDE_MODEL (per-role) > CLAUDE_MODEL (global)
        local enricher_model="${ENRICHER_CLAUDE_MODEL:-${CLAUDE_MODEL:-claude-opus-4-8}}"
        tmux send-keys -t "$session" "export CLAUDE_MODEL='$enricher_model'" Enter

        # Write prompt to file (avoids tmux multiline issues)
        local prompt_file="$LOGS_DIR/$session-prompt.md"
        cat > "$prompt_file" << PROMPT_EOF
# Proof Enrichment Agent $enricher_id

You are working in an isolated git worktree with your own branch.

**Your worktree:** $worktree_path
**Your branch:** feature/enricher-$i
**Claim script:** \$REPO_ROOT/scripts/enricher/claim-target.sh

## Quick Start

1. Read the full instructions: \`cat .lean/roles/enricher.md\`
2. **Check for stop signal before each iteration:**
   \`[[ -f \$REPO_ROOT/.loom/signals/stop-all ]] && echo "Stopping" && exit 0\`
3. Claim a target: \`\$REPO_ROOT/scripts/enricher/claim-target.sh claim-next\`
4. Enrich it (improve meta.json, annotations.json - add depth, cross-refs, context)
5. Build: \`pnpm build\`
6. Commit: \`git add src/data/proofs/<id>/ && git commit -m "Enrich <title>: add depth"\`
7. Push: \`git push -u origin feature/enricher-$i\`
8. Create PR: \`gh pr create --title "Enrich <title>" --body "Enrichment pass" --label enrichment\`
9. Mark complete: \`\$REPO_ROOT/scripts/enricher/claim-target.sh complete <id>\`
10. Reset for next: \`git checkout main && git pull && git checkout -B feature/enricher-$i main\`
11. Repeat from step 2

Start now by running step 1 to read the full instructions, then claim and enrich a target.
PROMPT_EOF

        # Start Claude Code with simple prompt pointing to instructions
        local simple_prompt="You are $enricher_id. Read $prompt_file for your instructions, then start the enrichment workflow."
        local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
        tmux send-keys -t "$session" "$wrapper_script --prompt '$simple_prompt' --log '$log_file' --max-retries 5" Enter

        print_success "Launched $session (worktree: $worktree_path)"
    done

    echo ""
    print_success "All agents launched in isolated worktrees!"
    echo ""
    echo "Each agent has:"
    echo "  - Its own worktree in .loom/worktrees/enricher-N"
    echo "  - Its own branch: feature/enricher-N"
    echo "  - Creates PRs instead of committing to main"
    echo ""
    echo "Commands:"
    echo "  $0 --status        Show agent status and worktrees"
    echo "  $0 --attach N      Attach to agent N's tmux session"
    echo "  $0 --stop          Stop all agents"
    echo "  $0 --cleanup       Remove all enricher worktrees"
}

# Main command dispatch
case "${1:-}" in
    --status|-s)
        show_status
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
    --slot)
        if [[ -z "${2:-}" ]]; then
            print_error "Usage: $0 --slot <agent-number>"
            exit 1
        fi
        slot_num="$2"
        if [[ $slot_num -lt 1 || $slot_num -gt $MAX_AGENTS ]]; then
            print_error "Slot must be between 1 and $MAX_AGENTS (got: $slot_num)"
            exit 1
        fi
        check_deps
        mkdir -p "$LOGS_DIR" "$WORKTREES_DIR" "$SIGNALS_DIR"
        mkdir -p "$REPO_ROOT/.lean/state/enrichment-claims"
        if [[ ! -f "$REPO_ROOT/src/data/proofs/enrichment-tracker.json" ]]; then
            echo '{"version": 1, "entries": {}}' > "$REPO_ROOT/src/data/proofs/enrichment-tracker.json"
        fi
        print_info "Updating main branch..."
        git fetch origin main 2>/dev/null || true
        git checkout main 2>/dev/null || true
        git pull origin main 2>/dev/null || true

        i="$slot_num"
        session="$SESSION_PREFIX-$i"
        log_file="$LOGS_DIR/$session.log"
        enricher_id="enricher-$i"
        worktree_path=$(create_agent_worktree "$i")
        tmux kill-session -t "$session" 2>/dev/null || true
        tmux new-session -d -s "$session" -c "$worktree_path"
        tmux send-keys -t "$session" "export ENRICHER_ID='$enricher_id'" Enter
        tmux send-keys -t "$session" "export CLAIM_TTL='$CLAIM_TTL'" Enter
        tmux send-keys -t "$session" "export REPO_ROOT='$REPO_ROOT'" Enter
        enricher_model="${ENRICHER_CLAUDE_MODEL:-${CLAUDE_MODEL:-claude-opus-4-8}}"
        tmux send-keys -t "$session" "export CLAUDE_MODEL='$enricher_model'" Enter
        prompt_file="$LOGS_DIR/$session-prompt.md"
        cat > "$prompt_file" << PROMPT_EOF
# Proof Enrichment Agent $enricher_id

You are working in an isolated git worktree with your own branch.

**Your worktree:** $worktree_path
**Your branch:** feature/enricher-$i
**Claim script:** \$REPO_ROOT/scripts/enricher/claim-target.sh

## Quick Start

1. Read the full instructions: \`cat .lean/roles/enricher.md\`
2. **Check for stop signal before each iteration:**
   \`[[ -f \$REPO_ROOT/.loom/signals/stop-all ]] && echo "Stopping" && exit 0\`
3. Claim a target: \`\$REPO_ROOT/scripts/enricher/claim-target.sh claim-next\`
4. Enrich it (improve meta.json, annotations.json - add depth, cross-refs, context)
5. Build: \`pnpm build\`
6. Commit: \`git add src/data/proofs/<id>/ && git commit -m "Enrich <title>: add depth"\`
7. Push: \`git push -u origin feature/enricher-$i\`
8. Create PR: \`gh pr create --title "Enrich <title>" --body "Enrichment pass" --label enrichment\`
9. Mark complete: \`\$REPO_ROOT/scripts/enricher/claim-target.sh complete <id>\`
10. Reset for next: \`git checkout main && git pull && git checkout -B feature/enricher-$i main\`
11. Repeat from step 2

Start now by running step 1 to read the full instructions, then claim and enrich a target.
PROMPT_EOF
        simple_prompt="You are $enricher_id. Read $prompt_file for your instructions, then start the enrichment workflow."
        wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
        tmux send-keys -t "$session" "$wrapper_script --prompt '$simple_prompt' --log '$log_file' --max-retries 5" Enter
        print_success "Launched $session (worktree: $worktree_path)"
        ;;
    --help|-h)
        cat << EOF
Parallel Proof Enrichment (with Worktree Isolation)

Launch multiple Claude Code agents to enrich gallery proofs concurrently.
Each agent works in its own git worktree with a dedicated branch.

Usage:
  $0 [count]            Launch N agents (default: $DEFAULT_AGENTS, max: $MAX_AGENTS)
  $0 --slot N           Launch a single agent at slot N
  $0 --status           Show running agents, worktrees, and claims
  $0 --graceful-stop    Signal agents to stop after current work
  $0 --graceful-stop N  Signal agent N to stop after current work
  $0 --stop             Force stop all agents immediately
  $0 --cleanup          Stop agents and remove all enricher worktrees
  $0 --attach N         Attach to agent N's tmux session
  $0 --help             Show this help

How it works:
  1. Each agent gets its own worktree: .loom/worktrees/enricher-N
  2. Each agent works on its own branch: feature/enricher-N
  3. Agents claim targets atomically (no duplicates)
  4. Each agent: claim → enrich → commit → push → create PR → repeat
  5. Entries with fewer passes get prioritized
  6. PRs can be reviewed and merged independently

Examples:
  $0                    # Launch 2 agents
  $0 3                  # Launch 3 agents
  $0 --status           # Check progress
  $0 --attach 2         # Interact with agent 2
  $0 --cleanup          # Clean up everything

Requirements:
  - tmux
  - claude (Claude Code CLI)
  - gh (GitHub CLI)
  - Node.js (for find-targets.ts)

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
