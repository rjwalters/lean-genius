#!/bin/bash
#
# launch-agent.sh - Launch the peer reviewer agent
#
# Usage:
#   ./launch-agent.sh              Launch peer reviewer
#   ./launch-agent.sh --slot N     Launch in specific slot (for multi-instance)
#   ./launch-agent.sh --stop       Stop the peer reviewer
#   ./launch-agent.sh --status     Check status
#   ./launch-agent.sh --attach     Attach to session
#   ./launch-agent.sh --logs       Tail logs
#
# Environment:
#   REVIEWER_INTERVAL - Interval in minutes between reviews (default: 60)

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
WORKTREES_DIR="$REPO_ROOT/.loom/worktrees"
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"

SLOT="${2:-1}"
if [[ "${1:-}" == "--slot" ]] && [[ -n "${2:-}" ]]; then
    SLOT="$2"
    shift 2
fi

SESSION_NAME="peer-reviewer-${SLOT}"
AGENT_ID="peer-reviewer-${SLOT}"
LOG_FILE="$LOGS_DIR/${AGENT_ID}.log"
INTERVAL="${REVIEWER_INTERVAL:-60}"
WORKTREE_PATH="$WORKTREES_DIR/${AGENT_ID}"
BRANCH_NAME="feature/${AGENT_ID}"

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

# Shared worktree reclaim helper (remove_own_worktree, guards 1-5).
# shellcheck source=../lib/worktree-cleanup.sh
source "$REPO_ROOT/scripts/lib/worktree-cleanup.sh"

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

# Create or update worktree
create_worktree() {
    mkdir -p "$WORKTREES_DIR"

    if [[ -d "$WORKTREE_PATH" ]]; then
        print_info "Worktree already exists, syncing with main..."
        (
            cd "$WORKTREE_PATH"
            git fetch origin main 2>/dev/null || true
            git stash 2>/dev/null || true
            if git reset --hard origin/main 2>/dev/null; then
                print_success "Synced with origin/main"
            else
                print_warning "Could not sync with origin/main"
            fi
            git stash pop 2>/dev/null || true
        )
        return 0
    fi

    print_info "Creating worktree for ${AGENT_ID} at $WORKTREE_PATH..."

    git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main 2>/dev/null || {
        git worktree add "$WORKTREE_PATH" "$BRANCH_NAME" 2>/dev/null || {
            git branch -D "$BRANCH_NAME" 2>/dev/null || true
            git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main
        }
    }

    # Install node dependencies in worktree
    if [[ -f "$WORKTREE_PATH/package.json" ]]; then
        print_info "Installing node dependencies..."
        (cd "$WORKTREE_PATH" && pnpm install --frozen-lockfile 2>/dev/null) || true
    fi

    print_success "Created peer reviewer worktree"
}

# Create prompt file
create_prompt_file() {
    local prompt_file="$LOGS_DIR/${AGENT_ID}-prompt.md"

    cat > "$prompt_file" << EOF
# Peer Reviewer Agent Instructions

You are the **peer reviewer** agent (${AGENT_ID}). Your mission is to deeply review proof gallery entries.

## Environment

- REVIEWER_ID: ${AGENT_ID}
- REPO_ROOT: $WORKTREE_PATH
- INTERVAL: $INTERVAL minutes
- LOG_FILE: $LOG_FILE

## Your Workflow (Repeat Every $INTERVAL Minutes)

1. **Check for stop signal**
   \`\`\`bash
   if [[ -f "$SIGNALS_DIR/stop-peer-reviewer" ]] || [[ -f "$SIGNALS_DIR/stop-${AGENT_ID}" ]] || [[ -f "$SIGNALS_DIR/stop-all" ]]; then
       echo "Stop signal received. Exiting."
       exit 0
   fi
   \`\`\`

2. **Claim and review a proof**
   Follow the workflow in \`.lean/roles/peer-reviewer.md\`

3. **Wait for next interval**
   \`\`\`bash
   echo "Next review in $INTERVAL minutes..."
   sleep ${INTERVAL}m
   \`\`\`

4. **Repeat from step 1**

## Start Now

Begin by:
1. Reading the peer reviewer role: \`cat .lean/roles/peer-reviewer.md\`
2. Claiming your first target: \`./scripts/peer-reviewer/claim-target.sh claim-next\`
3. Executing the 5-phase review workflow
4. Continuing the loop
EOF

    echo "$prompt_file"
}

# Launch the agent
launch_agent() {
    check_deps
    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR"

    # Remove any existing stop signal
    rm -f "$SIGNALS_DIR/stop-peer-reviewer"
    rm -f "$SIGNALS_DIR/stop-${AGENT_ID}"

    # Kill existing session if any
    tmux kill-session -t "$SESSION_NAME" 2>/dev/null || true

    # Create or update worktree
    create_worktree

    # Create prompt file
    local prompt_file
    prompt_file=$(create_prompt_file)

    # Per-role override: PEER_REVIEWER_CLAUDE_MODEL > CLAUDE_MODEL > wrapper default.
    local peer_reviewer_model="${PEER_REVIEWER_CLAUDE_MODEL:-${CLAUDE_MODEL:-claude-opus-4-8}}"

    print_info "Launching peer reviewer agent (${AGENT_ID})..."
    print_info "Interval: $INTERVAL minutes"
    print_info "Worktree: $WORKTREE_PATH"
    print_info "Model: $peer_reviewer_model"

    # Launch in tmux with wrapper
    local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
    tmux new-session -d -s "$SESSION_NAME" -c "$WORKTREE_PATH" \
        "REVIEWER_ID=${AGENT_ID} REPO_ROOT=$WORKTREE_PATH CLAUDE_MODEL=$peer_reviewer_model $wrapper_script --daemon --prompt 'You are the peer reviewer agent. Read $prompt_file for your instructions, then start the review loop.' --log '$LOG_FILE'"

    print_success "Launched peer reviewer agent (${AGENT_ID})"
    echo ""
    echo "Commands:"
    echo "  ./scripts/peer-reviewer/launch-agent.sh --status     Check status"
    echo "  ./scripts/peer-reviewer/launch-agent.sh --attach     Attach to session"
    echo "  ./scripts/peer-reviewer/launch-agent.sh --logs       Tail logs"
    echo "  ./scripts/peer-reviewer/launch-agent.sh --stop       Stop agent"
}

# Stop the agent
stop_agent() {
    print_info "Stopping peer reviewer (${AGENT_ID})..."

    touch "$SIGNALS_DIR/stop-${AGENT_ID}"
    sleep 2

    if tmux kill-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Stopped peer reviewer (${AGENT_ID})"
    else
        print_info "No peer reviewer session found"
    fi

    rm -f "$SIGNALS_DIR/stop-${AGENT_ID}"

    # Reclaim the agent's worktree now that its session is gone. The session is
    # dead (kill-session above) so the worktree is idle; remove_own_worktree
    # applies the shared safety guards (dirty / unpushed-or-unbacked / locked /
    # active-process / current-checkout) and is a no-op if there is nothing to
    # remove.
    remove_own_worktree "$WORKTREE_PATH"
}

# Check status
check_status() {
    echo "=== Peer Reviewer Status (${AGENT_ID}) ==="
    echo ""

    if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Peer reviewer is running"
        echo ""
        echo "Session: $SESSION_NAME"
        echo "Worktree: $WORKTREE_PATH"
        echo "Log file: $LOG_FILE"

        if [[ -d "$WORKTREE_PATH" ]]; then
            local branch
            branch=$(cd "$WORKTREE_PATH" && git branch --show-current 2>/dev/null || echo "unknown")
            echo "Branch: $branch"
        fi

        if [[ -f "$LOG_FILE" ]]; then
            echo ""
            echo "Recent activity:"
            tail -5 "$LOG_FILE" 2>/dev/null || echo "  (no logs yet)"
        fi
    else
        print_info "Peer reviewer is not running"
    fi

    echo ""
    # Show review stats
    if command -v npx >/dev/null 2>&1; then
        npx tsx "$REPO_ROOT/scripts/peer-reviewer/find-targets.ts" --stats 2>/dev/null || true
    fi
}

# Attach to session
attach_session() {
    if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_error "No peer reviewer session found"
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

# Main dispatch
case "${1:-}" in
    --stop)     stop_agent ;;
    --status)   check_status ;;
    --attach)   attach_session ;;
    --logs)     tail_logs ;;
    --slot)
        # --slot already handled above, launch
        launch_agent
        ;;
    ""|--launch)
        launch_agent
        ;;
    *)
        echo "Usage: launch-agent.sh [--slot N] [--stop|--status|--attach|--logs]"
        exit 1
        ;;
esac
