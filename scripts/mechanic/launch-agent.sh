#!/bin/bash
#
# launch-agent.sh - Launch the Lean mechanic agent (repair specialist)
#
# Repairs issues found by auditors and peer reviewers: metadata fixes,
# Lean code repairs, and Aristotle companion file creation.
#
# Usage:
#   ./launch-agent.sh              Launch mechanic (default 15min interval)
#   ./launch-agent.sh --stop       Stop the mechanic
#   ./launch-agent.sh --status     Check mechanic status
#   ./launch-agent.sh --attach     Attach to mechanic session
#   ./launch-agent.sh --logs       Tail mechanic logs
#   ./launch-agent.sh --graceful-stop  Signal mechanic to stop after current work
#
# Environment:
#   MECHANIC_INTERVAL - Interval in minutes between repair cycles (default: 15)
#   SESSION_NAME      - tmux session name (default: mechanic-agent; use mechanic-1..3 for multi-slot)

set -euo pipefail

# Find repo root (resolves worktrees to the main repo, not the worktree dir)
find_repo_root() {
    local common_git
    common_git="$(git rev-parse --git-common-dir 2>/dev/null)" || {
        echo "Error: Not in a git repository" >&2
        return 1
    }
    if [[ "$common_git" == ".git" ]]; then
        local dir="$PWD"
        while [[ "$dir" != "/" ]]; do
            if [[ -d "$dir/.git" ]]; then
                echo "$dir"
                return 0
            fi
            dir="$(dirname "$dir")"
        done
        echo "Error: Could not resolve repo root" >&2
        return 1
    fi
    dirname "$common_git"
}

REPO_ROOT="$(find_repo_root)"
WORKTREES_DIR="$REPO_ROOT/.loom/worktrees"
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
SESSION_NAME="${SESSION_NAME:-mechanic-agent}"
LOG_FILE="$LOGS_DIR/${SESSION_NAME}.log"
INTERVAL="${MECHANIC_INTERVAL:-30}"
WORKTREE_PATH="$WORKTREES_DIR/${SESSION_NAME}"
BRANCH_NAME="feature/${SESSION_NAME}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

print_error() { echo -e "${RED}x $1${NC}"; }
print_success() { echo -e "${GREEN}+ $1${NC}"; }
print_info() { echo -e "${BLUE}i $1${NC}"; }
print_warning() { echo -e "${YELLOW}! $1${NC}"; }

# Check dependencies
check_deps() {
    local missing=()
    command -v tmux >/dev/null 2>&1 || missing+=("tmux")
    command -v claude >/dev/null 2>&1 || missing+=("claude")
    command -v jq >/dev/null 2>&1 || missing+=("jq")

    if [[ ${#missing[@]} -gt 0 ]]; then
        print_error "Missing dependencies: ${missing[*]}"
        exit 1
    fi
}

# Create or update worktree for mechanic
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

    print_info "Creating worktree for mechanic at $WORKTREE_PATH..."

    # Try to create worktree
    git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main 2>/dev/null || {
        # Branch might exist, try to use it
        git worktree add "$WORKTREE_PATH" "$BRANCH_NAME" 2>/dev/null || {
            # Remove and recreate branch
            git branch -D "$BRANCH_NAME" 2>/dev/null || true
            git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main
        }
    }

    # Install node dependencies in worktree (needed for pnpm build validation)
    if [[ -f "$WORKTREE_PATH/package.json" ]]; then
        print_info "Installing node dependencies..."
        (cd "$WORKTREE_PATH" && pnpm install --frozen-lockfile 2>/dev/null) || true
    fi

    print_success "Created mechanic worktree"
}

# Create prompt file for mechanic
create_prompt_file() {
    local prompt_file="$LOGS_DIR/mechanic-prompt.md"

    cat > "$prompt_file" << EOF
# Lean Mechanic Agent Instructions

You are the **lean mechanic** agent. Your mission is to repair issues found by auditors and peer reviewers.

## Environment

- REPO_ROOT: $REPO_ROOT
- INTERVAL: $INTERVAL minutes
- LOG_FILE: $LOG_FILE

## Your Workflow (Repeat Every $INTERVAL Minutes)

1. **Check for stop signal**
   \`\`\`bash
   if [[ -f "$SIGNALS_DIR/stop-mechanic" ]] || [[ -f "$SIGNALS_DIR/stop-all" ]]; then
       echo "Stop signal received. Exiting."
       exit 0
   fi
   \`\`\`

2. **Sync with main**
   \`\`\`bash
   git fetch origin main 2>/dev/null
   git reset --hard origin/main 2>/dev/null
   \`\`\`

3. **Find work** (priority order)
   \`\`\`bash
   # Auditor issues
   gh issue list --label="loom:auditor" --state=open --limit=10 --json number,title

   # Unaddressed peer review comments
   gh pr list --state=open --json number,title,reviewDecision \\
     --jq '.[] | select(.reviewDecision == "CHANGES_REQUESTED")'
   \`\`\`

4. **Claim via branch** -- create \`fix/mechanic-<issue>\` branch; skip if remote already has it

5. **Triage and fix** -- metadata, Lean code, or Aristotle companion file

6. **Submit PR** -- do NOT add \`loom:review-requested\`

7. **Wait for next interval**
   \`\`\`bash
   echo "Next repair cycle in $INTERVAL minutes..."
   sleep ${INTERVAL}m
   \`\`\`

8. **Repeat from step 1**

## Start Now

Begin by:
1. Reading the lean mechanic skill: \`cat $REPO_ROOT/.claude/commands/lean-mechanic.md\`
2. Checking for auditor issues: \`gh issue list --label="loom:auditor" --state=open\`
3. Claiming and fixing the highest-priority item
4. Starting the periodic repair loop

Good luck, mechanic!
EOF

    echo "$prompt_file"
}

# Launch the mechanic agent
launch_agent() {
    check_deps
    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR"

    # Remove any existing stop signal
    rm -f "$SIGNALS_DIR/stop-mechanic"

    # Kill existing session if any
    tmux kill-session -t "$SESSION_NAME" 2>/dev/null || true

    # Create or update worktree
    create_worktree

    # Symlink OAuth tokens so the claude-wrapper can find them in the worktree.
    # Guard against self-pointing symlinks (corrupts load balancing).
    if [[ -d "$REPO_ROOT/.loom/tokens" ]]; then
        local src="$REPO_ROOT/.loom/tokens"
        local dst="$WORKTREE_PATH/.loom/tokens"
        local src_real dst_real
        src_real="$(cd "$src" 2>/dev/null && pwd -P)"
        dst_real="$(dirname "$dst")"; dst_real="$(cd "$dst_real" 2>/dev/null && pwd -P)/$(basename "$dst")"
        if [[ "$src_real" != "$dst_real" ]]; then
            mkdir -p "$WORKTREE_PATH/.loom" 2>/dev/null || true
            ln -sfn "$src_real" "$dst"
        fi
    fi

    # Create prompt file
    local prompt_file
    prompt_file=$(create_prompt_file)

    print_info "Launching mechanic agent..."
    print_info "Session: $SESSION_NAME"
    print_info "Interval: $INTERVAL minutes"
    print_info "Worktree: $WORKTREE_PATH"

    # Launch in tmux with resilient wrapper in DAEMON mode
    local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
    tmux new-session -d -s "$SESSION_NAME" -c "$WORKTREE_PATH" \
        "ENHANCER_ID=mechanic REPO_ROOT=$WORKTREE_PATH $wrapper_script --daemon --prompt 'You are the lean mechanic agent. Read $prompt_file for your instructions, then start the repair loop.' --log '$LOG_FILE'"

    print_success "Launched mechanic agent"
    echo ""
    echo "Commands:"
    echo "  ./scripts/mechanic/launch-agent.sh --status     Check status"
    echo "  ./scripts/mechanic/launch-agent.sh --attach     Attach to session"
    echo "  ./scripts/mechanic/launch-agent.sh --logs       Tail logs"
    echo "  ./scripts/mechanic/launch-agent.sh --stop       Stop agent"
}

# Stop the mechanic
stop_agent() {
    print_info "Stopping mechanic agent..."

    # Create stop signal for graceful shutdown
    touch "$SIGNALS_DIR/stop-mechanic"

    # Give it a moment to notice
    sleep 2

    # Kill the session
    if tmux kill-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Stopped mechanic agent"
    else
        print_info "No mechanic session found"
    fi

    # Clean up signal
    rm -f "$SIGNALS_DIR/stop-mechanic"
}

# Graceful stop (just create signal, don't kill)
graceful_stop_agent() {
    print_info "Sending graceful stop signal to mechanic agent..."
    mkdir -p "$SIGNALS_DIR"
    touch "$SIGNALS_DIR/stop-mechanic"
    print_success "Stop signal created. Mechanic will stop after current work."
}

# Check status
check_status() {
    echo "=== Mechanic Status ==="
    echo ""

    if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Mechanic is running"
        echo ""
        echo "Session: $SESSION_NAME"
        echo "Worktree: $WORKTREE_PATH"
        echo "Log file: $LOG_FILE"
        echo "Interval: $INTERVAL minutes"

        # Show worktree git status
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
        print_info "Mechanic is not running"
        echo ""
        if [[ -d "$WORKTREE_PATH" ]]; then
            echo "Worktree exists: $WORKTREE_PATH"
        fi
    fi
}

# Attach to session
attach_session() {
    if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_error "No mechanic session found"
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
    --stop|-s)
        stop_agent
        ;;
    --graceful-stop)
        graceful_stop_agent
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
Lean Mechanic Agent Launcher

Launches an autonomous agent that periodically repairs issues found by
auditors and peer reviewers. Fixes metadata mismatches, Lean code issues,
and creates Aristotle companion files for sorry-heavy proofs.

The agent runs in an isolated git worktree at $WORKTREES_DIR/$SESSION_NAME
to prevent contention with other agents working in the main repository.

Usage:
  ./launch-agent.sh              Launch mechanic (default 15min interval)
  ./launch-agent.sh --stop       Stop the mechanic
  ./launch-agent.sh --graceful-stop  Signal mechanic to stop
  ./launch-agent.sh --status     Check mechanic status
  ./launch-agent.sh --attach     Attach to mechanic session
  ./launch-agent.sh --logs       Tail mechanic logs
  ./launch-agent.sh --help       Show this help

Environment Variables:
  MECHANIC_INTERVAL  Interval in minutes between repair cycles (default: 15)
  SESSION_NAME       tmux session name (default: mechanic-agent; use mechanic-1..3 for multi-slot)

Examples:
  ./launch-agent.sh                              # Start with defaults
  MECHANIC_INTERVAL=5 ./launch-agent.sh          # Check every 5 minutes
  SESSION_NAME=mechanic-2 ./launch-agent.sh      # Launch in slot 2
  ./launch-agent.sh --attach                     # Watch the agent work
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
