#!/bin/bash
#
# launch-agent.sh - Launch the Aristotle queue management agent in a worktree
#
# Usage:
#   ./launch-agent.sh              # Launch the agent
#   ./launch-agent.sh --status     # Show agent status
#   ./launch-agent.sh --stop       # Stop the agent
#   ./launch-agent.sh --attach     # Attach to agent session
#   ./launch-agent.sh --logs       # Tail agent logs
#
# The agent runs in its own worktree, managing Aristotle job submissions,
# retrieving completed proofs, and creating PRs for integrations.
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

SESSION_NAME="aristotle-agent"
WORKTREE_PATH="$REPO_ROOT/.loom/worktrees/aristotle"
BRANCH_NAME="feature/aristotle-integrations"
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
LOG_FILE="$LOGS_DIR/$SESSION_NAME.log"
ROLE_FILE="$REPO_ROOT/.loom/roles/aristotle-agent.md"

# Defaults
TARGET_ACTIVE="${ARISTOTLE_TARGET:-20}"
INTERVAL_MINUTES="${ARISTOTLE_INTERVAL:-30}"

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

    if [[ -z "${ARISTOTLE_API_KEY:-}" ]] && [[ ! -f "$HOME/.aristotle_key" ]]; then
        missing+=("ARISTOTLE_API_KEY (or ~/.aristotle_key)")
    fi

    if [[ ${#missing[@]} -gt 0 ]]; then
        print_error "Missing dependencies: ${missing[*]}"
        exit 1
    fi
}

# Check if agent is running
is_running() {
    tmux has-session -t "$SESSION_NAME" 2>/dev/null
}

# Create worktree
create_worktree() {
    if [[ -d "$WORKTREE_PATH" ]]; then
        print_info "Removing existing worktree..."
        git worktree remove "$WORKTREE_PATH" --force 2>/dev/null || rm -rf "$WORKTREE_PATH"
    fi

    git branch -D "$BRANCH_NAME" 2>/dev/null || true

    print_info "Creating worktree..."
    git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main

    # Symlink .lake for fast Lean builds
    if [[ -d "$REPO_ROOT/proofs/.lake" ]] && [[ -d "$WORKTREE_PATH/proofs" ]]; then
        rm -rf "$WORKTREE_PATH/proofs/.lake"
        ln -s "$REPO_ROOT/proofs/.lake" "$WORKTREE_PATH/proofs/.lake"
    fi
}

# Show status
show_status() {
    echo "=== Aristotle Agent Status ==="
    echo ""

    if is_running; then
        print_success "Agent is RUNNING"
        echo "  Session: $SESSION_NAME"
        echo "  Worktree: $WORKTREE_PATH"
        echo "  Logs: $LOG_FILE"
    else
        print_warning "Agent is NOT running"
    fi

    echo ""

    # Show Aristotle job status
    "$SCRIPT_DIR/aristotle-agent.sh" --status 2>/dev/null || true

    # Check stop signal
    echo ""
    if [[ -f "$SIGNALS_DIR/stop-aristotle" ]]; then
        print_warning "STOP signal pending - agent will stop after current cycle"
    fi
}

# Signal graceful stop
signal_stop() {
    mkdir -p "$SIGNALS_DIR"
    touch "$SIGNALS_DIR/stop-aristotle"
    print_success "Signaled agent to stop after current cycle"
    echo ""
    echo "The agent will:"
    echo "  1. Finish current integration cycle"
    echo "  2. Commit and push any pending work"
    echo "  3. Exit cleanly"
    echo ""
    echo "Monitor: $0 --status"
    echo "Force:   $0 --stop"
}

# Stop agent (force)
stop_agent() {
    if is_running; then
        tmux kill-session -t "$SESSION_NAME" 2>/dev/null
        print_success "Stopped agent"
    else
        print_info "Agent not running"
    fi

    rm -f "$SIGNALS_DIR/stop-aristotle" 2>/dev/null || true
}

# Attach to session
attach_agent() {
    if ! is_running; then
        print_error "Agent is not running"
        exit 1
    fi

    print_info "Attaching to $SESSION_NAME (Ctrl+B D to detach)"
    tmux attach -t "$SESSION_NAME"
}

# Tail logs
tail_logs() {
    if [[ ! -f "$LOG_FILE" ]]; then
        print_error "Log file not found: $LOG_FILE"
        exit 1
    fi

    print_info "Tailing logs (Ctrl+C to stop)"
    tail -f "$LOG_FILE"
}

# Launch agent
launch_agent() {
    check_deps

    if is_running; then
        print_warning "Agent already running"
        echo "Use '$0 --stop' to stop it first"
        exit 1
    fi

    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR"
    rm -f "$SIGNALS_DIR/stop-aristotle" 2>/dev/null || true

    # Update main
    print_info "Updating main branch..."
    git checkout main 2>/dev/null || true
    git pull origin main 2>/dev/null || true

    # Create worktree
    create_worktree

    # Create prompt file
    local prompt_file="$LOGS_DIR/$SESSION_NAME-prompt.md"
    cat > "$prompt_file" << PROMPT_EOF
# Aristotle Queue Management Agent

You are the Aristotle agent, responsible for managing the flow of Lean proofs through Aristotle's proof search system.

**Your worktree:** $WORKTREE_PATH
**Your branch:** $BRANCH_NAME
**Target active jobs:** $TARGET_ACTIVE
**Check interval:** $INTERVAL_MINUTES minutes

## Your Mission

Maintain ~$TARGET_ACTIVE active Aristotle jobs at all times, maximizing throughput of automated proof search. When proofs are completed, integrate them and create PRs.

## Instructions

Read your full role definition: \`cat $ROLE_FILE\`

## Main Loop

Execute this workflow continuously:

\`\`\`
while true:
    1. CHECK FOR STOP SIGNAL
    2. Check status of submitted jobs (update completed/failed)
    3. Retrieve completed solutions
    4. For each improved proof:
       a. Copy to proofs/Proofs/
       b. Run pnpm build to verify
       c. Commit changes
       d. Push to branch
       e. Create PR (or update existing)
    5. Submit new files to maintain $TARGET_ACTIVE active
    6. Sleep $INTERVAL_MINUTES minutes
    7. Repeat
\`\`\`

### Stop Signal Check

\`\`\`bash
if [[ -f "\$REPO_ROOT/.loom/signals/stop-aristotle" ]]; then
    echo "Stop signal received. Finishing current work and exiting."
    # Complete any pending PRs first
    exit 0
fi
\`\`\`

## Key Scripts

- \`\$REPO_ROOT/scripts/aristotle/find-candidates.sh\` - Find files to submit
- \`\$REPO_ROOT/scripts/aristotle/submit-batch.sh\` - Submit files to Aristotle
- \`\$REPO_ROOT/scripts/aristotle/check-jobs.sh\` - Check job status
- \`\$REPO_ROOT/scripts/aristotle/retrieve-integrate.sh\` - Download and integrate proofs
- \`\$REPO_ROOT/scripts/aristotle/aristotle-agent.sh\` - Run one complete cycle

## PR Strategy

Create PRs for batches of integrations:
- Title: "Integrate Aristotle proofs: erdos-X, erdos-Y, erdos-Z"
- Label: aristotle-integration
- Body: List problems integrated and sorry counts

Start now by reading your full role, then begin the main loop.
PROMPT_EOF

    # Start tmux session
    tmux new-session -d -s "$SESSION_NAME" -c "$WORKTREE_PATH"

    # Set environment with delays to avoid interleaving
    sleep 0.5
    tmux send-keys -t "$SESSION_NAME" "export REPO_ROOT='$REPO_ROOT'" Enter
    sleep 0.3
    tmux send-keys -t "$SESSION_NAME" "export ARISTOTLE_TARGET='$TARGET_ACTIVE'" Enter
    sleep 0.3
    tmux send-keys -t "$SESSION_NAME" "export ARISTOTLE_INTERVAL='$INTERVAL_MINUTES'" Enter
    sleep 0.3

    # Load API key if from file
    if [[ -f "$HOME/.aristotle_key" ]]; then
        tmux send-keys -t "$SESSION_NAME" "export ARISTOTLE_API_KEY=\$(cat ~/.aristotle_key)" Enter
        sleep 0.3
    fi

    # Launch Claude with resilient wrapper for error handling
    sleep 0.5
    local prompt="You are the Aristotle agent. Read $prompt_file for your instructions, then start the queue management workflow."
    local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
    tmux send-keys -t "$SESSION_NAME" "ENHANCER_ID=aristotle $wrapper_script --prompt '$prompt' --log '$LOG_FILE' --max-retries 5" Enter

    print_success "Launched Aristotle agent"
    echo ""
    echo "Agent details:"
    echo "  Session: $SESSION_NAME"
    echo "  Worktree: $WORKTREE_PATH"
    echo "  Branch: $BRANCH_NAME"
    echo "  Target: $TARGET_ACTIVE active jobs"
    echo "  Interval: $INTERVAL_MINUTES minutes"
    echo ""
    echo "Commands:"
    echo "  $0 --status      Show status"
    echo "  $0 --attach      Attach to session"
    echo "  $0 --logs        Tail logs"
    echo "  $0 --stop        Stop agent"
}

# Main
case "${1:-}" in
    --status|-s)
        show_status
        ;;
    --stop)
        stop_agent
        ;;
    --graceful-stop|-g)
        signal_stop
        ;;
    --attach|-a)
        attach_agent
        ;;
    --logs|-l)
        tail_logs
        ;;
    --help|-h)
        echo "Usage: $0 [command]"
        echo ""
        echo "Commands:"
        echo "  (none)           Launch the agent"
        echo "  --status, -s     Show agent status"
        echo "  --stop           Stop the agent"
        echo "  --graceful-stop  Signal graceful stop"
        echo "  --attach, -a     Attach to tmux session"
        echo "  --logs, -l       Tail agent logs"
        echo ""
        echo "Environment:"
        echo "  ARISTOTLE_TARGET   Target active jobs (default: 20)"
        echo "  ARISTOTLE_INTERVAL Check interval in minutes (default: 30)"
        ;;
    "")
        launch_agent
        ;;
    *)
        print_error "Unknown command: $1"
        echo "Use '$0 --help' for usage"
        exit 1
        ;;
esac
