#!/bin/bash
#
# launch-agent.sh - Launch the Aristotle queue management agent in a worktree
#
# Usage:
#   ./launch-agent.sh              # Launch the agent
#   ./launch-agent.sh --dry-run    # Preview launch without starting tmux
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
ROLE_FILE="$REPO_ROOT/.lean/roles/aristotle-agent.md"
PERSIST_DIR="$REPO_ROOT/.loom/state"
PERSIST_JOBS="$PERSIST_DIR/aristotle-jobs.json"

# Defaults
TARGET_ACTIVE="${ARISTOTLE_TARGET:-3}"
INTERVAL_MINUTES="${ARISTOTLE_INTERVAL:-30}"
DRY_RUN=false
ARGS=()

for arg in "$@"; do
    case "$arg" in
        --dry-run|-n)
            DRY_RUN=true
            ;;
        --help|-h)
            ARGS+=("--help")
            ;;
        *)
            ARGS+=("$arg")
            ;;
    esac
done

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

# Salvage aristotle-jobs.json before worktree destruction
salvage_jobs_file() {
    local worktree_jobs="$WORKTREE_PATH/research/aristotle-jobs.json"
    if [[ -f "$worktree_jobs" ]]; then
        mkdir -p "$PERSIST_DIR"
        cp "$worktree_jobs" "$PERSIST_JOBS"
        print_info "Salvaged aristotle-jobs.json to persistent state"
    fi
}

# Restore aristotle-jobs.json into new worktree from persistent state
restore_jobs_file() {
    local worktree_jobs="$WORKTREE_PATH/research/aristotle-jobs.json"
    if [[ -f "$PERSIST_JOBS" ]] && [[ -f "$worktree_jobs" ]]; then
        # Only restore if persisted copy is newer (has more data)
        local persist_jobs_count worktree_jobs_count
        persist_jobs_count=$(jq '.jobs | length' "$PERSIST_JOBS" 2>/dev/null || echo 0)
        worktree_jobs_count=$(jq '.jobs | length' "$worktree_jobs" 2>/dev/null || echo 0)
        if [[ "$persist_jobs_count" -ge "$worktree_jobs_count" ]]; then
            cp "$PERSIST_JOBS" "$worktree_jobs"
            print_info "Restored aristotle-jobs.json from persistent state ($persist_jobs_count jobs)"
        fi
    elif [[ -f "$PERSIST_JOBS" ]]; then
        mkdir -p "$(dirname "$worktree_jobs")"
        cp "$PERSIST_JOBS" "$worktree_jobs"
        print_info "Restored aristotle-jobs.json from persistent state"
    fi
}

# Create worktree
create_worktree() {
    if [[ -d "$WORKTREE_PATH" ]]; then
        salvage_jobs_file
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

    # Restore jobs file after worktree creation
    restore_jobs_file
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
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would signal Aristotle agent to stop"
        print_info "Would create directory: $SIGNALS_DIR"
        print_info "Would create stop signal: $SIGNALS_DIR/stop-aristotle"
        return
    fi

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
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would stop Aristotle agent"
        print_info "Would kill tmux session if running: $SESSION_NAME"
        print_info "Would remove stop signal: $SIGNALS_DIR/stop-aristotle"
        return
    fi

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
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would attach to tmux session: $SESSION_NAME"
        return
    fi

    if ! is_running; then
        print_error "Agent is not running"
        exit 1
    fi

    print_info "Attaching to $SESSION_NAME (Ctrl+B D to detach)"
    tmux attach -t "$SESSION_NAME"
}

# Tail logs
tail_logs() {
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would tail log file: $LOG_FILE"
        return
    fi

    if [[ ! -f "$LOG_FILE" ]]; then
        print_error "Log file not found: $LOG_FILE"
        exit 1
    fi

    print_info "Tailing logs (Ctrl+C to stop)"
    tail -f "$LOG_FILE"
}

# Launch agent
launch_agent() {
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would launch Aristotle agent"
        print_info "Would check dependencies: tmux, gh, ARISTOTLE_API_KEY or ~/.aristotle_key"
        print_info "Would create directories: $LOGS_DIR, $SIGNALS_DIR"
        print_info "Would remove signal: $SIGNALS_DIR/stop-aristotle"
        print_info "Would update main branch with git checkout main and git pull origin main"
        print_info "Would salvage jobs from: $WORKTREE_PATH/research/aristotle-jobs.json"
        print_info "Would remove existing worktree if present: $WORKTREE_PATH"
        print_info "Would delete branch if present: $BRANCH_NAME"
        print_info "Would create worktree: $WORKTREE_PATH"
        print_info "Would restore jobs from: $PERSIST_JOBS"
        print_info "Would create tmux session: $SESSION_NAME"
        print_info "Would export REPO_ROOT, ARISTOTLE_TARGET, and ARISTOTLE_INTERVAL"
        if [[ -f "$HOME/.aristotle_key" ]]; then
            print_info "Would load ARISTOTLE_API_KEY from ~/.aristotle_key"
        fi
        print_info "Would run: $REPO_ROOT/scripts/aristotle/aristotle-agent.sh --loop --target $TARGET_ACTIVE --interval $INTERVAL_MINUTES"
        print_info "Worktree: $WORKTREE_PATH"
        print_info "Branch: $BRANCH_NAME"
        print_info "Target: $TARGET_ACTIVE active jobs"
        print_info "Interval: $INTERVAL_MINUTES minutes"
        return
    fi

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

    # Launch the deterministic agent script directly (no Claude needed)
    sleep 0.5
    local agent_script="$REPO_ROOT/scripts/aristotle/aristotle-agent.sh"
    tmux send-keys -t "$SESSION_NAME" "$agent_script --loop --target $TARGET_ACTIVE --interval $INTERVAL_MINUTES 2>&1 | tee -a '$LOG_FILE'" Enter

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
case "${ARGS[0]:-}" in
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
        echo "  --dry-run, -n    Preview launch/control actions without writing"
        echo "  --status, -s     Show agent status"
        echo "  --stop           Stop the agent"
        echo "  --dry-run --stop Preview stop without touching tmux or signals"
        echo "  --graceful-stop  Signal graceful stop"
        echo "  --attach, -a     Attach to tmux session"
        echo "  --logs, -l       Tail agent logs"
        echo ""
        echo "Environment:"
        echo "  ARISTOTLE_TARGET   Target active jobs (default: 3)"
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
