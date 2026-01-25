#!/bin/bash
#
# launch-agent.sh - Launch the deployer agent
#
# Usage:
#   ./launch-agent.sh              Launch deployer (default 30min interval)
#   ./launch-agent.sh --stop       Stop the deployer
#   ./launch-agent.sh --status     Check deployer status
#   ./launch-agent.sh --attach     Attach to deployer session
#   ./launch-agent.sh --logs       Tail deployer logs
#
# Environment:
#   DEPLOYER_INTERVAL - Interval in minutes between deploys (default: 30)

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
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
SESSION_NAME="deployer"
LOG_FILE="$LOGS_DIR/deployer.log"
INTERVAL="${DEPLOYER_INTERVAL:-30}"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

print_error() { echo -e "${RED}✗ $1${NC}"; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_info() { echo -e "${BLUE}ℹ $1${NC}"; }

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

# Create prompt file for deployer
create_prompt_file() {
    local prompt_file="$LOGS_DIR/deployer-prompt.md"

    cat > "$prompt_file" << EOF
# Deployer Agent Instructions

You are the **deployer** agent. Your mission is to keep the website current.

## Environment

- REPO_ROOT: $REPO_ROOT
- INTERVAL: $INTERVAL minutes
- LOG_FILE: $LOG_FILE

## Your Workflow (Repeat Every $INTERVAL Minutes)

1. **Check for stop signal**
   \`\`\`bash
   if [[ -f "$SIGNALS_DIR/stop-deployer" ]] || [[ -f "$SIGNALS_DIR/stop-all" ]]; then
       echo "Stop signal received. Exiting."
       exit 0
   fi
   \`\`\`

2. **Run the deploy pipeline**
   \`\`\`bash
   ./scripts/deploy/sync-and-deploy.sh
   \`\`\`

3. **Report results**
   - PRs merged
   - Any failures
   - Deployment URL

4. **Wait for next interval**
   \`\`\`bash
   echo "Next deploy in $INTERVAL minutes..."
   sleep ${INTERVAL}m
   \`\`\`

5. **Repeat from step 1**

## Start Now

Begin by:
1. Reading the deployer role: \`cat $REPO_ROOT/.loom/roles/deployer.md\`
2. Running your first deploy cycle
3. Continuing the loop

Good luck, deployer!
EOF

    echo "$prompt_file"
}

# Launch the deployer agent
launch_agent() {
    check_deps
    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR"

    # Remove any existing stop signal
    rm -f "$SIGNALS_DIR/stop-deployer"

    # Kill existing session if any
    tmux kill-session -t "$SESSION_NAME" 2>/dev/null || true

    # Create prompt file
    local prompt_file
    prompt_file=$(create_prompt_file)

    print_info "Launching deployer agent..."
    print_info "Interval: $INTERVAL minutes"

    # Launch in tmux with resilient wrapper in DAEMON mode for infinite retry
    # The --daemon flag ensures the deployer survives API outages indefinitely
    local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
    tmux new-session -d -s "$SESSION_NAME" -c "$REPO_ROOT" \
        "ENHANCER_ID=deployer REPO_ROOT=$REPO_ROOT $wrapper_script --daemon --prompt 'You are the deployer agent. Read $prompt_file for your instructions, then start the deploy loop.' --log '$LOG_FILE'"

    print_success "Launched deployer agent"
    echo ""
    echo "Commands:"
    echo "  ./scripts/deploy/launch-agent.sh --status     Check status"
    echo "  ./scripts/deploy/launch-agent.sh --attach     Attach to session"
    echo "  ./scripts/deploy/launch-agent.sh --logs       Tail logs"
    echo "  ./scripts/deploy/launch-agent.sh --stop       Stop agent"
}

# Stop the deployer
stop_agent() {
    print_info "Stopping deployer agent..."

    # Create stop signal for graceful shutdown
    touch "$SIGNALS_DIR/stop-deployer"

    # Give it a moment to notice
    sleep 2

    # Kill the session
    if tmux kill-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Stopped deployer agent"
    else
        print_info "No deployer session found"
    fi

    # Clean up signal
    rm -f "$SIGNALS_DIR/stop-deployer"
}

# Check status
check_status() {
    echo "=== Deployer Status ==="
    echo ""

    if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Deployer is running"
        echo ""
        echo "Session: $SESSION_NAME"
        echo "Log file: $LOG_FILE"

        if [[ -f "$LOG_FILE" ]]; then
            echo ""
            echo "Recent activity:"
            tail -5 "$LOG_FILE" 2>/dev/null || echo "  (no logs yet)"
        fi
    else
        print_info "Deployer is not running"
    fi

    echo ""
    echo "Open PRs: $(gh pr list --json number 2>/dev/null | jq 'length' || echo 'unknown')"
}

# Attach to session
attach_session() {
    if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_error "No deployer session found"
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
Deployer Agent Launcher

Launches an autonomous agent that periodically merges PRs, syncs data,
builds, and deploys the website to Cloudflare.

Usage:
  ./launch-agent.sh              Launch deployer (default 30min interval)
  ./launch-agent.sh --stop       Stop the deployer
  ./launch-agent.sh --status     Check deployer status
  ./launch-agent.sh --attach     Attach to deployer session
  ./launch-agent.sh --logs       Tail deployer logs
  ./launch-agent.sh --help       Show this help

Environment Variables:
  DEPLOYER_INTERVAL   Interval in minutes between deploys (default: 30)

Examples:
  ./launch-agent.sh                        # Start with 30min interval
  DEPLOYER_INTERVAL=15 ./launch-agent.sh   # Start with 15min interval
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
