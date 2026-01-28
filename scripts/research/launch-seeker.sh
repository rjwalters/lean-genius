#!/bin/bash
#
# launch-seeker.sh - Launch the Seeker agent
#
# The Seeker periodically checks the candidate pool and selects new
# research problems when the pool runs low. It closes the autonomous
# loop by keeping the Researcher pipeline fed with good problems.
#
# Usage:
#   ./launch-seeker.sh              Launch seeker (default 15min interval)
#   ./launch-seeker.sh --stop       Stop the seeker
#   ./launch-seeker.sh --status     Check seeker status
#   ./launch-seeker.sh --attach     Attach to seeker session
#   ./launch-seeker.sh --logs       Tail seeker logs
#   ./launch-seeker.sh --graceful-stop  Signal seeker to stop after current work
#
# Environment:
#   SEEKER_INTERVAL - Interval in minutes between checks (default: 15)
#   SEEKER_THRESHOLD - Minimum available problems before triggering (default: 5)

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
SESSION_NAME="seeker-agent"
LOG_FILE="$LOGS_DIR/seeker.log"
INTERVAL="${SEEKER_INTERVAL:-15}"
THRESHOLD="${SEEKER_THRESHOLD:-5}"
CANDIDATE_POOL="$REPO_ROOT/research/candidate-pool.json"
WORKTREE_PATH="$WORKTREES_DIR/seeker"
BRANCH_NAME="feature/seeker"

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

# Create or update worktree for seeker
create_worktree() {
    mkdir -p "$WORKTREES_DIR"

    if [[ -d "$WORKTREE_PATH" ]]; then
        print_info "Worktree already exists, syncing with main..."
        (
            cd "$WORKTREE_PATH"
            git fetch origin main 2>/dev/null || true
            git stash 2>/dev/null || true

            # Rebase on main to keep branch up to date
            if git rebase origin/main 2>/dev/null; then
                print_success "Rebased on origin/main"
            else
                # Abort rebase and reset if conflicts
                git rebase --abort 2>/dev/null || true
                print_warning "Rebase conflicts - resetting to origin/main"
                git reset --hard origin/main 2>/dev/null || true
            fi

            git stash pop 2>/dev/null || true
        )
        return 0
    fi

    print_info "Creating worktree for seeker at $WORKTREE_PATH..."

    # Try to create worktree
    git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main 2>/dev/null || {
        # Branch might exist, try to use it
        git worktree add "$WORKTREE_PATH" "$BRANCH_NAME" 2>/dev/null || {
            # Remove and recreate branch
            git branch -D "$BRANCH_NAME" 2>/dev/null || true
            git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main
        }
    }

    # Symlink .lake for fast Lean builds (if proofs directory exists)
    if [[ -d "$REPO_ROOT/proofs/.lake" ]] && [[ -d "$WORKTREE_PATH/proofs" ]]; then
        rm -rf "$WORKTREE_PATH/proofs/.lake" 2>/dev/null || true
        ln -s "$REPO_ROOT/proofs/.lake" "$WORKTREE_PATH/proofs/.lake"
        print_info "Linked .lake for fast Lean builds"
    fi

    print_success "Created seeker worktree"
}

# Check if candidate pool needs replenishment
check_pool_depth() {
    if [[ ! -f "$CANDIDATE_POOL" ]]; then
        echo "0"
        return
    fi
    jq '[.candidates[] | select(.status == "available")] | length' "$CANDIDATE_POOL" 2>/dev/null || echo "0"
}

# Create prompt file for seeker
create_prompt_file() {
    local prompt_file="$LOGS_DIR/seeker-prompt.md"

    cat > "$prompt_file" << EOF
# Seeker Agent Instructions

You are the **seeker** agent. Your mission is to keep the research pipeline fed with good problems.

## Environment

- REPO_ROOT: $REPO_ROOT
- INTERVAL: $INTERVAL minutes
- THRESHOLD: $THRESHOLD available problems minimum
- LOG_FILE: $LOG_FILE

## Your Workflow (Repeat Every $INTERVAL Minutes)

1. **Check for stop signal**
   \`\`\`bash
   if [[ -f "$SIGNALS_DIR/stop-seeker" ]] || [[ -f "$SIGNALS_DIR/stop-all" ]]; then
       echo "Stop signal received. Exiting."
       exit 0
   fi
   \`\`\`

2. **Check candidate pool depth**
   \`\`\`bash
   AVAILABLE=\$(jq '[.candidates[] | select(.status == "available")] | length' research/candidate-pool.json)
   echo "Available problems: \$AVAILABLE (threshold: $THRESHOLD)"
   \`\`\`

3. **If pool is low (< $THRESHOLD available), run selection**
   - Use the /seeker skill to select and initialize new problems
   - Run: \`/seeker --refresh\` to extract new problems from gallery
   - Or run: \`/seeker\` to select from existing pool
   - **CRITICAL - Database-first workflow**: When adding new problems, you MUST:
     a. Ensure database exists: \`if [ ! -f research/db/knowledge.db ]; then python3 research/db/migrate.py; fi\`
     b. Insert into database: \`sqlite3 research/db/knowledge.db "INSERT INTO problems ..."\`
     c. Regenerate pool JSON: \`python3 research/db/sync_pool.py\`
     d. Then initialize workspace: \`./.lean/scripts/research.sh init <slug>\`
   - Without steps (a-c), Researchers will NOT see the new problems in candidate-pool.json

4. **If pool is adequate, report status and wait**
   - Run: \`/seeker --status\` to generate a status report
   - Log the report

5. **Wait for next interval**
   \`\`\`bash
   echo "Next check in $INTERVAL minutes..."
   sleep ${INTERVAL}m
   \`\`\`

6. **Repeat from step 1**

## Start Now

Begin by:
1. Reading the seeker role: \`cat $REPO_ROOT/.lean/roles/seeker.md\`
2. Checking pool status
3. If pool is low, selecting problems
4. Starting the periodic check loop

Good luck, seeker!
EOF

    echo "$prompt_file"
}

# Launch the seeker agent
launch_agent() {
    check_deps
    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR"

    # Remove any existing stop signal
    rm -f "$SIGNALS_DIR/stop-seeker"

    # Kill existing session if any
    tmux kill-session -t "$SESSION_NAME" 2>/dev/null || true

    # Create or update worktree
    create_worktree

    # Check pool depth first
    local available
    available=$(check_pool_depth)

    # Create prompt file
    local prompt_file
    prompt_file=$(create_prompt_file)

    print_info "Launching seeker agent..."
    print_info "Interval: $INTERVAL minutes"
    print_info "Threshold: $THRESHOLD available problems"
    print_info "Current available: $available"
    print_info "Worktree: $WORKTREE_PATH"

    if [[ "$available" -lt "$THRESHOLD" ]]; then
        print_warning "Pool is low ($available < $THRESHOLD) - seeker will select problems immediately"
    fi

    # Launch in tmux with resilient wrapper in DAEMON mode
    # Run in worktree to isolate from main repo
    local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
    tmux new-session -d -s "$SESSION_NAME" -c "$WORKTREE_PATH" \
        "ENHANCER_ID=seeker REPO_ROOT=$WORKTREE_PATH $wrapper_script --daemon --prompt 'You are the seeker agent. Read $prompt_file for your instructions, then start the selection loop.' --log '$LOG_FILE'"

    print_success "Launched seeker agent"
    echo ""
    echo "Commands:"
    echo "  ./scripts/research/launch-seeker.sh --status     Check status"
    echo "  ./scripts/research/launch-seeker.sh --attach     Attach to session"
    echo "  ./scripts/research/launch-seeker.sh --logs       Tail logs"
    echo "  ./scripts/research/launch-seeker.sh --stop       Stop agent"
}

# Stop the seeker
stop_agent() {
    print_info "Stopping seeker agent..."

    # Create stop signal for graceful shutdown
    touch "$SIGNALS_DIR/stop-seeker"

    # Give it a moment to notice
    sleep 2

    # Kill the session
    if tmux kill-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Stopped seeker agent"
    else
        print_info "No seeker session found"
    fi

    # Clean up signal
    rm -f "$SIGNALS_DIR/stop-seeker"
}

# Graceful stop (just create signal, don't kill)
graceful_stop_agent() {
    print_info "Sending graceful stop signal to seeker agent..."
    mkdir -p "$SIGNALS_DIR"
    touch "$SIGNALS_DIR/stop-seeker"
    print_success "Stop signal created. Seeker will stop after current work."
}

# Check status
check_status() {
    echo "=== Seeker Status ==="
    echo ""

    if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Seeker is running"
        echo ""
        echo "Session: $SESSION_NAME"
        echo "Worktree: $WORKTREE_PATH"
        echo "Log file: $LOG_FILE"
        echo "Interval: $INTERVAL minutes"
        echo "Threshold: $THRESHOLD available problems"

        # Show worktree git status
        if [[ -d "$WORKTREE_PATH" ]]; then
            local branch
            branch=$(cd "$WORKTREE_PATH" && git branch --show-current 2>/dev/null || echo "unknown")
            echo "Branch: $branch"
        fi

        local available
        available=$(check_pool_depth)
        echo "Available problems: $available"

        if [[ "$available" -lt "$THRESHOLD" ]]; then
            print_warning "Pool is low - seeker should be selecting"
        else
            echo "Pool depth: adequate"
        fi

        if [[ -f "$LOG_FILE" ]]; then
            echo ""
            echo "Recent activity:"
            tail -5 "$LOG_FILE" 2>/dev/null || echo "  (no logs yet)"
        fi
    else
        print_info "Seeker is not running"
        echo ""
        if [[ -d "$WORKTREE_PATH" ]]; then
            echo "Worktree exists: $WORKTREE_PATH"
        fi
        local available
        available=$(check_pool_depth)
        echo "Available problems: $available"
        if [[ "$available" -lt "$THRESHOLD" ]]; then
            print_warning "Pool is low ($available < $THRESHOLD) - consider starting seeker"
        fi
    fi
}

# Attach to session
attach_session() {
    if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_error "No seeker session found"
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
Seeker Agent Launcher

Launches an autonomous agent that periodically checks the candidate pool
and selects new research problems when the pool runs low.

The agent runs in an isolated git worktree at $WORKTREES_DIR/seeker
to prevent contention with other agents working in the main repository.

Usage:
  ./launch-seeker.sh              Launch seeker (default 15min interval)
  ./launch-seeker.sh --stop       Stop the seeker
  ./launch-seeker.sh --graceful-stop  Signal seeker to stop
  ./launch-seeker.sh --status     Check seeker status
  ./launch-seeker.sh --attach     Attach to seeker session
  ./launch-seeker.sh --logs       Tail seeker logs
  ./launch-seeker.sh --help       Show this help

Environment Variables:
  SEEKER_INTERVAL    Interval in minutes between checks (default: 15)
  SEEKER_THRESHOLD   Minimum available problems before triggering (default: 5)

Examples:
  ./launch-seeker.sh                         # Start with defaults
  SEEKER_INTERVAL=5 ./launch-seeker.sh       # Check every 5 minutes
  SEEKER_THRESHOLD=3 ./launch-seeker.sh      # Trigger at 3 available
  ./launch-seeker.sh --attach                # Watch the agent work
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
