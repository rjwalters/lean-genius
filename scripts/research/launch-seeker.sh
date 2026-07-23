#!/bin/bash
#
# launch-seeker.sh - Launch the Seeker agent
#
# The Seeker periodically checks the candidate pool and selects new
# research problems when the pool runs low. It closes the autonomous
# loop by keeping the Researcher pipeline fed with good problems.
#
# Usage:
#   ./launch-seeker.sh              Launch seeker (default 30min interval)
#   ./launch-seeker.sh --dry-run    Preview launch without starting tmux
#   ./launch-seeker.sh --stop       Stop the seeker
#   ./launch-seeker.sh --status     Check seeker status
#   ./launch-seeker.sh --attach     Attach to seeker session
#   ./launch-seeker.sh --logs       Tail seeker logs
#   ./launch-seeker.sh --graceful-stop  Signal seeker to stop after current work
#
# Environment:
#   SEEKER_INTERVAL - Interval in minutes between checks (default: 30)
#   SEEKER_THRESHOLD - Minimum available problems before triggering (default: 15)

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
# Resolved worktree base (LOOM_WORKTREE_ROOT env var / .loom/config.json
# worktree.root override; default $REPO_ROOT/.loom/worktrees).
# shellcheck source=../lib/worktree-root.sh
source "$REPO_ROOT/scripts/lib/worktree-root.sh"
# Shared branch-reclaim + fatal-logging helpers (reclaim_branch_worktree,
# log_worktree_fatal) so a stale/locked worktree holding feature/seeker can't
# silently kill this backgrounded launcher (issue #39649).
# shellcheck source=../lib/worktree-cleanup.sh
source "$REPO_ROOT/scripts/lib/worktree-cleanup.sh"
WORKTREES_DIR="$(loom_worktree_root "$REPO_ROOT")"
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
SESSION_NAME="seeker-agent"
LOG_FILE="$LOGS_DIR/seeker.log"
INTERVAL="${SEEKER_INTERVAL:-30}"
THRESHOLD="${SEEKER_THRESHOLD:-15}"
CANDIDATE_POOL="$REPO_ROOT/.lean/state/candidate-pool.json"
WORKTREE_PATH="$WORKTREES_DIR/seeker"
BRANCH_NAME="feature/seeker"
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

    # Free the branch if a stale/locked/legacy worktree still holds it at another
    # path (e.g. left by the /Volumes/Stripe migration); otherwise every add
    # below fails and this backgrounded launcher dies silently (issue #39649).
    reclaim_branch_worktree "$BRANCH_NAME" "$WORKTREE_PATH" || \
        log_worktree_fatal "$LOG_FILE" "could not reclaim '$BRANCH_NAME' from a stale worktree (see 'git worktree list')"

    # Try to create worktree. The final attempt must NOT die silently under
    # `set -e` (backgrounded launcher, invisible non-zero exit — issue #39649).
    git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main 2>/dev/null || {
        # Branch might exist, try to use it
        git worktree add "$WORKTREE_PATH" "$BRANCH_NAME" 2>/dev/null || {
            # Remove and recreate branch
            git branch -D "$BRANCH_NAME" 2>/dev/null || true
            git worktree add "$WORKTREE_PATH" -b "$BRANCH_NAME" main 2>/dev/null || \
                log_worktree_fatal "$LOG_FILE" "worktree setup failed for '$BRANCH_NAME' at $WORKTREE_PATH (branch may be checked out elsewhere; see 'git worktree list')"
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

2. **Refresh candidate pool** (picks up newly enriched gallery proofs)
   \`\`\`bash
   # NOTE: --json mode writes .lean/research/problems.json itself. Do NOT add a
   # shell redirect (> .lean/research/problems.json) — it clobbers the file the
   # script writes, interleaving stdout progress lines into the JSON and
   # corrupting the reservoir. (Caused 100+ no-op replenish cycles.)
   npx tsx .lean/scripts/extract-problems.ts --json 2>/dev/null
   # Reconcile finished problems INTO the DB before regenerating the pool.
   # sync_pool.py treats knowledge.db as the source of truth, but nothing else
   # propagates completion back into it, so problems marked graduated/blocked in
   # the git-tracked registry keep their servable DB status and get re-served
   # forever (140 such rows on 2026-07-19). This one-way reconcile only moves a
   # servable row to a terminal status; it never resurrects a finished problem.
   python3 scripts/research/sync-db-status-from-registry.py 2>/dev/null
   # sync_pool.py writes directly to the consumed pool at
   # .lean/state/candidate-pool.json (see #26802). No copy step is needed.
   python3 research/db/sync_pool.py 2>/dev/null
   \`\`\`

2b. **Ingest GitHub research issues** (ADDITIONAL source — issue #41840)
   Human-filed research problems tagged \`research:queued\` are explicit
   requests, so they are ingested EVERY cycle regardless of pool depth (the
   gallery-derived replenishment below stays threshold-gated). This inserts each
   new such issue into the DB, writes its site JSON, regenerates the pool, and
   marks the issue \`research:pooled\` so it is never ingested twice.
   \`\`\`bash
   # Idempotent: skips issues already carrying research:pooled or already in the
   # DB. Re-runs sync_pool.py internally, so run it AFTER the refresh above.
   ./scripts/research/ingest-issue-problems.sh 2>&1 | tee -a "$LOG_FILE"
   \`\`\`

3. **Check candidate pool depth**
   \`\`\`bash
   AVAILABLE=\$(jq '[.candidates[] | select(.status == "available")] | length' .lean/state/candidate-pool.json)
   echo "Available problems: \$AVAILABLE (threshold: $THRESHOLD)"
   \`\`\`

4. **If pool is low (< $THRESHOLD available), run selection**
   - Use the /seeker skill to select and initialize new problems
   - Run: \`/seeker --refresh\` to extract new problems from gallery
   - Or run: \`/seeker\` to select from existing pool
   - **CRITICAL - Database-first workflow**: When adding new problems, you MUST:
     a. Ensure database exists: \`if [ ! -f research/db/knowledge.db ]; then python3 research/db/migrate.py; fi\`
     b. Insert into database: \`sqlite3 research/db/knowledge.db "INSERT INTO problems ..."\`
     c. Regenerate pool JSON: \`python3 research/db/sync_pool.py\` (writes .lean/state/candidate-pool.json directly)
     d. Then initialize workspace: \`./.lean/scripts/research.sh init <slug>\`
     e. Fill in \`research/problems/<slug>/problem.md\` and any matching site JSON
     f. Validate the filled stub: \`npx tsx scripts/research/validate-seeker-stubs.ts <slug>\`
   - Without steps (a-c), Researchers will NOT see the new problems in the consumed .lean/state/candidate-pool.json
   - Without step (f), unfilled template placeholders may leak into the public gallery
   - **After each problem is selected**, create a completion signal for stats tracking:
     \`\`\`bash
     npx tsx scripts/research/validate-seeker-stubs.ts <slug>
     $REPO_ROOT/scripts/lean/update-stats.sh problem-selected
     \`\`\`

5. **If pool is adequate, report status and wait**
   - Run: \`/seeker --status\` to generate a status report
   - Log the report

6. **Wait for next interval**
   \`\`\`bash
   echo "Next check in $INTERVAL minutes..."
   sleep ${INTERVAL}m
   \`\`\`

7. **Repeat from step 1**

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
    if [[ "$DRY_RUN" == "true" ]]; then
        local available
        available=$(check_pool_depth)

        print_info "Dry run: would launch seeker agent"
        print_info "Would check dependencies: tmux, claude, jq"
        print_info "Would create directories: $LOGS_DIR, $SIGNALS_DIR"
        print_info "Would remove signal: $SIGNALS_DIR/stop-seeker"
        print_info "Would replace tmux session: $SESSION_NAME"
        print_info "Would create or update worktree: $WORKTREE_PATH"
        print_info "Would create prompt file under: $LOGS_DIR"
        print_info "Would launch claude wrapper in daemon mode"
        print_info "Interval: $INTERVAL minutes"
        print_info "Threshold: $THRESHOLD available problems"
        print_info "Current available: $available"
        if [[ "$available" -lt "$THRESHOLD" ]]; then
            print_warning "Pool is low ($available < $THRESHOLD) - seeker would select problems immediately"
        fi
        return
    fi

    check_deps
    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR"

    # Remove any existing stop signal
    rm -f "$SIGNALS_DIR/stop-seeker"

    # Kill existing session if any
    tmux kill-session -t "$SESSION_NAME" 2>/dev/null || true

    # Create or update worktree
    create_worktree

    # Symlink OAuth tokens so the claude-wrapper can find them in the worktree.
    # Guard against self-pointing symlinks: the seeker operates from the MAIN
    # checkout, so WORKTREE_PATH == REPO_ROOT and dst == src. A bare `ln -sfn`
    # would then replace main's real tokens dir with a circular self-reference
    # (.loom/tokens -> .../.loom/tokens), flapping the pool every cycle (#41551).
    # Mirror the guard used by deploy/auditor/mechanic launchers.
    if [[ -d "$REPO_ROOT/.loom/tokens" ]]; then
        local src="$REPO_ROOT/.loom/tokens"
        local dst="$WORKTREE_PATH/.loom/tokens"
        local src_real dst_real
        src_real="$(cd "$src" 2>/dev/null && pwd -P)"
        dst_real="$(dirname "$dst")"; dst_real="$(cd "$dst_real" 2>/dev/null && pwd -P)/$(basename "$dst")"
        if [[ -z "$src_real" ]]; then
            print_warning "Skipping tokens symlink: $src is not a resolvable directory (broken symlink?)."
        elif [[ "$src_real" == "$dst_real" ]]; then
            print_warning "Refusing to create self-pointing tokens symlink ($dst → $src). Skipping."
        else
            mkdir -p "$WORKTREE_PATH/.loom" 2>/dev/null || true
            ln -sfn "$src_real" "$dst"
            print_info "Linked .loom/tokens for OAuth token rotation"
        fi
    fi

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
    # Run in worktree to isolate from main repo.
    # Per-role override: SEEKER_CLAUDE_MODEL > CLAUDE_MODEL > wrapper default.
    local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
    local seeker_model="${SEEKER_CLAUDE_MODEL:-${CLAUDE_MODEL:-claude-opus-4-8}}"
    # Enforce the check interval as a floor between cycles. Seeker usually finds
    # the pool adequate and stands down in under a minute; without a floor the
    # wrapper busy-loops and re-invokes Claude every ~40s-1m instead of every
    # INTERVAL minutes, burning quota on no-op cycles (same fix as herald; see
    # scripts/herald/launch-agent.sh).
    local cycle_min_seconds=$((INTERVAL * 60))
    tmux new-session -d -s "$SESSION_NAME" -c "$WORKTREE_PATH" \
        "ENHANCER_ID=seeker REPO_ROOT=$WORKTREE_PATH CLAUDE_MODEL=$seeker_model CYCLE_MIN_SECONDS=$cycle_min_seconds $wrapper_script --daemon --prompt 'You are the seeker agent. Read $prompt_file for your instructions, then start the selection loop.' --log '$LOG_FILE'"

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
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would stop seeker agent"
        print_info "Would create stop signal: $SIGNALS_DIR/stop-seeker"
        print_info "Would wait 2 seconds for graceful shutdown"
        print_info "Would kill tmux session: $SESSION_NAME"
        print_info "Would remove stop signal: $SIGNALS_DIR/stop-seeker"
        return
    fi

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
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would create stop signal: $SIGNALS_DIR/stop-seeker"
        return
    fi

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
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would attach to tmux session: $SESSION_NAME"
        return
    fi

    if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_error "No seeker session found"
        exit 1
    fi

    tmux attach-session -t "$SESSION_NAME"
}

# Tail logs
tail_logs() {
    if [[ "$DRY_RUN" == "true" ]]; then
        print_info "Dry run: would tail log file: $LOG_FILE"
        return
    fi

    if [[ ! -f "$LOG_FILE" ]]; then
        print_error "No log file found: $LOG_FILE"
        exit 1
    fi

    tail -f "$LOG_FILE"
}

# Main command dispatch
case "${ARGS[0]:-}" in
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
  ./launch-seeker.sh              Launch seeker (default 30min interval)
  ./launch-seeker.sh --dry-run    Preview launch without starting tmux
  ./launch-seeker.sh --stop       Stop the seeker
  ./launch-seeker.sh --dry-run --stop  Preview stop without touching signals
  ./launch-seeker.sh --graceful-stop  Signal seeker to stop
  ./launch-seeker.sh --status     Check seeker status
  ./launch-seeker.sh --attach     Attach to seeker session
  ./launch-seeker.sh --logs       Tail seeker logs
  ./launch-seeker.sh --help       Show this help

Environment Variables:
  SEEKER_INTERVAL    Interval in minutes between checks (default: 30)
  SEEKER_THRESHOLD   Minimum available problems before triggering (default: 15)

Examples:
  ./launch-seeker.sh                         # Start with defaults
  ./launch-seeker.sh --dry-run               # Preview launch
  SEEKER_INTERVAL=5 ./launch-seeker.sh       # Check every 5 minutes
  SEEKER_THRESHOLD=3 ./launch-seeker.sh      # Trigger at 3 available
  ./launch-seeker.sh --attach                # Watch the agent work
EOF
        ;;
    "")
        launch_agent
        ;;
    *)
        print_error "Unknown option: ${ARGS[0]}"
        echo "Run '$0 --help' for usage"
        exit 1
        ;;
esac
