#!/bin/bash
#
# launch-agent.sh - Launch the Herald agent
#
# The Herald periodically scans for noteworthy results and posts highlights
# to Mathstodon (@rjwalters@mathstodon.xyz). Read-only agent, no worktree needed.
#
# Usage:
#   ./launch-agent.sh              Launch herald (default 6h interval)
#   ./launch-agent.sh --stop       Stop the herald
#   ./launch-agent.sh --status     Check herald status
#   ./launch-agent.sh --attach     Attach to herald session
#   ./launch-agent.sh --logs       Tail herald logs
#   ./launch-agent.sh --graceful-stop  Signal herald to stop after current work
#
# Environment:
#   HERALD_INTERVAL - Interval in minutes between scans (default: 360 = 6 hours)

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
LOGS_DIR="$REPO_ROOT/.loom/logs"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
STATE_DIR="$REPO_ROOT/.loom/state"
SESSION_NAME="herald-agent"
LOG_FILE="$LOGS_DIR/herald.log"
INTERVAL="${HERALD_INTERVAL:-360}"
STATE_FILE="$STATE_DIR/herald-posts.json"

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
    command -v curl >/dev/null 2>&1 || missing+=("curl")

    if [[ ${#missing[@]} -gt 0 ]]; then
        print_error "Missing dependencies: ${missing[*]}"
        exit 1
    fi

    # Validate token
    if [[ -f "$REPO_ROOT/.env" ]]; then
        if ! grep -q '^MATHSTODON_TOKEN=' "$REPO_ROOT/.env"; then
            print_error "MATHSTODON_TOKEN not found in .env"
            exit 1
        fi
    else
        print_error ".env file not found"
        exit 1
    fi
}

# Initialize state file if needed
init_state() {
    mkdir -p "$STATE_DIR"
    if [[ ! -f "$STATE_FILE" ]]; then
        echo '{"posts": [], "daily_counts": {}}' > "$STATE_FILE"
        print_info "Created herald state file: $STATE_FILE"
    fi
}

# Create prompt file for herald
create_prompt_file() {
    local prompt_file="$LOGS_DIR/herald-prompt.md"

    cat > "$prompt_file" << 'PROMPT_EOF'
# Herald Agent Instructions

You are the **herald** agent for Lean Genius. Your mission is to post noteworthy mathematical achievements to Mathstodon (@rjwalters@mathstodon.xyz).

## Environment

- REPO_ROOT: ${REPO_ROOT}
- INTERVAL: ${INTERVAL} minutes (${INTERVAL_HOURS} hours)
- STATE_FILE: ${STATE_FILE}
- LOG_FILE: ${LOG_FILE}
- POST_SCRIPT: ${REPO_ROOT}/scripts/herald/post-mathstodon.sh

## Posting Tool

All posting goes through `post-mathstodon.sh`. The script handles:
- Posting to the Mastodon API
- Updating state file (post history + daily counts) automatically
- Rate limit enforcement (max 4 posts/day)
- Dedup checking (blocks posts with previously-used subject keys)
- Appending `[automated post]` tag when `--automated` is set

**You do NOT need to manually update the state file.** The script does it for you.

### Usage
```bash
# Always use --automated (you are an automated agent)
# Always provide --subject for dedup tracking
# Provide --arc when the post belongs to a narrative arc
${REPO_ROOT}/scripts/herald/post-mathstodon.sh \
    --automated \
    --subject "SUBJECT_KEY" \
    --arc "ARC_NAME" \
    "POST_TEXT"

# Dry run first if unsure
${REPO_ROOT}/scripts/herald/post-mathstodon.sh \
    --dry-run \
    --subject "SUBJECT_KEY" \
    "POST_TEXT"

# Check rate limit and recent history
${REPO_ROOT}/scripts/herald/post-mathstodon.sh --status
```

## Your Workflow (Repeat Every Cycle)

### 1. Check for stop signal
```bash
if [[ -f "${SIGNALS_DIR}/stop-herald" ]] || [[ -f "${SIGNALS_DIR}/stop-all" ]]; then
    echo "Stop signal received. Exiting."
    exit 0
fi
```

### 2. Read your role definition
```bash
cat ${REPO_ROOT}/.lean/roles/herald.md
```

### 3. Check rate limit and post history
```bash
${REPO_ROOT}/scripts/herald/post-mathstodon.sh --status
```
If daily rate limit is reached, skip to sleep.

### 4. Load recent post subjects (for choosing new topics)
```bash
jq -r '.posts[-10:][].subject' ${STATE_FILE} 2>/dev/null || echo "(no history)"
```

### 5. Scan for noteworthy results

Check these sources for significant events since last scan:

**Git log** (research PRs merged recently):
```bash
git log --oneline --since="7 hours ago" --grep="Research:" --grep="Proof:" --grep="axiom" --grep="sorry" | head -20
```

**Action logs** (enricher/researcher completions):
```bash
ls -lt ${REPO_ROOT}/.loom/signals/completions/ 2>/dev/null | head -10
```

**Proof files** (check for zero-sorry, zero-axiom proofs):
```bash
# Find recently modified proof files
find ${REPO_ROOT}/proofs/Proofs -name "*.lean" -mmin -420 -type f 2>/dev/null | head -10
# For each, check sorry/axiom count
```

**Gallery meta.json** (check for quality scores, new entries):
```bash
# Recently updated gallery entries
find ${REPO_ROOT}/src/data/proofs -name "meta.json" -mmin -420 -type f 2>/dev/null | head -10
```

### 6. Assess significance

Apply the criteria from your role definition (herald.md):
- **Tier 1 (always post)**: Full proof completion (0 axioms, 0 sorries), Freek 100 entry, soundness catch
- **Tier 2 (if notable)**: Major axiom elimination (N→0), named theorem formalization
- **Tier 3 (weekly max)**: Cumulative stats roundup

Skip if nothing meets the threshold.

### 7. Verify the proof page is deployed (MANDATORY)

Before composing any post that links to a proof page (leangenius.org/proof/<slug>), you MUST verify the proof data is complete. For each proof slug you plan to link:

```bash
# All four checks must pass:
# 1. meta.json exists
test -f ${REPO_ROOT}/src/data/proofs/<slug>/meta.json

# 2. leanFile has lineCount > 0
jq '(.leanFile | type) == "object" and (.leanFile.lineCount > 0)' ${REPO_ROOT}/src/data/proofs/<slug>/meta.json

# 3. Proof is in listings.json
jq --arg s "<slug>" '[.[] | select(.slug == $s)] | length' ${REPO_ROOT}/src/data/proofs/listings.json

# 4. Lean source file exists
ls ${REPO_ROOT}/proofs/Proofs/*.lean | grep -i "<name>"
```

If ANY check fails, do NOT post about that proof. The post-mathstodon.sh script also enforces this as a hard gate, but you should check first to avoid wasting a dry-run cycle.

**Why this matters**: The site is an SPA, so any route returns HTML. A proof page can appear to exist but show "coming soon" if the data is incomplete or was not included in the last deploy.

### 8. Compose and post

If a significant result is found:

a. Compose a post (max 500 chars). Follow the style guide in herald.md.
   Choose a unique SUBJECT_KEY (e.g., "theorem-name-milestone-type").
   Choose an ARC_NAME if it fits a narrative arc (e.g., "szemeredi-pipeline", "number-theory").

b. Dry-run first to verify:
```bash
${REPO_ROOT}/scripts/herald/post-mathstodon.sh \
    --dry-run \
    --automated \
    --subject "SUBJECT_KEY" \
    --arc "ARC_NAME" \
    "POST_TEXT"
```

c. If dry-run looks good, post it (dedup + rate limit + state update all handled automatically):
```bash
${REPO_ROOT}/scripts/herald/post-mathstodon.sh \
    --automated \
    --subject "SUBJECT_KEY" \
    --arc "ARC_NAME" \
    "POST_TEXT"
```

The script will:
- Block the post if the subject was already posted (dedup)
- Block the post if the daily rate limit (4/day) is reached
- Post to Mastodon API
- Update the state file with the post record and daily count
- Append `[automated post]` tag to the text

### 9. Scan for engagement opportunities

After posting (or if nothing to post), scan for community engagement:

```bash
# Scan hashtag timelines for posts mentioning Lean/formal math
npx tsx ${REPO_ROOT}/scripts/herald/scan-engagement.ts --json
```

This returns a JSON list of candidate posts from #LeanProver, #FormalMath, #Lean4, and #ProofAssistants that mention Lean.

**Engagement rules:**
- Max 3 replies per cycle
- Only reply to posts that are substantively about Lean/formal math
- Use the TS client directly for replies:
  ```bash
  npx tsx ${REPO_ROOT}/scripts/herald/mastodon-client.ts reply <parent-id> "Reply text"
  ```
- Be helpful and collegial — share relevant links to our gallery when appropriate
- Never self-promote aggressively; only link our proofs when genuinely relevant
- Boost posts that showcase interesting formal math work by others
- Skip posts that are just tangentially mentioning Lean

After replying, the engagement state file tracks replied-to IDs to prevent duplicate replies.

### 10. Sleep until next cycle
```bash
echo "Next scan in ${INTERVAL} minutes..."
sleep ${INTERVAL}m
```

### 11. Repeat from step 1

## Important Rules

- **Max 1 post per cycle, max 4 posts per day**
- **Max 3 replies per engagement scan** (replies also count toward daily post limit)
- **Never post about**: build fixes, data syncs, enrichment batches, axiom decomposition
- **Always use --subject** for every post (enables dedup)
- **Always use --automated** (you are an automated agent)
- Posts must be ≤500 characters (the [automated post] tag is added by the script and counts toward the limit)
- Use --dry-run first if unsure about a post
- Do NOT manually edit the state file — the posting script manages it

Good luck, herald!
PROMPT_EOF

    # Now do variable substitution (the prompt uses ${VAR} placeholders)
    local interval_hours=$((INTERVAL / 60))
    sed -i '' \
        -e "s|\${REPO_ROOT}|$REPO_ROOT|g" \
        -e "s|\${INTERVAL}|$INTERVAL|g" \
        -e "s|\${INTERVAL_HOURS}|$interval_hours|g" \
        -e "s|\${STATE_FILE}|$STATE_FILE|g" \
        -e "s|\${LOG_FILE}|$LOG_FILE|g" \
        -e "s|\${SIGNALS_DIR}|$SIGNALS_DIR|g" \
        "$prompt_file"

    echo "$prompt_file"
}

# Launch the herald agent
launch_agent() {
    check_deps
    mkdir -p "$LOGS_DIR" "$SIGNALS_DIR" "$STATE_DIR"

    # Remove any existing stop signal
    rm -f "$SIGNALS_DIR/stop-herald"

    # Kill existing session if any
    tmux kill-session -t "$SESSION_NAME" 2>/dev/null || true

    # Initialize state
    init_state

    # Create prompt file
    local prompt_file
    prompt_file=$(create_prompt_file)

    local interval_hours=$((INTERVAL / 60))

    print_info "Launching herald agent..."
    print_info "Interval: ${INTERVAL}m (${interval_hours}h)"
    print_info "State: $STATE_FILE"

    # Launch in tmux — no worktree needed (read-only agent).
    # Pin standard-context Opus 4.7: herald's prompt + state file can trigger 1M
    # auto-selection, which fails on accounts without the 1M-context entitlement.
    local wrapper_script="$REPO_ROOT/scripts/agents/claude-wrapper.sh"
    local herald_model="${HERALD_CLAUDE_MODEL:-claude-opus-4-7}"
    tmux new-session -d -s "$SESSION_NAME" -c "$REPO_ROOT" \
        "ENHANCER_ID=herald REPO_ROOT=$REPO_ROOT CLAUDE_MODEL=$herald_model $wrapper_script --daemon --prompt 'You are the herald agent. Read $prompt_file for your instructions, then start the scan loop.' --log '$LOG_FILE'"

    print_success "Launched herald agent"
    echo ""
    echo "Commands:"
    echo "  ./scripts/herald/launch-agent.sh --status     Check status"
    echo "  ./scripts/herald/launch-agent.sh --attach     Attach to session"
    echo "  ./scripts/herald/launch-agent.sh --logs       Tail logs"
    echo "  ./scripts/herald/launch-agent.sh --stop       Stop agent"
}

# Stop the herald
stop_agent() {
    print_info "Stopping herald agent..."

    # Create stop signal for graceful shutdown
    touch "$SIGNALS_DIR/stop-herald"

    # Give it a moment to notice
    sleep 2

    # Kill the session
    if tmux kill-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Stopped herald agent"
    else
        print_info "No herald session found"
    fi

    # Clean up signal
    rm -f "$SIGNALS_DIR/stop-herald"
}

# Graceful stop (just create signal, don't kill)
graceful_stop_agent() {
    print_info "Sending graceful stop signal to herald agent..."
    mkdir -p "$SIGNALS_DIR"
    touch "$SIGNALS_DIR/stop-herald"
    print_success "Stop signal created. Herald will stop after current work."
}

# Check status
check_status() {
    echo "=== Herald Status ==="
    echo ""

    if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_success "Herald is running"
        echo ""
        echo "Session: $SESSION_NAME"
        echo "Log file: $LOG_FILE"
        echo "Interval: $INTERVAL minutes"

        if [[ -f "$STATE_FILE" ]]; then
            local total_posts
            total_posts=$(jq '.posts | length' "$STATE_FILE" 2>/dev/null || echo "0")
            local today
            today=$(date -u +%Y-%m-%d)
            local today_posts
            today_posts=$(jq -r --arg d "$today" '.daily_counts[$d] // 0' "$STATE_FILE" 2>/dev/null || echo "0")
            echo "Total posts: $total_posts"
            echo "Posts today: $today_posts / 4"

            if [[ "$total_posts" -gt 0 ]]; then
                echo ""
                echo "Last post:"
                jq -r '.posts[-1] | "  \(.posted_at): \(.text[0:80])..."' "$STATE_FILE" 2>/dev/null || true
            fi
        fi

        if [[ -f "$LOG_FILE" ]]; then
            echo ""
            echo "Recent activity:"
            tail -5 "$LOG_FILE" 2>/dev/null || echo "  (no logs yet)"
        fi
    else
        print_info "Herald is not running"
        echo ""
        if [[ -f "$STATE_FILE" ]]; then
            local total_posts
            total_posts=$(jq '.posts | length' "$STATE_FILE" 2>/dev/null || echo "0")
            echo "Total posts: $total_posts"
        fi
    fi
}

# Attach to session
attach_session() {
    if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
        print_error "No herald session found"
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
Herald Agent Launcher

Launches an autonomous agent that periodically scans for noteworthy
mathematical results and posts highlights to Mathstodon.

The agent runs in the main repo (read-only, no worktree needed).

Usage:
  ./launch-agent.sh              Launch herald (default 6h interval)
  ./launch-agent.sh --stop       Stop the herald
  ./launch-agent.sh --graceful-stop  Signal herald to stop
  ./launch-agent.sh --status     Check herald status
  ./launch-agent.sh --attach     Attach to herald session
  ./launch-agent.sh --logs       Tail herald logs
  ./launch-agent.sh --help       Show this help

Environment Variables:
  HERALD_INTERVAL    Interval in minutes between scans (default: 360 = 6 hours)

Examples:
  ./launch-agent.sh                        # Start with defaults (6h cycle)
  HERALD_INTERVAL=60 ./launch-agent.sh     # Scan every hour
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
