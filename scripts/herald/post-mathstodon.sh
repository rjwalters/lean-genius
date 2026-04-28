#!/usr/bin/env bash
#
# post-mathstodon.sh - Single source of truth for all Mathstodon posting
#
# Posts to Mastodon API, updates state file, enforces rate limits, and dedup.
# Used by both manual posts and the Herald agent.
#
# Usage:
#   ./post-mathstodon.sh "Post text here"
#   ./post-mathstodon.sh --subject "key" --arc "name" "Post text"
#   ./post-mathstodon.sh --automated --subject "key" --arc "name" "Post text"
#   ./post-mathstodon.sh --dry-run --subject "key" "Test post"
#   ./post-mathstodon.sh --status
#
# Environment:
#   MATHSTODON_TOKEN - API access token (read from .env if not set)
#

set -euo pipefail

# Config
MASTODON_INSTANCE="https://mathstodon.xyz"
MAX_CHARS=500
MAX_DAILY_POSTS=8

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Find repo root
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
STATE_FILE="$REPO_ROOT/.loom/state/herald-posts.json"

# Ensure state directory and file exist
init_state() {
    mkdir -p "$(dirname "$STATE_FILE")"
    if [[ ! -f "$STATE_FILE" ]]; then
        echo '{"posts": [], "daily_counts": {}}' > "$STATE_FILE"
    fi
}

# Load token from .env if not already set
load_token() {
    if [[ -z "${MATHSTODON_TOKEN:-}" ]]; then
        if [[ -f "$REPO_ROOT/.env" ]]; then
            MATHSTODON_TOKEN=$(grep '^MATHSTODON_TOKEN=' "$REPO_ROOT/.env" | cut -d= -f2- | tr -d "'\"")
        fi
    fi

    if [[ -z "${MATHSTODON_TOKEN:-}" ]]; then
        echo -e "${RED}Error: MATHSTODON_TOKEN not set. Add it to .env or export it.${NC}" >&2
        exit 1
    fi
}

# Get today's post count
get_daily_count() {
    local today
    today=$(date -u +%Y-%m-%d)
    init_state
    jq -r --arg d "$today" '.daily_counts[$d] // 0' "$STATE_FILE"
}

# Check if subject was already posted
check_dedup() {
    local subject="$1"
    init_state
    local existing
    existing=$(jq -r --arg s "$subject" '[.posts[] | select(.subject == $s)] | length' "$STATE_FILE")
    if [[ "$existing" -gt 0 ]]; then
        return 0  # duplicate found
    fi
    return 1  # no duplicate
}

# Update state file after a successful post
update_state() {
    local subject="$1"
    local text="$2"
    local url="$3"
    local arc="$4"

    local today now tmp
    today=$(date -u +%Y-%m-%d)
    now=$(date -u +%Y-%m-%dT%H:%M:%SZ)
    tmp=$(mktemp)

    init_state

    # Build the post object conditionally (include arc only if provided)
    if [[ -n "$arc" ]]; then
        jq --arg subject "$subject" \
           --arg text "$text" \
           --arg url "$url" \
           --arg ts "$now" \
           --arg day "$today" \
           --arg arc "$arc" \
           '.posts += [{"subject": $subject, "text": $text, "url": $url, "posted_at": $ts, "arc": $arc}] | .daily_counts[$day] = ((.daily_counts[$day] // 0) + 1)' \
           "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
    else
        jq --arg subject "$subject" \
           --arg text "$text" \
           --arg url "$url" \
           --arg ts "$now" \
           --arg day "$today" \
           '.posts += [{"subject": $subject, "text": $text, "url": $url, "posted_at": $ts}] | .daily_counts[$day] = ((.daily_counts[$day] // 0) + 1)' \
           "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
    fi
}

# Increment daily count only (when no subject is provided)
increment_daily_count() {
    local today tmp
    today=$(date -u +%Y-%m-%d)
    tmp=$(mktemp)

    init_state

    jq --arg day "$today" \
       '.daily_counts[$day] = ((.daily_counts[$day] // 0) + 1)' \
       "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
}

# Show status
show_status() {
    init_state
    local today total_posts today_posts
    today=$(date -u +%Y-%m-%d)
    total_posts=$(jq '.posts | length' "$STATE_FILE")
    today_posts=$(jq -r --arg d "$today" '.daily_counts[$d] // 0' "$STATE_FILE")

    echo -e "${BLUE}=== Mathstodon Posting Status ===${NC}"
    echo ""
    echo "State file: $STATE_FILE"
    echo "Total posts tracked: $total_posts"
    echo "Posts today ($today): $today_posts / $MAX_DAILY_POSTS"
    echo ""

    if [[ "$today_posts" -ge "$MAX_DAILY_POSTS" ]]; then
        echo -e "${RED}Daily rate limit reached. No more posts today.${NC}"
    else
        local remaining=$((MAX_DAILY_POSTS - today_posts))
        echo -e "${GREEN}$remaining posts remaining today.${NC}"
    fi

    if [[ "$total_posts" -gt 0 ]]; then
        echo ""
        echo "Last 5 posts:"
        jq -r '.posts[-5:][] | "  [\(.posted_at)] \(.subject // "(no subject)"): \(.text[0:70])..."' "$STATE_FILE" 2>/dev/null || true
    fi

    exit 0
}

# Parse arguments
DRY_RUN=false
AUTOMATED=false
SUBJECT=""
ARC=""
TEXT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --automated)
            AUTOMATED=true
            shift
            ;;
        --subject)
            SUBJECT="$2"
            shift 2
            ;;
        --arc)
            ARC="$2"
            shift 2
            ;;
        --status)
            show_status
            ;;
        --help|-h)
            cat << 'EOF'
post-mathstodon.sh - Single source of truth for Mathstodon posting

Usage:
  ./post-mathstodon.sh "Post text"
  ./post-mathstodon.sh --subject "key" --arc "name" "Post text"
  ./post-mathstodon.sh --automated --subject "key" --arc "name" "Post text"
  ./post-mathstodon.sh --dry-run --subject "key" "Test post"
  ./post-mathstodon.sh --status

Options:
  --subject KEY    Dedup key for tracking (prevents double-posting)
  --arc NAME       Narrative arc this post belongs to
  --automated      Append [automated post] tag (for Herald agent)
  --dry-run        Show what would happen without posting or updating state
  --status         Show current rate limit and recent post history
  --help           Show this help

Environment:
  MATHSTODON_TOKEN   API access token (read from .env if not set)
EOF
            exit 0
            ;;
        -*)
            echo -e "${RED}Error: Unknown option: $1${NC}" >&2
            echo "Run '$0 --help' for usage" >&2
            exit 1
            ;;
        *)
            TEXT="$1"
            shift
            ;;
    esac
done

if [[ -z "$TEXT" ]]; then
    echo "Usage: $0 [--dry-run] [--automated] [--subject KEY] [--arc NAME] \"Post text\"" >&2
    exit 1
fi

# Append automated post tag only when --automated is set
if [[ "$AUTOMATED" == "true" ]]; then
    TEXT="${TEXT}

[automated post]"
fi

# Validate character limit
CHAR_COUNT=${#TEXT}
if [[ $CHAR_COUNT -gt $MAX_CHARS ]]; then
    echo -e "${RED}Error: Post is $CHAR_COUNT chars (max $MAX_CHARS)${NC}" >&2
    exit 1
fi

# Initialize state
init_state

# Check daily rate limit
DAILY_COUNT=$(get_daily_count)
if [[ "$DAILY_COUNT" -ge "$MAX_DAILY_POSTS" ]]; then
    echo -e "${RED}Error: Daily rate limit reached ($DAILY_COUNT/$MAX_DAILY_POSTS posts today)${NC}" >&2
    echo -e "${YELLOW}Use --status to see recent posts.${NC}" >&2
    exit 1
fi

# Check dedup if subject provided
if [[ -n "$SUBJECT" ]]; then
    if check_dedup "$SUBJECT"; then
        echo -e "${RED}Error: Subject '$SUBJECT' already posted. Skipping duplicate.${NC}" >&2
        echo -e "${YELLOW}Existing post:${NC}" >&2
        jq -r --arg s "$SUBJECT" '.posts[] | select(.subject == $s) | "  [\(.posted_at)] \(.url)"' "$STATE_FILE" >&2
        exit 1
    fi
fi

# Verify proof page URLs point to deployed content
# Extract proof slugs from leangenius.org/proof/<slug> URLs in the post text
_proof_slugs=()
while IFS= read -r _slug; do
    [[ -n "$_slug" ]] && _proof_slugs+=("$_slug")
done < <(echo "$TEXT" | grep -oE 'leangenius\.org/proof/[a-zA-Z0-9_-]+' | sed 's|leangenius\.org/proof/||' | sort -u)

if [[ ${#_proof_slugs[@]} -gt 0 ]]; then
    _verify_failed=false
    for _slug in "${_proof_slugs[@]}"; do
        _meta="$REPO_ROOT/src/data/proofs/$_slug/meta.json"

        # Check 1: meta.json exists
        if [[ ! -f "$_meta" ]]; then
            echo -e "${RED}Error: Proof page verification failed for '$_slug'${NC}" >&2
            echo -e "${RED}  meta.json not found: $_meta${NC}" >&2
            _verify_failed=true
            continue
        fi

        # Check 2: leanFile is an object with lineCount > 0
        _has_lean_file=$(jq '(.leanFile | type) == "object" and (.leanFile.lineCount > 0)' "$_meta" 2>/dev/null)
        if [[ "$_has_lean_file" != "true" ]]; then
            echo -e "${RED}Error: Proof page verification failed for '$_slug'${NC}" >&2
            echo -e "${RED}  meta.json leanFile is missing or has lineCount 0${NC}" >&2
            _verify_failed=true
            continue
        fi

        # Check 3: Listed in listings.json
        _listings="$REPO_ROOT/src/data/proofs/listings.json"
        if [[ ! -f "$_listings" ]]; then
            echo -e "${RED}Error: Proof page verification failed for '$_slug'${NC}" >&2
            echo -e "${RED}  listings.json not found${NC}" >&2
            _verify_failed=true
            continue
        fi
        _in_listings=$(jq --arg s "$_slug" '[.[] | select(.slug == $s)] | length' "$_listings" 2>/dev/null)
        if [[ "$_in_listings" -eq 0 ]]; then
            echo -e "${RED}Error: Proof page verification failed for '$_slug'${NC}" >&2
            echo -e "${RED}  Proof '$_slug' not found in listings.json${NC}" >&2
            _verify_failed=true
            continue
        fi

        # Check 4: Lean source file exists at the path declared in meta.json
        _lean_path=$(jq -r '.leanFile.path // empty' "$_meta" 2>/dev/null)
        if [[ -z "$_lean_path" ]]; then
            echo -e "${RED}Error: Proof page verification failed for '$_slug'${NC}" >&2
            echo -e "${RED}  meta.json leanFile.path is missing${NC}" >&2
            _verify_failed=true
            continue
        fi
        if [[ ! -f "$REPO_ROOT/proofs/$_lean_path" ]]; then
            echo -e "${RED}Error: Proof page verification failed for '$_slug'${NC}" >&2
            echo -e "${RED}  Lean source file not found: proofs/$_lean_path${NC}" >&2
            _verify_failed=true
            continue
        fi

        # Check 5: Verify the live site actually serves the proof (not "Proof not found")
        # Local checks pass against the working tree, but the site may not be deployed yet.
        _live_body=$(curl -sL --max-time 10 "https://leangenius.org/proof/$_slug" 2>/dev/null)
        if echo "$_live_body" | grep -q "Proof not found"; then
            echo -e "${RED}Error: Proof page verification failed for '$_slug'${NC}" >&2
            echo -e "${RED}  Live site returns 'Proof not found' — proof exists locally but hasn't been deployed yet${NC}" >&2
            echo -e "${YELLOW}  Wait for the deployer to run, then retry.${NC}" >&2
            _verify_failed=true
            continue
        fi
        if [[ -z "$_live_body" ]]; then
            echo -e "${YELLOW}Warning: Could not reach live site for '$_slug' (curl failed) — skipping live check${NC}" >&2
        fi

        echo -e "${GREEN}Verified proof page: $_slug${NC}"
    done

    if [[ "$_verify_failed" == "true" ]]; then
        echo -e "${RED}Aborting: One or more proof page URLs point to content that may not be deployed.${NC}" >&2
        echo -e "${YELLOW}Ensure the proof has a complete meta.json, is in listings.json, has a Lean source file, and is deployed to the live site.${NC}" >&2
        exit 1
    fi
fi

# Dry run: show what would happen
if [[ "$DRY_RUN" == "true" ]]; then
    echo -e "${YELLOW}[DRY RUN] Would post ($CHAR_COUNT chars):${NC}"
    echo "$TEXT"
    echo ""
    echo -e "${BLUE}State updates that would be applied:${NC}"
    echo "  Subject: ${SUBJECT:-"(none - post won't be tracked for dedup)"}"
    echo "  Arc: ${ARC:-"(none)"}"
    echo "  Daily count: $DAILY_COUNT -> $((DAILY_COUNT + 1)) / $MAX_DAILY_POSTS"
    exit 0
fi

# Load token (only needed for actual posting)
load_token

# Post via TypeScript Mastodon client (uses masto.js under the hood)
# The --no-state flag tells the TS client to skip state updates — we handle state here.
TS_CLIENT="$REPO_ROOT/scripts/herald/mastodon-client.ts"
TS_OUTPUT=$(MATHSTODON_TOKEN="$MATHSTODON_TOKEN" npx tsx "$TS_CLIENT" post --no-state "$TEXT" 2>&1) || {
    echo -e "${RED}Error posting via mastodon-client.ts:${NC}" >&2
    echo "$TS_OUTPUT" >&2
    exit 1
}

# Parse output: line 1 = "Posted successfully (N chars)", line 2 = URL (optional), last line = ID
POST_URL=$(echo "$TS_OUTPUT" | grep -E '^https://' | head -1)
POST_ID=$(echo "$TS_OUTPUT" | tail -1)

echo -e "${GREEN}Posted successfully ($CHAR_COUNT chars)${NC}"
if [[ -n "$POST_URL" ]]; then
    echo "$POST_URL"
fi
echo "$POST_ID"

# Update state file
if [[ -n "$SUBJECT" ]]; then
    update_state "$SUBJECT" "$TEXT" "${POST_URL:-""}" "$ARC"
    echo -e "${BLUE}State updated: subject='$SUBJECT'${ARC:+", arc='$ARC'"}${NC}"
else
    # No subject: just increment daily count
    increment_daily_count
    echo -e "${YELLOW}Warning: No --subject provided. Post tracked in daily count but not in dedup history.${NC}"
fi
