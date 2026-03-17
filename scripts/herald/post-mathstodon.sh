#!/usr/bin/env bash
#
# post-mathstodon.sh - Post a status to Mathstodon (Mastodon)
#
# Usage:
#   ./post-mathstodon.sh "Your post text here"
#   ./post-mathstodon.sh --dry-run "Test post"
#
# Environment:
#   MATHSTODON_TOKEN - API access token (read from .env if not set)
#

set -euo pipefail

# Config
MASTODON_INSTANCE="https://mathstodon.xyz"
MAX_CHARS=500

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Find repo root
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd)"

# Load token from .env if not already set
if [[ -z "${MATHSTODON_TOKEN:-}" ]]; then
    if [[ -f "$REPO_ROOT/.env" ]]; then
        MATHSTODON_TOKEN=$(grep '^MATHSTODON_TOKEN=' "$REPO_ROOT/.env" | cut -d= -f2- | tr -d "'\"")
    fi
fi

if [[ -z "${MATHSTODON_TOKEN:-}" ]]; then
    echo -e "${RED}Error: MATHSTODON_TOKEN not set. Add it to .env or export it.${NC}" >&2
    exit 1
fi

# Parse arguments
DRY_RUN=false
TEXT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        *)
            TEXT="$1"
            shift
            ;;
    esac
done

if [[ -z "$TEXT" ]]; then
    echo "Usage: $0 [--dry-run] \"Post text\"" >&2
    exit 1
fi

# Append automated post tag
TEXT="${TEXT}

[automated post]"

# Validate character limit
CHAR_COUNT=${#TEXT}
if [[ $CHAR_COUNT -gt $MAX_CHARS ]]; then
    echo -e "${RED}Error: Post is $CHAR_COUNT chars (max $MAX_CHARS)${NC}" >&2
    exit 1
fi

if [[ "$DRY_RUN" == "true" ]]; then
    echo -e "${YELLOW}[DRY RUN] Would post ($CHAR_COUNT chars):${NC}"
    echo "$TEXT"
    exit 0
fi

# Post via Mastodon API
# Use jq for proper JSON escaping of the status text
JSON_PAYLOAD=$(jq -n --arg status "$TEXT" '{"status": $status, "visibility": "public"}')

RESPONSE=$(curl -s -w "\n%{http_code}" \
    -X POST \
    -H "Authorization: Bearer $MATHSTODON_TOKEN" \
    -H "Content-Type: application/json" \
    -d "$JSON_PAYLOAD" \
    "$MASTODON_INSTANCE/api/v1/statuses")

HTTP_CODE=$(echo "$RESPONSE" | tail -1)
BODY=$(echo "$RESPONSE" | sed '$d')

if [[ "$HTTP_CODE" -ge 200 && "$HTTP_CODE" -lt 300 ]]; then
    POST_URL=$(echo "$BODY" | jq -r '.url // empty')
    POST_ID=$(echo "$BODY" | jq -r '.id // empty')
    echo -e "${GREEN}Posted successfully ($CHAR_COUNT chars)${NC}"
    if [[ -n "$POST_URL" ]]; then
        echo "$POST_URL"
    fi
    echo "$POST_ID"
else
    ERROR_MSG=$(echo "$BODY" | jq -r '.error // "Unknown error"' 2>/dev/null || echo "$BODY")
    echo -e "${RED}Error posting (HTTP $HTTP_CODE): $ERROR_MSG${NC}" >&2
    exit 1
fi
