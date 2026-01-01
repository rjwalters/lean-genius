#!/bin/bash
#
# research-release.sh - Release a claimed research problem
#
# Usage:
#   ./research-release.sh <problem-id> [--status <status>] [--notes <notes>]
#
# Examples:
#   ./research-release.sh vietas-formulas --status completed
#   ./research-release.sh hurwitz --status skipped --notes "Missing quaternion infrastructure"
#
# Exit codes:
#   0 - Successfully released
#   1 - Not claimed or claim doesn't exist
#   2 - Problem not found
#   3 - Invalid arguments

set -euo pipefail

# Find repo root by traversing up to find .git
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
CLAIMS_DIR="$REPO_ROOT/research/claims"
POOL_FILE="$REPO_ROOT/research/candidate-pool.json"

# Defaults
NEW_STATUS=""
NEW_NOTES=""
UPDATE_POOL=false

# Parse arguments
PROBLEM_ID=""
while [[ $# -gt 0 ]]; do
    case $1 in
        --status)
            NEW_STATUS="$2"
            UPDATE_POOL=true
            shift 2
            ;;
        --notes)
            NEW_NOTES="$2"
            UPDATE_POOL=true
            shift 2
            ;;
        --help|-h)
            echo "Usage: $0 <problem-id> [--status <status>] [--notes <notes>]"
            echo ""
            echo "Release a claimed research problem."
            echo ""
            echo "Options:"
            echo "  --status <status>  Update problem status in pool"
            echo "                     Valid: completed, skipped, surveyed, available"
            echo "  --notes <notes>    Update problem notes in pool"
            echo "  --help             Show this help"
            exit 0
            ;;
        -*)
            echo "Error: Unknown option $1" >&2
            exit 3
            ;;
        *)
            if [[ -z "$PROBLEM_ID" ]]; then
                PROBLEM_ID="$1"
            else
                echo "Error: Unexpected argument $1" >&2
                exit 3
            fi
            shift
            ;;
    esac
done

if [[ -z "$PROBLEM_ID" ]]; then
    echo "Error: Problem ID required" >&2
    echo "Usage: $0 <problem-id> [--status <status>]" >&2
    exit 3
fi

# Validate status if provided
if [[ -n "$NEW_STATUS" ]]; then
    case "$NEW_STATUS" in
        completed|skipped|surveyed|available|in-progress)
            ;;
        *)
            echo "Error: Invalid status '$NEW_STATUS'" >&2
            echo "Valid statuses: completed, skipped, surveyed, available, in-progress" >&2
            exit 3
            ;;
    esac
fi

LOCK_DIR="$CLAIMS_DIR/$PROBLEM_ID.lock"
CLAIM_FILE="$CLAIMS_DIR/$PROBLEM_ID.json"

# Check if claim exists
if [[ ! -d "$LOCK_DIR" ]] && [[ ! -f "$CLAIM_FILE" ]]; then
    echo "Warning: No claim found for '$PROBLEM_ID'" >&2
    # Continue anyway to update pool status if requested
fi

# Get claim info before removing
if [[ -f "$CLAIM_FILE" ]]; then
    CLAIMED_BY=$(jq -r '.agent_id' "$CLAIM_FILE")
    CLAIMED_AT=$(jq -r '.claimed_at' "$CLAIM_FILE")
    echo "Releasing claim on '$PROBLEM_ID' (was held by $CLAIMED_BY since $CLAIMED_AT)"
fi

# Remove lock and claim file
rm -rf "$LOCK_DIR" 2>/dev/null || true
rm -f "$CLAIM_FILE" 2>/dev/null || true

# Update pool if requested
if [[ "$UPDATE_POOL" == "true" ]]; then
    TEMP_FILE=$(mktemp)

    if [[ -n "$NEW_STATUS" ]] && [[ -n "$NEW_NOTES" ]]; then
        # Update both status and notes
        jq "(.candidates[] | select(.id == \"$PROBLEM_ID\")) |= . + {\"status\": \"$NEW_STATUS\", \"notes\": \"$NEW_NOTES\"}" \
            "$POOL_FILE" > "$TEMP_FILE"
        echo "Updated '$PROBLEM_ID' status to '$NEW_STATUS' with notes in pool"
    elif [[ -n "$NEW_STATUS" ]]; then
        # Update status only
        jq "(.candidates[] | select(.id == \"$PROBLEM_ID\") | .status) = \"$NEW_STATUS\"" \
            "$POOL_FILE" > "$TEMP_FILE"
        echo "Updated '$PROBLEM_ID' status to '$NEW_STATUS' in pool"
    elif [[ -n "$NEW_NOTES" ]]; then
        # Update notes only
        jq "(.candidates[] | select(.id == \"$PROBLEM_ID\") | .notes) = \"$NEW_NOTES\"" \
            "$POOL_FILE" > "$TEMP_FILE"
        echo "Updated '$PROBLEM_ID' notes in pool"
    fi

    mv "$TEMP_FILE" "$POOL_FILE"
fi

echo "Released '$PROBLEM_ID'"
exit 0
