#!/bin/bash
#
# research-available.sh - List available (unclaimed) research problems
#
# Usage:
#   ./research-available.sh [--json] [--random] [--claim]
#
# Examples:
#   ./research-available.sh              # List all available
#   ./research-available.sh --random     # Pick one random problem
#   ./research-available.sh --random --claim  # Pick and claim a random problem
#
# Exit codes:
#   0 - Success
#   1 - No available problems
#   2 - Claim failed (with --claim)

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

# Options
JSON_OUTPUT=false
RANDOM_PICK=false
AUTO_CLAIM=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --json)
            JSON_OUTPUT=true
            shift
            ;;
        --random)
            RANDOM_PICK=true
            shift
            ;;
        --claim)
            AUTO_CLAIM=true
            shift
            ;;
        --help|-h)
            echo "Usage: $0 [--json] [--random] [--claim]"
            echo ""
            echo "List available (unclaimed) research problems."
            echo ""
            echo "Options:"
            echo "  --json    Output as JSON"
            echo "  --random  Pick one random problem"
            echo "  --claim   Auto-claim the selected problem (requires --random)"
            echo "  --help    Show this help"
            exit 0
            ;;
        *)
            echo "Error: Unknown option $1" >&2
            exit 1
            ;;
    esac
done

# Get all problems with status "available" from pool
AVAILABLE_IN_POOL=$(jq -r '.candidates[] | select(.status == "available") | .id' "$POOL_FILE")

if [[ -z "$AVAILABLE_IN_POOL" ]]; then
    if [[ "$JSON_OUTPUT" == "true" ]]; then
        echo "[]"
    else
        echo "No available problems in pool"
    fi
    exit 1
fi

# Filter out claimed problems
TRULY_AVAILABLE=""
for problem_id in $AVAILABLE_IN_POOL; do
    CLAIM_FILE="$CLAIMS_DIR/$problem_id.json"
    LOCK_DIR="$CLAIMS_DIR/$problem_id.lock"

    # Check if claimed
    if [[ -d "$LOCK_DIR" ]] || [[ -f "$CLAIM_FILE" ]]; then
        # Check if claim is stale
        if [[ -f "$CLAIM_FILE" ]]; then
            EXPIRES_AT=$(jq -r '.expires_at' "$CLAIM_FILE")
            NOW_EPOCH=$(date -u +%s)
            if [[ "$(uname)" == "Darwin" ]]; then
                EXPIRES_EPOCH=$(date -j -f "%Y-%m-%dT%H:%M:%SZ" "$EXPIRES_AT" +%s 2>/dev/null || echo 0)
            else
                EXPIRES_EPOCH=$(date -d "$EXPIRES_AT" +%s 2>/dev/null || echo 0)
            fi

            if [[ $NOW_EPOCH -gt $EXPIRES_EPOCH ]]; then
                # Stale claim - problem is available
                TRULY_AVAILABLE="$TRULY_AVAILABLE $problem_id"
            fi
            # Else: valid claim, skip this problem
        fi
        # Else: lock without claim file, skip (will be cleaned up)
    else
        # Not claimed
        TRULY_AVAILABLE="$TRULY_AVAILABLE $problem_id"
    fi
done

# Trim whitespace
TRULY_AVAILABLE=$(echo "$TRULY_AVAILABLE" | xargs)

if [[ -z "$TRULY_AVAILABLE" ]]; then
    if [[ "$JSON_OUTPUT" == "true" ]]; then
        echo "[]"
    else
        echo "No available problems (all are claimed)"
    fi
    exit 1
fi

# Random pick
if [[ "$RANDOM_PICK" == "true" ]]; then
    # Convert to array and pick random
    AVAILABLE_ARRAY=($TRULY_AVAILABLE)
    COUNT=${#AVAILABLE_ARRAY[@]}
    RANDOM_INDEX=$((RANDOM % COUNT))
    SELECTED="${AVAILABLE_ARRAY[$RANDOM_INDEX]}"

    if [[ "$AUTO_CLAIM" == "true" ]]; then
        # Claim the selected problem
        if "$REPO_ROOT/.loom/scripts/research-claim.sh" "$SELECTED"; then
            if [[ "$JSON_OUTPUT" == "true" ]]; then
                jq ".candidates[] | select(.id == \"$SELECTED\")" "$POOL_FILE"
            else
                echo "Selected and claimed: $SELECTED"
                # Show problem details
                jq -r ".candidates[] | select(.id == \"$SELECTED\") | \"  Name: \\(.name)\\n  Tier: \\(.tier)\\n  Tractability: \\(.tractability)\\n  Notes: \\(.notes)\"" "$POOL_FILE"
            fi
            exit 0
        else
            echo "Error: Failed to claim '$SELECTED'" >&2
            exit 2
        fi
    else
        if [[ "$JSON_OUTPUT" == "true" ]]; then
            jq ".candidates[] | select(.id == \"$SELECTED\")" "$POOL_FILE"
        else
            echo "Random pick: $SELECTED"
            jq -r ".candidates[] | select(.id == \"$SELECTED\") | \"  Name: \\(.name)\\n  Tier: \\(.tier)\\n  Tractability: \\(.tractability)\\n  Notes: \\(.notes)\"" "$POOL_FILE"
        fi
    fi
else
    # List all available
    if [[ "$JSON_OUTPUT" == "true" ]]; then
        # Build JSON array of available problems
        echo "["
        FIRST=true
        for problem_id in $TRULY_AVAILABLE; do
            if [[ "$FIRST" == "true" ]]; then
                FIRST=false
            else
                echo ","
            fi
            jq ".candidates[] | select(.id == \"$problem_id\")" "$POOL_FILE"
        done
        echo "]"
    else
        echo "Available problems ($(echo $TRULY_AVAILABLE | wc -w | xargs) total):"
        echo ""
        for problem_id in $TRULY_AVAILABLE; do
            jq -r ".candidates[] | select(.id == \"$problem_id\") | \"  [\(.tier)] \\(.id) - \\(.name) (tractability: \\(.tractability))\"" "$POOL_FILE"
        done
    fi
fi
