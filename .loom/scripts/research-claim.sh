#!/bin/bash
#
# research-claim.sh - Claim a research problem for exclusive work
#
# Usage:
#   ./research-claim.sh <problem-id> [--ttl <minutes>] [--agent <agent-id>]
#
# Examples:
#   ./research-claim.sh vietas-formulas
#   ./research-claim.sh hurwitz --ttl 90 --agent terminal-2
#
# Exit codes:
#   0 - Successfully claimed
#   1 - Already claimed by another agent
#   2 - Problem not found
#   3 - Invalid arguments

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
CLAIMS_DIR="$REPO_ROOT/research/claims"
POOL_FILE="$REPO_ROOT/research/candidate-pool.json"

# Defaults
TTL_MINUTES=60
AGENT_ID="${CLAUDE_AGENT_ID:-agent-$$}"

# Parse arguments
PROBLEM_ID=""
while [[ $# -gt 0 ]]; do
    case $1 in
        --ttl)
            TTL_MINUTES="$2"
            shift 2
            ;;
        --agent)
            AGENT_ID="$2"
            shift 2
            ;;
        --help|-h)
            echo "Usage: $0 <problem-id> [--ttl <minutes>] [--agent <agent-id>]"
            echo ""
            echo "Claim a research problem for exclusive work."
            echo ""
            echo "Options:"
            echo "  --ttl <minutes>   Time-to-live for claim (default: 60)"
            echo "  --agent <id>      Agent identifier (default: agent-PID)"
            echo "  --help            Show this help"
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
    echo "Usage: $0 <problem-id> [--ttl <minutes>]" >&2
    exit 3
fi

# Check problem exists in pool
if ! jq -e ".candidates[] | select(.id == \"$PROBLEM_ID\")" "$POOL_FILE" > /dev/null 2>&1; then
    echo "Error: Problem '$PROBLEM_ID' not found in candidate pool" >&2
    exit 2
fi

# Check problem status
PROBLEM_STATUS=$(jq -r ".candidates[] | select(.id == \"$PROBLEM_ID\") | .status" "$POOL_FILE")
if [[ "$PROBLEM_STATUS" != "available" ]]; then
    echo "Warning: Problem '$PROBLEM_ID' has status '$PROBLEM_STATUS' (not 'available')" >&2
fi

# Ensure claims directory exists
mkdir -p "$CLAIMS_DIR"

# Calculate timestamps
CLAIMED_AT=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
if [[ "$(uname)" == "Darwin" ]]; then
    EXPIRES_AT=$(date -u -v+${TTL_MINUTES}M +"%Y-%m-%dT%H:%M:%SZ")
else
    EXPIRES_AT=$(date -u -d "+${TTL_MINUTES} minutes" +"%Y-%m-%dT%H:%M:%SZ")
fi

LOCK_DIR="$CLAIMS_DIR/$PROBLEM_ID.lock"
CLAIM_FILE="$CLAIMS_DIR/$PROBLEM_ID.json"

# Atomic claim using mkdir
if mkdir "$LOCK_DIR" 2>/dev/null; then
    # Successfully acquired lock - write claim file
    cat > "$CLAIM_FILE" << EOF
{
  "problem_id": "$PROBLEM_ID",
  "agent_id": "$AGENT_ID",
  "claimed_at": "$CLAIMED_AT",
  "expires_at": "$EXPIRES_AT",
  "ttl_minutes": $TTL_MINUTES,
  "status": "in_progress"
}
EOF

    echo "Claimed '$PROBLEM_ID' by $AGENT_ID (expires: $EXPIRES_AT)"
    exit 0
else
    # Lock exists - check if it's stale
    if [[ -f "$CLAIM_FILE" ]]; then
        EXISTING_EXPIRES=$(jq -r '.expires_at' "$CLAIM_FILE")
        EXISTING_AGENT=$(jq -r '.agent_id' "$CLAIM_FILE")

        # Compare timestamps
        NOW_EPOCH=$(date -u +%s)
        if [[ "$(uname)" == "Darwin" ]]; then
            EXPIRES_EPOCH=$(date -j -f "%Y-%m-%dT%H:%M:%SZ" "$EXISTING_EXPIRES" +%s 2>/dev/null || echo 0)
        else
            EXPIRES_EPOCH=$(date -d "$EXISTING_EXPIRES" +%s 2>/dev/null || echo 0)
        fi

        if [[ $NOW_EPOCH -gt $EXPIRES_EPOCH ]]; then
            # Claim is stale - remove and retry
            echo "Stale claim detected, reclaiming..."
            rm -rf "$LOCK_DIR"
            rm -f "$CLAIM_FILE"

            # Retry claim
            if mkdir "$LOCK_DIR" 2>/dev/null; then
                cat > "$CLAIM_FILE" << EOF
{
  "problem_id": "$PROBLEM_ID",
  "agent_id": "$AGENT_ID",
  "claimed_at": "$CLAIMED_AT",
  "expires_at": "$EXPIRES_AT",
  "ttl_minutes": $TTL_MINUTES,
  "status": "in_progress"
}
EOF
                echo "Claimed '$PROBLEM_ID' by $AGENT_ID (expires: $EXPIRES_AT)"
                exit 0
            fi
        fi

        echo "Error: Problem '$PROBLEM_ID' already claimed by $EXISTING_AGENT (expires: $EXISTING_EXPIRES)" >&2
        exit 1
    else
        echo "Error: Lock exists but no claim file - run research-cleanup.sh" >&2
        exit 1
    fi
fi
