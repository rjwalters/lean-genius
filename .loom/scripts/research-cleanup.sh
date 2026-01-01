#!/bin/bash
#
# research-cleanup.sh - Clean up stale research claims
#
# Usage:
#   ./research-cleanup.sh [--dry-run] [--all]
#
# Examples:
#   ./research-cleanup.sh            # Clean stale claims
#   ./research-cleanup.sh --dry-run  # Preview what would be cleaned
#   ./research-cleanup.sh --all      # Remove ALL claims (force)
#
# Exit codes:
#   0 - Success (or nothing to clean)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
CLAIMS_DIR="$REPO_ROOT/research/claims"

# Options
DRY_RUN=false
CLEAN_ALL=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --all)
            CLEAN_ALL=true
            shift
            ;;
        --help|-h)
            echo "Usage: $0 [--dry-run] [--all]"
            echo ""
            echo "Clean up stale research claims."
            echo ""
            echo "Options:"
            echo "  --dry-run  Preview what would be cleaned"
            echo "  --all      Remove ALL claims (force reset)"
            echo "  --help     Show this help"
            exit 0
            ;;
        *)
            echo "Error: Unknown option $1" >&2
            exit 1
            ;;
    esac
done

# Ensure claims directory exists
if [[ ! -d "$CLAIMS_DIR" ]]; then
    echo "No claims directory found"
    exit 0
fi

NOW_EPOCH=$(date -u +%s)
CLEANED=0
ACTIVE=0

echo "Scanning claims..."
echo ""

# Find all claim files
shopt -s nullglob
for claim_file in "$CLAIMS_DIR"/*.json; do
    [[ -f "$claim_file" ]] || continue

    problem_id=$(basename "$claim_file" .json)
    agent_id=$(jq -r '.agent_id' "$claim_file")
    claimed_at=$(jq -r '.claimed_at' "$claim_file")
    expires_at=$(jq -r '.expires_at' "$claim_file")

    # Parse expiry time
    if [[ "$(uname)" == "Darwin" ]]; then
        EXPIRES_EPOCH=$(date -j -f "%Y-%m-%dT%H:%M:%SZ" "$expires_at" +%s 2>/dev/null || echo 0)
    else
        EXPIRES_EPOCH=$(date -d "$expires_at" +%s 2>/dev/null || echo 0)
    fi

    IS_STALE=false
    if [[ $NOW_EPOCH -gt $EXPIRES_EPOCH ]]; then
        IS_STALE=true
    fi

    if [[ "$CLEAN_ALL" == "true" ]] || [[ "$IS_STALE" == "true" ]]; then
        if [[ "$IS_STALE" == "true" ]]; then
            echo "  STALE: $problem_id (by $agent_id, expired: $expires_at)"
        else
            echo "  ACTIVE: $problem_id (by $agent_id, expires: $expires_at) [--all]"
        fi

        if [[ "$DRY_RUN" == "false" ]]; then
            rm -rf "$CLAIMS_DIR/$problem_id.lock" 2>/dev/null || true
            rm -f "$claim_file"
            CLEANED=$((CLEANED + 1))
        fi
    else
        # Calculate remaining time
        REMAINING=$((EXPIRES_EPOCH - NOW_EPOCH))
        REMAINING_MIN=$((REMAINING / 60))
        echo "  ACTIVE: $problem_id (by $agent_id, ${REMAINING_MIN}m remaining)"
        ACTIVE=$((ACTIVE + 1))
    fi
done

# Clean orphaned lock directories (no claim file)
for lock_dir in "$CLAIMS_DIR"/*.lock; do
    [[ -d "$lock_dir" ]] || continue

    problem_id=$(basename "$lock_dir" .lock)
    claim_file="$CLAIMS_DIR/$problem_id.json"

    if [[ ! -f "$claim_file" ]]; then
        echo "  ORPHAN: $problem_id.lock (no claim file)"
        if [[ "$DRY_RUN" == "false" ]]; then
            rm -rf "$lock_dir"
            CLEANED=$((CLEANED + 1))
        fi
    fi
done

echo ""
if [[ "$DRY_RUN" == "true" ]]; then
    echo "Dry run - no changes made"
    echo "Would clean: $CLEANED items"
else
    echo "Cleaned: $CLEANED items"
fi
echo "Active claims: $ACTIVE"
