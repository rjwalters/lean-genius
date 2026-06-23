#!/bin/bash
#
# claim-target.sh - Claim a proof gallery entry for exclusive enrichment work
#
# Usage:
#   ./claim-target.sh claim-next            # Claim the highest-priority unclaimed target
#   ./claim-target.sh claim <id>            # Claim a specific entry
#   ./claim-target.sh complete <id>         # Mark as completed and release
#   ./claim-target.sh release <id>          # Release a claimed entry
#   ./claim-target.sh status                # Show all claims
#   ./claim-target.sh cleanup               # Remove stale claims
#
# Environment:
#   ENRICHER_ID - Agent identifier (default: enricher-PID)
#   CLAIM_TTL   - Claim time-to-live in minutes (default: 90)

set -euo pipefail
shopt -s nullglob

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

REPO_ROOT="${REPO_ROOT:-$(find_repo_root)}"
CLAIMS_DIR="$REPO_ROOT/.lean/state/enrichment-claims"
TRACKER_FILE="$REPO_ROOT/src/data/proofs/enrichment-tracker.json"
FIND_TARGETS="$REPO_ROOT/scripts/enricher/find-targets.ts"
COMPLETIONS_DIR="$REPO_ROOT/.loom/signals/completions"

# Defaults
TTL_MINUTES="${CLAIM_TTL:-90}"
AGENT_ID="${ENRICHER_ID:-enricher-$$}"

# Ensure claims directory exists
mkdir -p "$CLAIMS_DIR"

# Initialize tracker if missing
if [[ ! -f "$TRACKER_FILE" ]]; then
    echo '{"version": 1, "entries": {}}' > "$TRACKER_FILE"
fi

# Calculate timestamps
get_timestamps() {
    CLAIMED_AT=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    if [[ "$(uname)" == "Darwin" ]]; then
        EXPIRES_AT=$(date -u -v+${TTL_MINUTES}M +"%Y-%m-%dT%H:%M:%SZ")
    else
        EXPIRES_AT=$(date -u -d "+${TTL_MINUTES} minutes" +"%Y-%m-%dT%H:%M:%SZ")
    fi
}

# Check if claim is expired
is_claim_expired() {
    local claim_file="$1"
    if [[ ! -f "$claim_file" ]]; then
        return 0
    fi

    local expires_at
    expires_at=$(jq -r '.expires_at' "$claim_file")

    local now_epoch expires_epoch
    now_epoch=$(date -u +%s)

    if [[ "$(uname)" == "Darwin" ]]; then
        local stripped="${expires_at%Z}"
        expires_epoch=$(TZ=UTC date -j -f "%Y-%m-%dT%H:%M:%S" "$stripped" +%s 2>/dev/null || echo 0)
    else
        expires_epoch=$(date -d "$expires_at" +%s 2>/dev/null || echo 0)
    fi

    [[ $now_epoch -gt $expires_epoch ]]
}

# Claim a specific entry
claim_target() {
    local target_id="$1"
    local lock_dir="$CLAIMS_DIR/$target_id.lock"
    local claim_file="$CLAIMS_DIR/$target_id.json"

    get_timestamps

    # Try atomic claim with mkdir
    if mkdir "$lock_dir" 2>/dev/null; then
        cat > "$claim_file" << EOF
{
  "target_id": "$target_id",
  "agent_id": "$AGENT_ID",
  "claimed_at": "$CLAIMED_AT",
  "expires_at": "$EXPIRES_AT",
  "ttl_minutes": $TTL_MINUTES,
  "status": "in_progress"
}
EOF
        echo "Claimed $target_id by $AGENT_ID (expires: $EXPIRES_AT)"
        return 0
    else
        # Lock exists - check if stale
        if is_claim_expired "$claim_file"; then
            echo "Stale claim detected, reclaiming..."
            rm -rf "$lock_dir"
            rm -f "$claim_file"

            if mkdir "$lock_dir" 2>/dev/null; then
                cat > "$claim_file" << EOF
{
  "target_id": "$target_id",
  "agent_id": "$AGENT_ID",
  "claimed_at": "$CLAIMED_AT",
  "expires_at": "$EXPIRES_AT",
  "ttl_minutes": $TTL_MINUTES,
  "status": "in_progress"
}
EOF
                echo "Claimed $target_id by $AGENT_ID (expires: $EXPIRES_AT)"
                return 0
            fi
        fi

        local existing_agent
        existing_agent=$(jq -r '.agent_id' "$claim_file" 2>/dev/null || echo "unknown")
        echo "Error: $target_id already claimed by $existing_agent" >&2
        return 1
    fi
}

# Claim the highest-priority unclaimed target
claim_next() {
    # Get sorted targets
    local targets_json
    targets_json=$(npx tsx "$FIND_TARGETS" --json 2>/dev/null)

    if [[ -z "$targets_json" ]]; then
        echo "Error: Could not find enrichment targets" >&2
        return 1
    fi

    # Iterate through targets in priority order
    local count
    count=$(echo "$targets_json" | jq 'length')

    for i in $(seq 0 $((count - 1))); do
        local target_id
        target_id=$(echo "$targets_json" | jq -r ".[$i].id")

        # Skip if currently claimed (and not expired)
        local claim_file="$CLAIMS_DIR/$target_id.json"
        if [[ -d "$CLAIMS_DIR/$target_id.lock" ]] && ! is_claim_expired "$claim_file"; then
            continue
        fi

        # Try to claim it
        if claim_target "$target_id"; then
            local quality passes priority
            quality=$(echo "$targets_json" | jq ".[$i].quality")
            passes=$(echo "$targets_json" | jq ".[$i].passes")
            priority=$(echo "$targets_json" | jq ".[$i].priority")
            echo "Target: $target_id (quality: $quality, passes: $passes, priority: $priority)"
            return 0
        fi
    done

    echo "No unclaimed targets available" >&2
    return 1
}

# Release a claim
release_target() {
    local target_id="$1"
    local lock_dir="$CLAIMS_DIR/$target_id.lock"
    local claim_file="$CLAIMS_DIR/$target_id.json"

    if [[ -d "$lock_dir" ]]; then
        rm -rf "$lock_dir"
        rm -f "$claim_file"
        echo "Released $target_id"
    else
        echo "Warning: No claim found for $target_id" >&2
    fi
}

# Mark as completed, update tracker, and release
complete_target() {
    local target_id="$1"

    get_timestamps

    # Update enrichment tracker
    local tmp_file
    tmp_file=$(mktemp)

    if jq -e ".entries[\"$target_id\"]" "$TRACKER_FILE" > /dev/null 2>&1; then
        # Existing entry: increment passes and update quality
        local quality
        quality=$(npx tsx "$FIND_TARGETS" --json 2>/dev/null | jq "[.[] | select(.id == \"$target_id\")] | .[0].quality // 0")
        jq --arg id "$target_id" \
           --arg ts "$CLAIMED_AT" \
           --argjson quality "$quality" \
           '.entries[$id].passes += 1 |
            .entries[$id].lastEnriched = $ts |
            .entries[$id].quality = $quality' \
           "$TRACKER_FILE" > "$tmp_file"
    else
        # New entry
        local quality
        quality=$(npx tsx "$FIND_TARGETS" --json 2>/dev/null | jq "[.[] | select(.id == \"$target_id\")] | .[0].quality // 0")
        jq --arg id "$target_id" \
           --arg ts "$CLAIMED_AT" \
           --argjson quality "$quality" \
           '.entries[$id] = {
               "passes": 1,
               "lastEnriched": $ts,
               "quality": ($quality // 0)
           }' \
           "$TRACKER_FILE" > "$tmp_file"
    fi

    mv "$tmp_file" "$TRACKER_FILE"

    # Release the claim
    release_target "$target_id"

    # Create completion signal for daemon stats tracking
    mkdir -p "$COMPLETIONS_DIR"
    touch "$COMPLETIONS_DIR/enrichment-completed-$target_id-$(date +%s)"

    echo "Marked $target_id as enriched (pass $(jq -r ".entries[\"$target_id\"].passes" "$TRACKER_FILE"))"
}

# Show status
show_status() {
    echo "=== Enrichment Claims ==="
    echo ""

    local active_count=0
    local stale_count=0

    for lock_dir in "$CLAIMS_DIR"/*.lock; do
        [[ ! -d "$lock_dir" ]] && continue

        local target_id
        target_id=$(basename "$lock_dir" .lock)
        local claim_file="$CLAIMS_DIR/$target_id.json"

        if [[ -f "$claim_file" ]]; then
            local agent expires status
            agent=$(jq -r '.agent_id' "$claim_file")
            expires=$(jq -r '.expires_at' "$claim_file")

            if is_claim_expired "$claim_file"; then
                status="STALE"
                ((++stale_count))
            else
                status="active"
                ((++active_count))
            fi

            echo "  $target_id: $agent ($status, expires: $expires)"
        fi
    done

    if [[ $active_count -eq 0 && $stale_count -eq 0 ]]; then
        echo "  (no active claims)"
    fi

    echo ""

    # Show tracker stats
    if [[ -f "$TRACKER_FILE" ]]; then
        local total_entries enriched_entries avg_quality
        total_entries=$(jq '.entries | length' "$TRACKER_FILE" 2>/dev/null || echo 0)
        avg_quality=$(jq '[.entries[] | .quality] | if length > 0 then add / length else 0 end' "$TRACKER_FILE" 2>/dev/null || echo 0)

        echo "Tracker: $total_entries entries enriched"
        echo "Average quality: $avg_quality"
    fi

    echo "Active claims: $active_count"
    echo "Stale claims: $stale_count"
}

# Cleanup stale claims
cleanup_claims() {
    local cleaned=0

    for lock_dir in "$CLAIMS_DIR"/*.lock; do
        [[ ! -d "$lock_dir" ]] && continue

        local target_id
        target_id=$(basename "$lock_dir" .lock)
        local claim_file="$CLAIMS_DIR/$target_id.json"

        if is_claim_expired "$claim_file"; then
            rm -rf "$lock_dir"
            rm -f "$claim_file"
            echo "Cleaned up stale claim: $target_id"
            ((++cleaned))
        fi
    done

    if [[ $cleaned -eq 0 ]]; then
        echo "No stale claims to clean up"
    else
        echo "Cleaned up $cleaned stale claims"
    fi
}

# Extend a claim (renew TTL)
extend_claim() {
    local target_id="$1"
    local claim_file="$CLAIMS_DIR/$target_id.json"

    if [[ ! -f "$claim_file" ]]; then
        echo "Error: No claim found for $target_id" >&2
        return 1
    fi

    get_timestamps

    local tmp_file
    tmp_file=$(mktemp)
    jq ".expires_at = \"$EXPIRES_AT\"" "$claim_file" > "$tmp_file"
    mv "$tmp_file" "$claim_file"

    echo "Extended claim for $target_id (new expires: $EXPIRES_AT)"
}

# Main command dispatch
case "${1:-help}" in
    claim-next)
        claim_next
        ;;
    claim)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 claim <target-id>" >&2
            exit 1
        fi
        claim_target "$2"
        ;;
    release)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 release <target-id>" >&2
            exit 1
        fi
        release_target "$2"
        ;;
    complete)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 complete <target-id>" >&2
            exit 1
        fi
        complete_target "$2"
        ;;
    extend)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 extend <target-id>" >&2
            exit 1
        fi
        extend_claim "$2"
        ;;
    status)
        show_status
        ;;
    cleanup)
        cleanup_claims
        ;;
    help|--help|-h)
        cat << EOF
Enrichment Target Claiming System

Provides atomic claiming for parallel proof enrichment.

Commands:
  claim-next              Claim the highest-priority unclaimed target
  claim <target-id>       Claim a specific entry
  release <target-id>     Release a claimed entry
  complete <target-id>    Mark as enriched, update tracker, release
  extend <target-id>      Extend claim TTL
  status                  Show all claims and tracker stats
  cleanup                 Remove stale claims
  help                    Show this help

Environment Variables:
  ENRICHER_ID   Agent identifier (default: enricher-PID)
  CLAIM_TTL     Claim time-to-live in minutes (default: 90)

Examples:
  ENRICHER_ID=enricher-1 ./claim-target.sh claim-next
  ENRICHER_ID=enricher-1 ./claim-target.sh complete pythagorean-theorem
  ./claim-target.sh status
EOF
        ;;
    *)
        echo "Unknown command: $1" >&2
        echo "Run '$0 help' for usage" >&2
        exit 1
        ;;
esac
