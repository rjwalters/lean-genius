#!/bin/bash
#
# claim-problem.sh - Claim a research problem for exclusive work
#
# Usage:
#   ./claim-problem.sh claim <problem-id>      # Claim a specific problem
#   ./claim-problem.sh claim-random            # Claim random problem (knowledge-prioritized)
#   ./claim-problem.sh release <problem-id>    # Release a claimed problem
#   ./claim-problem.sh update <problem-id> <status>  # Update problem status
#   ./claim-problem.sh status                  # Show all claims
#   ./claim-problem.sh cleanup                 # Remove stale claims
#
# Environment:
#   RESEARCHER_ID - Agent identifier (default: researcher-PID)
#   CLAIM_TTL     - Claim time-to-live in minutes (default: 90)

set -euo pipefail
shopt -s nullglob

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
CLAIMS_DIR="$REPO_ROOT/research/claims"
POOL_FILE="$REPO_ROOT/research/candidate-pool.json"
PROBLEMS_DIR="$REPO_ROOT/src/data/research/problems"

# Defaults
TTL_MINUTES="${CLAIM_TTL:-90}"
AGENT_ID="${RESEARCHER_ID:-researcher-$$}"

# Ensure directories exist
mkdir -p "$CLAIMS_DIR"
mkdir -p "$PROBLEMS_DIR"

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
        return 0  # No claim file = "expired"
    fi

    local expires_at
    expires_at=$(jq -r '.expires_at' "$claim_file")

    local now_epoch
    local expires_epoch
    now_epoch=$(date -u +%s)

    if [[ "$(uname)" == "Darwin" ]]; then
        expires_epoch=$(date -j -f "%Y-%m-%dT%H:%M:%SZ" "$expires_at" +%s 2>/dev/null || echo 0)
    else
        expires_epoch=$(date -d "$expires_at" +%s 2>/dev/null || echo 0)
    fi

    [[ $now_epoch -gt $expires_epoch ]]
}

# Calculate knowledge score for a problem
get_knowledge_score() {
    local problem_id="$1"
    local problem_file="$PROBLEMS_DIR/${problem_id}.json"
    
    if [[ ! -f "$problem_file" ]]; then
        echo "0"  # No file = EMPTY knowledge
        return
    fi
    
    local score
    score=$(jq -r '
        (.knowledge.insights // [] | length) +
        (.knowledge.builtItems // [] | length) +
        (.knowledge.mathlibGaps // [] | length) +
        (.knowledge.nextSteps // [] | length)
    ' "$problem_file" 2>/dev/null || echo "0")
    
    echo "$score"
}

# Get knowledge tier from score
get_knowledge_tier() {
    local score="$1"
    if [[ $score -eq 0 ]]; then
        echo "EMPTY"
    elif [[ $score -le 5 ]]; then
        echo "WEAK"
    elif [[ $score -le 15 ]]; then
        echo "MODERATE"
    else
        echo "RICH"
    fi
}

# Claim a specific problem
claim_problem() {
    local problem_id="$1"
    local lock_dir="$CLAIMS_DIR/${problem_id}.lock"
    local claim_file="$CLAIMS_DIR/${problem_id}.json"

    # Check if problem exists in pool
    if ! jq -e ".candidates[] | select(.id == \"$problem_id\")" "$POOL_FILE" > /dev/null 2>&1; then
        echo "Error: Problem '$problem_id' not found in candidate pool" >&2
        return 1
    fi

    # Check if already completed
    local status
    status=$(jq -r ".candidates[] | select(.id == \"$problem_id\") | .status" "$POOL_FILE")
    if [[ "$status" == "completed" ]]; then
        echo "Error: Problem '$problem_id' already completed" >&2
        return 1
    fi

    get_timestamps
    local knowledge_score
    knowledge_score=$(get_knowledge_score "$problem_id")
    local knowledge_tier
    knowledge_tier=$(get_knowledge_tier "$knowledge_score")

    # Try atomic claim with mkdir
    if mkdir "$lock_dir" 2>/dev/null; then
        # Successfully acquired lock
        cat > "$claim_file" << EOF
{
  "problem_id": "$problem_id",
  "agent_id": "$AGENT_ID",
  "claimed_at": "$CLAIMED_AT",
  "expires_at": "$EXPIRES_AT",
  "ttl_minutes": $TTL_MINUTES,
  "knowledge_score": $knowledge_score,
  "knowledge_tier": "$knowledge_tier"
}
EOF
        echo "Claimed $problem_id by $AGENT_ID"
        echo "Knowledge score: $knowledge_score ($knowledge_tier)"
        echo "Expires: $EXPIRES_AT"
        return 0
    else
        # Lock exists - check if stale
        if is_claim_expired "$claim_file"; then
            echo "Stale claim detected, reclaiming..."
            rm -rf "$lock_dir"
            rm -f "$claim_file"

            # Retry
            if mkdir "$lock_dir" 2>/dev/null; then
                cat > "$claim_file" << EOF
{
  "problem_id": "$problem_id",
  "agent_id": "$AGENT_ID",
  "claimed_at": "$CLAIMED_AT",
  "expires_at": "$EXPIRES_AT",
  "ttl_minutes": $TTL_MINUTES,
  "knowledge_score": $knowledge_score,
  "knowledge_tier": "$knowledge_tier"
}
EOF
                echo "Claimed $problem_id by $AGENT_ID"
                echo "Knowledge score: $knowledge_score ($knowledge_tier)"
                echo "Expires: $EXPIRES_AT"
                return 0
            fi
        fi

        local existing_agent
        existing_agent=$(jq -r '.agent_id' "$claim_file" 2>/dev/null || echo "unknown")
        echo "Error: $problem_id already claimed by $existing_agent" >&2
        return 1
    fi
}

# Claim a random problem (prioritized by knowledge score)
claim_random_problem() {
    # Get available problems sorted by knowledge score (ascending)
    local available=()
    local scores=()
    
    while IFS= read -r problem_id; do
        [[ -z "$problem_id" ]] && continue
        
        # Skip if currently claimed (and not expired)
        local lock_dir="$CLAIMS_DIR/${problem_id}.lock"
        local claim_file="$CLAIMS_DIR/${problem_id}.json"
        if [[ -d "$lock_dir" ]] && ! is_claim_expired "$claim_file"; then
            continue
        fi
        
        local score
        score=$(get_knowledge_score "$problem_id")
        available+=("$problem_id")
        scores+=("$score")
    done < <(jq -r '.candidates[] | select(.status != "completed" and .status != "blocked") | .id' "$POOL_FILE" 2>/dev/null)

    if [[ ${#available[@]} -eq 0 ]]; then
        echo "No available problems to claim" >&2
        return 1
    fi

    # Find problems with lowest knowledge score
    local min_score=999999
    for score in "${scores[@]}"; do
        if [[ $score -lt $min_score ]]; then
            min_score=$score
        fi
    done

    # Collect all problems with min score
    local candidates=()
    for i in "${!available[@]}"; do
        if [[ ${scores[$i]} -eq $min_score ]]; then
            candidates+=("${available[$i]}")
        fi
    done

    # Pick random from candidates with lowest score
    local random_index=$((RANDOM % ${#candidates[@]}))
    local selected="${candidates[$random_index]}"

    echo "Selected $selected (${#available[@]} available, ${#candidates[@]} with lowest knowledge)"

    # Claim it
    claim_problem "$selected"
}

# Release a claim
release_problem() {
    local problem_id="$1"
    local lock_dir="$CLAIMS_DIR/${problem_id}.lock"
    local claim_file="$CLAIMS_DIR/${problem_id}.json"

    if [[ -d "$lock_dir" ]]; then
        rm -rf "$lock_dir"
        rm -f "$claim_file"
        echo "Released $problem_id"
    else
        echo "Warning: No claim found for $problem_id" >&2
    fi
}

# Update problem status in pool
update_problem_status() {
    local problem_id="$1"
    local new_status="$2"

    local tmp_file
    tmp_file=$(mktemp)
    jq "(.candidates[] | select(.id == \"$problem_id\")).status = \"$new_status\"" "$POOL_FILE" > "$tmp_file"
    mv "$tmp_file" "$POOL_FILE"

    echo "Updated $problem_id status to: $new_status"
}

# Show status
show_status() {
    echo "=== Research Problem Claims ==="
    echo ""

    local active_count=0
    local stale_count=0

    for lock_dir in "$CLAIMS_DIR"/*.lock; do
        [[ ! -d "$lock_dir" ]] && continue

        local problem_id
        problem_id=$(basename "$lock_dir" .lock)
        local claim_file="$CLAIMS_DIR/${problem_id}.json"

        if [[ -f "$claim_file" ]]; then
            local agent expires knowledge_tier status_label
            agent=$(jq -r '.agent_id' "$claim_file")
            expires=$(jq -r '.expires_at' "$claim_file")
            knowledge_tier=$(jq -r '.knowledge_tier // "UNKNOWN"' "$claim_file")

            if is_claim_expired "$claim_file"; then
                status_label="STALE"
                ((stale_count++))
            else
                status_label="active"
                ((active_count++))
            fi

            echo "  $problem_id: $agent ($status_label, $knowledge_tier, expires: $expires)"
        fi
    done

    if [[ $active_count -eq 0 && $stale_count -eq 0 ]]; then
        echo "  (no active claims)"
    fi

    echo ""

    # Show pool statistics
    if [[ -f "$POOL_FILE" ]]; then
        echo "=== Pool Status ==="
        jq -r '.candidates | group_by(.status) | map({status: .[0].status, count: length}) | .[] | "  \(.status): \(.count)"' "$POOL_FILE" 2>/dev/null || echo "  (unable to read pool)"
    fi

    echo ""
    echo "Active claims: $active_count"
    echo "Stale claims: $stale_count"
}

# Cleanup stale claims
cleanup_claims() {
    local cleaned=0

    for lock_dir in "$CLAIMS_DIR"/*.lock; do
        [[ ! -d "$lock_dir" ]] && continue

        local problem_id
        problem_id=$(basename "$lock_dir" .lock)
        local claim_file="$CLAIMS_DIR/${problem_id}.json"

        if is_claim_expired "$claim_file"; then
            rm -rf "$lock_dir"
            rm -f "$claim_file"
            echo "Cleaned up stale claim: $problem_id"
            ((cleaned++))
        fi
    done

    if [[ $cleaned -eq 0 ]]; then
        echo "No stale claims to clean up"
    else
        echo "Cleaned up $cleaned stale claims"
    fi
}

# Extend a claim
extend_claim() {
    local problem_id="$1"
    local claim_file="$CLAIMS_DIR/${problem_id}.json"

    if [[ ! -f "$claim_file" ]]; then
        echo "Error: No claim found for $problem_id" >&2
        return 1
    fi

    local current_agent
    current_agent=$(jq -r '.agent_id' "$claim_file")

    if [[ "$current_agent" != "$AGENT_ID" ]]; then
        echo "Error: Claim belongs to $current_agent, not $AGENT_ID" >&2
        return 1
    fi

    get_timestamps

    local tmp_file
    tmp_file=$(mktemp)
    jq ".expires_at = \"$EXPIRES_AT\"" "$claim_file" > "$tmp_file"
    mv "$tmp_file" "$claim_file"

    echo "Extended claim for $problem_id (new expires: $EXPIRES_AT)"
}

# Main command dispatch
case "${1:-help}" in
    claim)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 claim <problem-id>" >&2
            exit 1
        fi
        claim_problem "$2"
        ;;
    claim-random)
        claim_random_problem
        ;;
    release)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 release <problem-id>" >&2
            exit 1
        fi
        release_problem "$2"
        ;;
    update)
        if [[ -z "${2:-}" || -z "${3:-}" ]]; then
            echo "Usage: $0 update <problem-id> <status>" >&2
            exit 1
        fi
        update_problem_status "$2" "$3"
        ;;
    extend)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 extend <problem-id>" >&2
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
Research Problem Claiming System

Provides atomic claiming for parallel research agents.

Commands:
  claim <problem-id>         Claim a specific problem
  claim-random               Claim random problem (knowledge-prioritized)
  release <problem-id>       Release a claimed problem
  update <problem-id> <status>  Update problem status in pool
  extend <problem-id>        Extend claim TTL
  status                     Show all claims and pool status
  cleanup                    Remove stale claims
  help                       Show this help

Environment Variables:
  RESEARCHER_ID   Agent identifier (default: researcher-PID)
  CLAIM_TTL       Claim time-to-live in minutes (default: 90)

Knowledge Tiers (lower = higher priority):
  EMPTY (0)      - No knowledge yet
  WEAK (1-5)     - Little exploration
  MODERATE (6-15) - Some work done
  RICH (16+)     - Well explored

Examples:
  RESEARCHER_ID=agent-1 ./claim-problem.sh claim-random
  RESEARCHER_ID=agent-1 ./claim-problem.sh update weak-goldbach in-progress
  ./claim-problem.sh status
EOF
        ;;
    *)
        echo "Unknown command: $1" >&2
        echo "Run '$0 help' for usage" >&2
        exit 1
        ;;
esac
