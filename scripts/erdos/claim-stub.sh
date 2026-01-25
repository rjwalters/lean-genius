#!/bin/bash
#
# claim-stub.sh - Claim an Erdős stub for exclusive enhancement work
#
# Usage:
#   ./claim-stub.sh claim <erdos-number>     # Claim a specific stub
#   ./claim-stub.sh claim-random             # Claim a random unclaimed stub
#   ./claim-stub.sh claim-random-any         # Claim any stub (including unsourced)
#   ./claim-stub.sh claim-missing            # Create and claim a missing problem
#   ./claim-stub.sh claim-any                # Try existing, then create missing
#   ./claim-stub.sh release <erdos-number>   # Release a claimed stub
#   ./claim-stub.sh complete <erdos-number>  # Mark as completed and release
#   ./claim-stub.sh status                   # Show all claims
#   ./claim-stub.sh cleanup                  # Remove stale claims
#
# Environment:
#   ENHANCER_ID - Agent identifier (default: enhancer-PID)
#   CLAIM_TTL   - Claim time-to-live in minutes (default: 60)

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
CLAIMS_DIR="$REPO_ROOT/research/stub-claims"
COMPLETED_FILE="$CLAIMS_DIR/completed.json"
STUBS_SCRIPT="$REPO_ROOT/scripts/erdos/find-stubs.ts"

# Defaults
TTL_MINUTES="${CLAIM_TTL:-60}"
AGENT_ID="${ENHANCER_ID:-enhancer-$$}"

# Ensure claims directory exists
mkdir -p "$CLAIMS_DIR"

# Initialize completed file if missing
if [[ ! -f "$COMPLETED_FILE" ]]; then
    echo '{"completed": []}' > "$COMPLETED_FILE"
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
        return 0  # No claim file = "expired"
    fi

    local expires_at
    expires_at=$(jq -r '.expires_at' "$claim_file")

    local now_epoch
    local expires_epoch
    now_epoch=$(date -u +%s)

    if [[ "$(uname)" == "Darwin" ]]; then
        # Strip the Z suffix and parse as UTC
        # macOS date -j doesn't respect Z timezone suffix
        local stripped="${expires_at%Z}"
        expires_epoch=$(TZ=UTC date -j -f "%Y-%m-%dT%H:%M:%S" "$stripped" +%s 2>/dev/null || echo 0)
    else
        expires_epoch=$(date -d "$expires_at" +%s 2>/dev/null || echo 0)
    fi

    [[ $now_epoch -gt $expires_epoch ]]
}

# Claim a specific stub
claim_stub() {
    local erdos_number="$1"
    local lock_dir="$CLAIMS_DIR/erdos-$erdos_number.lock"
    local claim_file="$CLAIMS_DIR/erdos-$erdos_number.json"
    local worktree_path="$REPO_ROOT/.loom/worktrees/erdos-$erdos_number"
    local branch_name="feature/erdos-$erdos_number-enhance"

    # Check if already completed
    if jq -e ".completed | index($erdos_number)" "$COMPLETED_FILE" > /dev/null 2>&1; then
        echo "Error: Erdős #$erdos_number already completed" >&2
        return 1
    fi

    get_timestamps

    # Try atomic claim with mkdir
    if mkdir "$lock_dir" 2>/dev/null; then
        # Successfully acquired lock
        cat > "$claim_file" << EOF
{
  "erdos_number": $erdos_number,
  "agent_id": "$AGENT_ID",
  "claimed_at": "$CLAIMED_AT",
  "expires_at": "$EXPIRES_AT",
  "ttl_minutes": $TTL_MINUTES,
  "status": "in_progress",
  "worktree": "$worktree_path",
  "branch": "$branch_name"
}
EOF
        echo "Claimed erdos-$erdos_number by $AGENT_ID (expires: $EXPIRES_AT)"

        # Create or reuse problem-specific worktree
        setup_problem_worktree "$erdos_number"
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
  "erdos_number": $erdos_number,
  "agent_id": "$AGENT_ID",
  "claimed_at": "$CLAIMED_AT",
  "expires_at": "$EXPIRES_AT",
  "ttl_minutes": $TTL_MINUTES,
  "status": "in_progress",
  "worktree": "$worktree_path",
  "branch": "$branch_name"
}
EOF
                echo "Claimed erdos-$erdos_number by $AGENT_ID (expires: $EXPIRES_AT)"

                # Create or reuse problem-specific worktree
                setup_problem_worktree "$erdos_number"
                return 0
            fi
        fi

        local existing_agent
        existing_agent=$(jq -r '.agent_id' "$claim_file" 2>/dev/null || echo "unknown")
        echo "Error: erdos-$erdos_number already claimed by $existing_agent" >&2
        return 1
    fi
}

# Setup problem-specific worktree (creates new or reuses existing with partial work)
setup_problem_worktree() {
    local erdos_number="$1"
    local worktree_path="$REPO_ROOT/.loom/worktrees/erdos-$erdos_number"
    local branch_name="feature/erdos-$erdos_number-enhance"

    # Check if worktree already exists (has partial work from previous agent)
    if [[ -d "$worktree_path" ]]; then
        echo "Reusing existing worktree with partial work: $worktree_path"
        echo "Branch: $branch_name"

        # Update to latest main but keep local changes
        (cd "$worktree_path" && git fetch origin main 2>/dev/null) || true
        return 0
    fi

    # Check if branch exists on remote (previous work pushed)
    if git ls-remote --heads origin "$branch_name" 2>/dev/null | grep -q "$branch_name"; then
        echo "Found existing branch with partial work: $branch_name"
        git worktree add "$worktree_path" "$branch_name" 2>/dev/null || \
            git worktree add "$worktree_path" -b "$branch_name" "origin/$branch_name"
    else
        # Fresh start - create new worktree from main
        echo "Creating fresh worktree: $worktree_path"
        git worktree add "$worktree_path" -b "$branch_name" main 2>/dev/null || {
            # Branch might exist locally, try to reuse
            git worktree add "$worktree_path" "$branch_name" 2>/dev/null || {
                git branch -D "$branch_name" 2>/dev/null
                git worktree add "$worktree_path" -b "$branch_name" main
            }
        }
    fi

    # Symlink .lake for fast Lean builds
    if [[ -d "$REPO_ROOT/proofs/.lake" ]] && [[ -d "$worktree_path/proofs" ]]; then
        rm -rf "$worktree_path/proofs/.lake" 2>/dev/null
        ln -s "$REPO_ROOT/proofs/.lake" "$worktree_path/proofs/.lake"
    fi

    echo "Worktree ready: $worktree_path"
    echo "Branch: $branch_name"
}

# Claim a random unclaimed stub (sourced only, or any if --any flag)
claim_random_stub() {
    local include_unsourced="${1:-false}"

    # Get all stubs as JSON
    local stubs_json
    stubs_json=$(npx tsx "$STUBS_SCRIPT" --json 2>/dev/null)

    # Get stub numbers based on mode
    local stub_numbers
    if [[ "$include_unsourced" == "true" ]]; then
        # All stubs
        stub_numbers=$(echo "$stubs_json" | jq -r '.stubs[].erdosNumber')
    else
        # Only sourced stubs (easier to enhance)
        stub_numbers=$(echo "$stubs_json" | jq -r '.stubs[] | select(.hasFormalConjecturesSource == true) | .erdosNumber')
    fi

    # Get completed list
    local completed
    completed=$(jq -r '.completed[]' "$COMPLETED_FILE" 2>/dev/null || echo "")

    # Find unclaimed stubs
    local available=()
    while IFS= read -r num; do
        [[ -z "$num" ]] && continue

        # Skip if completed
        if echo "$completed" | grep -q "^$num$"; then
            continue
        fi

        # Skip if currently claimed (and not expired)
        local claim_file="$CLAIMS_DIR/erdos-$num.json"
        if [[ -d "$CLAIMS_DIR/erdos-$num.lock" ]] && ! is_claim_expired "$claim_file"; then
            continue
        fi

        available+=("$num")
    done <<< "$stub_numbers"

    if [[ ${#available[@]} -eq 0 ]]; then
        if [[ "$include_unsourced" == "true" ]]; then
            echo "No unclaimed stubs available" >&2
        else
            echo "No unclaimed stubs with sources available. Try 'claim-random-any' for unsourced stubs." >&2
        fi
        return 1
    fi

    # Pick random from available
    local random_index=$((RANDOM % ${#available[@]}))
    local selected="${available[$random_index]}"

    echo "Selected erdos-$selected (${#available[@]} available)"

    # Claim it
    claim_stub "$selected"
}

# Release a claim
release_stub() {
    local erdos_number="$1"
    local lock_dir="$CLAIMS_DIR/erdos-$erdos_number.lock"
    local claim_file="$CLAIMS_DIR/erdos-$erdos_number.json"

    if [[ -d "$lock_dir" ]]; then
        rm -rf "$lock_dir"
        rm -f "$claim_file"
        echo "Released erdos-$erdos_number"
    else
        echo "Warning: No claim found for erdos-$erdos_number" >&2
    fi
}

# Mark as completed and release
complete_stub() {
    local erdos_number="$1"

    # Add to completed list
    local tmp_file
    tmp_file=$(mktemp)
    jq ".completed += [$erdos_number] | .completed |= unique | .completed |= sort" "$COMPLETED_FILE" > "$tmp_file"
    mv "$tmp_file" "$COMPLETED_FILE"

    # Release the claim
    release_stub "$erdos_number"

    echo "Marked erdos-$erdos_number as completed"
}

# Show status
show_status() {
    echo "=== Stub Enhancement Claims ==="
    echo ""

    local active_count=0
    local stale_count=0

    for lock_dir in "$CLAIMS_DIR"/*.lock; do
        [[ ! -d "$lock_dir" ]] && continue

        local erdos_num
        erdos_num=$(basename "$lock_dir" .lock | sed 's/erdos-//')
        local claim_file="$CLAIMS_DIR/erdos-$erdos_num.json"

        if [[ -f "$claim_file" ]]; then
            local agent expires status
            agent=$(jq -r '.agent_id' "$claim_file")
            expires=$(jq -r '.expires_at' "$claim_file")

            if is_claim_expired "$claim_file"; then
                status="STALE"
                ((stale_count++))
            else
                status="active"
                ((active_count++))
            fi

            echo "  erdos-$erdos_num: $agent ($status, expires: $expires)"
        fi
    done

    if [[ $active_count -eq 0 && $stale_count -eq 0 ]]; then
        echo "  (no active claims)"
    fi

    echo ""

    # Show completed count
    local completed_count
    completed_count=$(jq '.completed | length' "$COMPLETED_FILE" 2>/dev/null || echo 0)
    echo "Completed: $completed_count stubs"
    echo "Active claims: $active_count"
    echo "Stale claims: $stale_count"
}

# Cleanup stale claims
cleanup_claims() {
    local cleaned=0

    for lock_dir in "$CLAIMS_DIR"/*.lock; do
        [[ ! -d "$lock_dir" ]] && continue

        local erdos_num
        erdos_num=$(basename "$lock_dir" .lock | sed 's/erdos-//')
        local claim_file="$CLAIMS_DIR/erdos-$erdos_num.json"

        if is_claim_expired "$claim_file"; then
            rm -rf "$lock_dir"
            rm -f "$claim_file"
            echo "Cleaned up stale claim: erdos-$erdos_num"
            ((cleaned++))
        fi
    done

    if [[ $cleaned -eq 0 ]]; then
        echo "No stale claims to clean up"
    else
        echo "Cleaned up $cleaned stale claims"
    fi
}

# Claim a missing problem (create stub and claim it)
claim_missing_stub() {
    local CREATE_STUB_SCRIPT="$REPO_ROOT/scripts/erdos/create-stub.sh"

    # Get a random missing problem number
    local missing_num
    missing_num=$("$CREATE_STUB_SCRIPT" --random-missing 2>/dev/null)

    if [[ -z "$missing_num" ]]; then
        echo "No missing problems available" >&2
        return 1
    fi

    echo "Selected missing problem: erdos-$missing_num"

    # Create the stub
    echo "Creating stub..."
    if ! "$CREATE_STUB_SCRIPT" "$missing_num"; then
        echo "Error: Failed to create stub for erdos-$missing_num" >&2
        return 1
    fi

    # Now claim it
    claim_stub "$missing_num"
}

# Claim any available work (existing stub OR create missing)
claim_any_work() {
    # First try to claim an existing stub
    if claim_random_stub "true" 2>/dev/null; then
        return 0
    fi

    echo "No existing stubs available, creating from missing problems..."

    # Fall back to creating a missing stub
    claim_missing_stub
}

# Extend a claim (renew TTL)
extend_claim() {
    local erdos_number="$1"
    local claim_file="$CLAIMS_DIR/erdos-$erdos_number.json"

    if [[ ! -f "$claim_file" ]]; then
        echo "Error: No claim found for erdos-$erdos_number" >&2
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

    echo "Extended claim for erdos-$erdos_number (new expires: $EXPIRES_AT)"
}

# Main command dispatch
case "${1:-help}" in
    claim)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 claim <erdos-number>" >&2
            exit 1
        fi
        claim_stub "$2"
        ;;
    claim-random)
        claim_random_stub "false"
        ;;
    claim-random-any)
        claim_random_stub "true"
        ;;
    claim-missing)
        claim_missing_stub
        ;;
    claim-any)
        claim_any_work
        ;;
    release)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 release <erdos-number>" >&2
            exit 1
        fi
        release_stub "$2"
        ;;
    complete)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 complete <erdos-number>" >&2
            exit 1
        fi
        complete_stub "$2"
        ;;
    extend)
        if [[ -z "${2:-}" ]]; then
            echo "Usage: $0 extend <erdos-number>" >&2
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
Erdős Stub Claiming System

Provides atomic claiming for parallel stub enhancement.

Commands:
  claim <erdos-number>    Claim a specific stub
  claim-random            Claim a random stub with formal-conjectures source
  claim-random-any        Claim a random stub (including unsourced)
  claim-missing           Create and claim a random MISSING problem
  claim-any               Try existing stubs first, then create missing if none
  release <erdos-number>  Release a claimed stub
  complete <erdos-number> Mark as completed and release
  extend <erdos-number>   Extend claim TTL
  status                  Show all claims
  cleanup                 Remove stale claims
  help                    Show this help

Environment Variables:
  ENHANCER_ID   Agent identifier (default: enhancer-PID)
  CLAIM_TTL     Claim time-to-live in minutes (default: 60)

Examples:
  ENHANCER_ID=agent-1 ./claim-stub.sh claim-random
  ENHANCER_ID=agent-1 ./claim-stub.sh complete 516
  ./claim-stub.sh status
EOF
        ;;
    *)
        echo "Unknown command: $1" >&2
        echo "Run '$0 help' for usage" >&2
        exit 1
        ;;
esac
