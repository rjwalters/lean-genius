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
#   ./claim-stub.sh claim-needs-work         # Claim a completed stub needing quality repair
#   ./claim-stub.sh release <erdos-number>   # Release a claimed stub
#   ./claim-stub.sh complete <erdos-number>  # Mark as completed (strict quality gate) and release
#   ./claim-stub.sh complete <erdos-number> --force  # Force completion despite quality issues
#   ./claim-stub.sh status                   # Show all claims with quality breakdown
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
HAS_QUALITY_ISSUES="$REPO_ROOT/scripts/erdos/has-quality-issues.sh"
COMPLETIONS_DIR="$REPO_ROOT/.loom/signals/completions"

# Defaults
TTL_MINUTES="${CLAIM_TTL:-60}"
AGENT_ID="${ENHANCER_ID:-enhancer-$$}"

# Ensure claims directory exists
mkdir -p "$CLAIMS_DIR"

# Initialize completed file if missing
if [[ ! -f "$COMPLETED_FILE" ]]; then
    echo '{"completed": {}}' > "$COMPLETED_FILE"
fi

# Detect completed.json format (array = legacy, object = new)
is_legacy_format() {
    jq -e '.completed | type == "array"' "$COMPLETED_FILE" > /dev/null 2>&1
}

# Check if a number is in the completed list (supports both formats)
is_completed() {
    local num="$1"
    if is_legacy_format; then
        jq -e ".completed | index($num)" "$COMPLETED_FILE" > /dev/null 2>&1
    else
        jq -e ".completed[\"$num\"]" "$COMPLETED_FILE" > /dev/null 2>&1
    fi
}

# Check if a completed entry needs work (new format only)
is_needs_work() {
    local num="$1"
    if is_legacy_format; then
        # In legacy format, fall back to has-quality-issues check
        "$HAS_QUALITY_ISSUES" "$num" 2>/dev/null
    else
        jq -e ".completed[\"$num\"].status == \"needs-work\"" "$COMPLETED_FILE" > /dev/null 2>&1
    fi
}

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
    if is_completed "$erdos_number"; then
        # Allow re-claiming if it still has quality issues
        if is_needs_work "$erdos_number" || "$HAS_QUALITY_ISSUES" "$erdos_number" 2>/dev/null; then
            echo "Re-claiming erdos-$erdos_number (completed but has quality issues)"
        else
            echo "Error: Erdős #$erdos_number already completed with no quality issues" >&2
            return 1
        fi
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

    # Find unclaimed stubs
    local available=()
    while IFS= read -r num; do
        [[ -z "$num" ]] && continue

        # Skip if completed AND has no quality issues
        if is_completed "$num"; then
            if ! is_needs_work "$num" && ! "$HAS_QUALITY_ISSUES" "$num" 2>/dev/null; then
                continue
            fi
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
    local force_flag="${2:-}"

    # Run quality check
    local status="quality"
    if "$HAS_QUALITY_ISSUES" "$erdos_number" 2>/dev/null; then
        if [[ "$force_flag" != "--force" ]]; then
            # STRICT MODE: Fail completion
            echo "ERROR: Cannot complete erdos-$erdos_number -- quality issues remain" >&2
            echo "" >&2
            echo "Quality issues detected:" >&2

            local lean_file="$REPO_ROOT/proofs/Proofs/Erdos${erdos_number}Problem.lean"
            local entry_dir="$REPO_ROOT/src/data/proofs/erdos-$erdos_number"

            if [[ ! -f "$lean_file" ]] || grep -q 'True := trivial' "$lean_file" 2>/dev/null; then
                echo "  - Placeholder proof (True := trivial)" >&2
            fi

            local annotations_file="$entry_dir/annotations.json"
            if [[ ! -f "$annotations_file" ]]; then
                echo "  - Missing annotations.json" >&2
            else
                local count
                count=$(python3 -c "import json; print(len(json.load(open('$annotations_file'))))" 2>/dev/null || echo "0")
                if [[ "$count" -lt 3 ]]; then
                    echo "  - Insufficient annotations ($count < 3)" >&2
                fi
            fi

            local meta_file="$entry_dir/meta.json"
            if [[ -f "$meta_file" ]] && grep -qE 'Forum|Favourites|Random Solved' "$meta_file" 2>/dev/null; then
                echo "  - Scraping garbage in meta.json" >&2
            fi

            echo "" >&2
            echo "Fix these issues and try again, or use:" >&2
            echo "  $0 complete $erdos_number --force" >&2
            return 1
        fi

        # Force mode: allow completion with needs-work status
        echo "WARNING: Forcing completion despite quality issues" >&2
        status="needs-work"
    fi

    get_timestamps

    local tmp_file
    tmp_file=$(mktemp)

    if is_legacy_format; then
        # Legacy array format - add to array
        jq ".completed += [$erdos_number] | .completed |= unique | .completed |= sort" "$COMPLETED_FILE" > "$tmp_file"
    else
        # New object format - add with metadata
        jq --arg num "$erdos_number" \
           --arg status "$status" \
           --arg enhanced_at "$CLAIMED_AT" \
           --arg agent "$AGENT_ID" \
           '.completed[$num] = {
               "status": $status,
               "enhanced_at": $enhanced_at,
               "agent": $agent,
               "issues": []
           }' "$COMPLETED_FILE" > "$tmp_file"
    fi

    mv "$tmp_file" "$COMPLETED_FILE"

    # Release the claim
    release_stub "$erdos_number"

    # Create completion signal for daemon stats tracking
    mkdir -p "$COMPLETIONS_DIR"
    touch "$COMPLETIONS_DIR/stub-enhanced-$erdos_number-$(date +%s)"

    echo "Marked erdos-$erdos_number as completed (status: $status)"
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

    # Show completed count with quality breakdown
    local completed_count
    completed_count=$(jq '.completed | length' "$COMPLETED_FILE" 2>/dev/null || echo 0)
    echo "Completed: $completed_count stubs"

    if ! is_legacy_format 2>/dev/null; then
        local quality_count needs_work_count
        quality_count=$(jq '[.completed[] | select(.status == "quality")] | length' "$COMPLETED_FILE" 2>/dev/null || echo "?")
        needs_work_count=$(jq '[.completed[] | select(.status == "needs-work")] | length' "$COMPLETED_FILE" 2>/dev/null || echo "?")
        echo "  Quality: $quality_count"
        echo "  Needs rework: $needs_work_count"
    fi

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

# Claim a completed stub that needs quality rework
claim_needs_work() {
    local needs_work=""

    if is_legacy_format; then
        # Legacy format: check each completed number for quality issues
        while IFS= read -r num; do
            [[ -z "$num" ]] && continue
            if "$HAS_QUALITY_ISSUES" "$num" 2>/dev/null; then
                # Skip if currently claimed
                if [[ -d "$CLAIMS_DIR/erdos-$num.lock" ]] && ! is_claim_expired "$CLAIMS_DIR/erdos-$num.json"; then
                    continue
                fi
                needs_work="$needs_work $num"
            fi
        done < <(jq -r '.completed[]' "$COMPLETED_FILE")
    else
        # New format: use status field
        while IFS= read -r num; do
            [[ -z "$num" ]] && continue
            # Skip if currently claimed
            if [[ -d "$CLAIMS_DIR/erdos-$num.lock" ]] && ! is_claim_expired "$CLAIMS_DIR/erdos-$num.json"; then
                continue
            fi
            needs_work="$needs_work $num"
        done < <(jq -r '.completed | to_entries[] | select(.value.status == "needs-work") | .key' "$COMPLETED_FILE")
    fi

    needs_work=$(echo "$needs_work" | xargs)  # trim

    if [[ -z "$needs_work" ]]; then
        echo "No completed stubs need rework" >&2
        return 1
    fi

    # Pick random from needs-work pool
    local count
    count=$(echo "$needs_work" | wc -w | xargs)
    local random_index=$(( RANDOM % count + 1 ))
    local selected
    selected=$(echo "$needs_work" | tr ' ' '\n' | sed -n "${random_index}p")

    echo "Selected erdos-$selected (needs quality repair, $count available)"
    claim_stub "$selected"
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
    claim-needs-work)
        claim_needs_work
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
            echo "Usage: $0 complete <erdos-number> [--force]" >&2
            exit 1
        fi
        complete_stub "$2" "${3:-}"
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
  claim <erdos-number>    Claim a specific stub (allows re-claiming broken completions)
  claim-random            Claim a random stub with formal-conjectures source
  claim-random-any        Claim a random stub (including unsourced)
  claim-missing           Create and claim a random MISSING problem
  claim-any               Try existing stubs first, then create missing if none
  claim-needs-work        Claim a completed stub that still has quality issues
  release <erdos-number>  Release a claimed stub
  complete <erdos-number> [--force]  Mark as completed (strict quality gate)
                                   Fails if quality issues remain unless --force
  extend <erdos-number>   Extend claim TTL
  status                  Show all claims with quality breakdown
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
