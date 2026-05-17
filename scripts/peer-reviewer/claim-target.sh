#!/bin/bash
#
# claim-target.sh - Claim a proof gallery entry for exclusive peer review
#
# Usage:
#   ./claim-target.sh --dry-run claim-next  # Preview the next claim without writing
#   ./claim-target.sh claim-next            # Claim the highest-priority unclaimed target
#   ./claim-target.sh claim <id>            # Claim a specific entry
#   ./claim-target.sh complete <id> [grade] # Mark as completed with overall grade
#   ./claim-target.sh release <id>          # Release a claimed entry
#   ./claim-target.sh status                # Show all claims
#   ./claim-target.sh cleanup               # Remove stale claims
#
# Environment:
#   REVIEWER_ID  - Agent identifier (default: peer-reviewer-PID)
#   CLAIM_TTL    - Claim time-to-live in minutes (default: 120)

set -euo pipefail
shopt -s nullglob

usage() {
    cat <<EOF
Usage: claim-target.sh [--dry-run] {claim-next|claim <id>|complete <id> [grade]|release <id>|status|cleanup}

Options:
  --dry-run, -n  Preview claim/tracker changes without writing files
  --help, -h     Show this help message

Commands:
  claim-next            Claim the highest-priority unclaimed target
  claim <id>            Claim a specific entry
  complete <id> [grade] Mark as completed with overall grade
  release <id>          Release a claimed entry
  status                Show all active claims
  cleanup               Remove stale claims
EOF
}

DRY_RUN=false
ARGS=()

for arg in "$@"; do
    case "$arg" in
        --dry-run|-n)
            DRY_RUN=true
            ;;
        --help|-h)
            usage
            exit 0
            ;;
        *)
            ARGS+=("$arg")
            ;;
    esac
done

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
CLAIMS_DIR="$REPO_ROOT/.lean/state/peer-review-claims"
TRACKER_FILE="$REPO_ROOT/src/data/proofs/review-tracker.json"
FIND_TARGETS="$REPO_ROOT/scripts/peer-reviewer/find-targets.ts"

# Defaults — longer TTL than auditor since reviews take more time
TTL_MINUTES="${CLAIM_TTL:-120}"
AGENT_ID="${REVIEWER_ID:-peer-reviewer-$$}"

# Ensure claims directory exists
if [[ "$DRY_RUN" != "true" ]]; then
    mkdir -p "$CLAIMS_DIR"
fi

# Initialize tracker if missing
if [[ "$DRY_RUN" != "true" && ! -f "$TRACKER_FILE" ]]; then
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

# Check if a claim is still valid (not expired)
is_claim_valid() {
    local claim_file="$1"
    if [[ ! -f "$claim_file" ]]; then
        return 1
    fi
    local expires
    expires=$(python3 -c "import json; print(json.load(open('$claim_file'))['expiresAt'])")
    local now
    now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    [[ "$now" < "$expires" ]]
}

# Claim a specific target
do_claim() {
    local id="$1"
    local claim_file="$CLAIMS_DIR/$id.json"

    # Check if already claimed by someone else
    if is_claim_valid "$claim_file" 2>/dev/null; then
        local owner
        owner=$(python3 -c "import json; print(json.load(open('$claim_file'))['agentId'])")
        echo "Already claimed by $owner" >&2
        return 1
    fi

    get_timestamps
    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Would claim $id"
        echo "  Claim file: $claim_file"
        echo "  Agent: $AGENT_ID"
        echo "  Expires: $EXPIRES_AT"
        return 0
    fi

    python3 -c "
import json
claim = {
    'proofId': '$id',
    'agentId': '$AGENT_ID',
    'claimedAt': '$CLAIMED_AT',
    'expiresAt': '$EXPIRES_AT'
}
with open('$claim_file', 'w') as f:
    json.dump(claim, f, indent=2)
"
    echo "$id"
}

# Claim the next highest-priority unclaimed target
do_claim_next() {
    # Get all targets sorted by priority
    local targets
    targets=$(npx tsx "$FIND_TARGETS" --json 2>/dev/null || echo "[]")

    # Find first unclaimed
    local id
    id=$(python3 -c "
import json, os
targets = json.loads('''$targets''')
claims_dir = '$CLAIMS_DIR'
for t in targets:
    claim_file = os.path.join(claims_dir, t['id'] + '.json')
    if os.path.exists(claim_file):
        try:
            claim = json.load(open(claim_file))
            import datetime
            expires = datetime.datetime.fromisoformat(claim['expiresAt'].replace('Z', '+00:00'))
            if datetime.datetime.now(datetime.timezone.utc) < expires:
                continue  # Still claimed
        except:
            pass
    print(t['id'])
    break
" 2>/dev/null)

    if [[ -z "$id" ]]; then
        echo "No unclaimed targets available" >&2
        return 1
    fi

    do_claim "$id"
}

# Complete a review and update tracker
do_complete() {
    local id="$1"
    local grade="${2:-ungraded}"
    local claim_file="$CLAIMS_DIR/$id.json"

    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Would update tracker: $TRACKER_FILE"
        echo "  Proof: $id"
        echo "  Grade: $grade"
        echo "Would remove claim file: $claim_file"
        return 0
    fi

    # Update tracker
    python3 -c "
import json
from datetime import datetime, timezone

tracker_file = '$TRACKER_FILE'
with open(tracker_file) as f:
    tracker = json.load(f)

entry = tracker['entries'].get('$id', {
    'reviewCount': 0,
    'lastReviewed': None,
    'overallGrade': None,
    'qualityScore': None,
    'actionItems': 0,
    'resolvedItems': 0
})
entry['reviewCount'] = entry.get('reviewCount', 0) + 1
entry['lastReviewed'] = datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
entry['overallGrade'] = '$grade'
tracker['entries']['$id'] = entry

with open(tracker_file, 'w') as f:
    json.dump(tracker, f, indent=2)
"

    # Remove claim
    rm -f "$claim_file"
    echo "Completed review of $id (grade: $grade)"
}

# Release a claim without completing
do_release() {
    local id="$1"
    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Would remove claim file: $CLAIMS_DIR/$id.json"
        return 0
    fi
    rm -f "$CLAIMS_DIR/$id.json"
    echo "Released claim on $id"
}

# Show all active claims
do_status() {
    echo "Active peer review claims:"
    local count=0
    for claim_file in "$CLAIMS_DIR"/*.json; do
        if is_claim_valid "$claim_file" 2>/dev/null; then
            python3 -c "
import json
c = json.load(open('$claim_file'))
print(f\"  {c['proofId']} -> {c['agentId']} (expires {c['expiresAt']})\")
"
            count=$((count + 1))
        fi
    done
    echo "Total: $count active claims"
}

# Remove expired claims
do_cleanup() {
    local removed=0
    for claim_file in "$CLAIMS_DIR"/*.json; do
        if ! is_claim_valid "$claim_file" 2>/dev/null; then
            if [[ "$DRY_RUN" == "true" ]]; then
                echo "Would remove expired claim: $claim_file"
            else
                rm -f "$claim_file"
            fi
            removed=$((removed + 1))
        fi
    done
    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Would clean up $removed expired claims"
        return 0
    fi
    echo "Cleaned up $removed expired claims"
}

# Main dispatch
case "${ARGS[0]:-help}" in
    claim-next) do_claim_next ;;
    claim)      do_claim "${ARGS[1]:?Usage: claim-target.sh claim <id>}" ;;
    complete)   do_complete "${ARGS[1]:?Usage: claim-target.sh complete <id> [grade]}" "${ARGS[2]:-ungraded}" ;;
    release)    do_release "${ARGS[1]:?Usage: claim-target.sh release <id>}" ;;
    status)     do_status ;;
    cleanup)    do_cleanup ;;
    help)
        usage
        ;;
    *)
        usage >&2
        exit 1
        ;;
esac
