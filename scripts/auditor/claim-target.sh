#!/bin/bash
#
# claim-target.sh - Claim a proof gallery entry for exclusive audit work
#
# Usage:
#   ./claim-target.sh claim-next            # Claim the highest-priority unclaimed target
#   ./claim-target.sh claim <id>            # Claim a specific entry
#   ./claim-target.sh complete <id> [clean|issues-found|issues-fixed]  # Mark as completed
#   ./claim-target.sh release <id>          # Release a claimed entry
#   ./claim-target.sh status                # Show all claims
#   ./claim-target.sh cleanup               # Remove stale claims
#
# Environment:
#   AUDITOR_ID  - Agent identifier (default: auditor-PID)
#   CLAIM_TTL   - Claim time-to-live in minutes (default: 60)

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
CLAIMS_DIR="$REPO_ROOT/.lean/state/audit-claims"
TRACKER_FILE="$REPO_ROOT/src/data/proofs/audit-tracker.json"
FIND_TARGETS="$REPO_ROOT/scripts/auditor/find-targets.ts"

# Defaults
TTL_MINUTES="${CLAIM_TTL:-60}"
AGENT_ID="${AUDITOR_ID:-auditor-$$}"

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

# Complete an audit and update tracker
do_complete() {
    local id="$1"
    local result="${2:-clean}"
    local claim_file="$CLAIMS_DIR/$id.json"

    # Update tracker
    python3 -c "
import json
from datetime import datetime, timezone

tracker_file = '$TRACKER_FILE'
with open(tracker_file) as f:
    tracker = json.load(f)

entry = tracker['entries'].get('$id', {
    'auditCount': 0,
    'lastAudited': None,
    'result': None,
    'issues': []
})
entry['auditCount'] = entry.get('auditCount', 0) + 1
entry['lastAudited'] = datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')
entry['result'] = '$result'
tracker['entries']['$id'] = entry

with open(tracker_file, 'w') as f:
    json.dump(tracker, f, indent=2, ensure_ascii=False)
    f.write('\n')
"

    # Remove claim
    rm -f "$claim_file"
    echo "Completed audit of $id (result: $result)"
}

# Release a claim without completing
do_release() {
    local id="$1"
    rm -f "$CLAIMS_DIR/$id.json"
    echo "Released claim on $id"
}

# Show all active claims
do_status() {
    echo "Active audit claims:"
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
            rm -f "$claim_file"
            removed=$((removed + 1))
        fi
    done
    echo "Cleaned up $removed expired claims"
}

# Main dispatch
case "${1:-help}" in
    claim-next) do_claim_next ;;
    claim)      do_claim "${2:?Usage: claim-target.sh claim <id>}" ;;
    complete)   do_complete "${2:?Usage: claim-target.sh complete <id> [result]}" "${3:-clean}" ;;
    release)    do_release "${2:?Usage: claim-target.sh release <id>}" ;;
    status)     do_status ;;
    cleanup)    do_cleanup ;;
    help|*)
        echo "Usage: claim-target.sh {claim-next|claim <id>|complete <id> [result]|release <id>|status|cleanup}"
        ;;
esac
