#!/bin/bash
#
# migrate-completed.sh - Migrate completed.json from array to object format
#
# Old format: {"completed": [7, 8, 9, ...]}
# New format: {"completed": {"7": {"status": "quality", ...}, "8": {...}}}
#
# Usage:
#   ./migrate-completed.sh           # Migrate in place (creates backup)
#   ./migrate-completed.sh --dry-run # Preview without writing

set -euo pipefail

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
COMPLETED_FILE="$REPO_ROOT/research/stub-claims/completed.json"
HAS_QUALITY_ISSUES="$REPO_ROOT/scripts/erdos/has-quality-issues.sh"
DRY_RUN=false

if [[ "${1:-}" == "--dry-run" ]]; then
    DRY_RUN=true
fi

if [[ ! -f "$COMPLETED_FILE" ]]; then
    echo "Error: $COMPLETED_FILE not found" >&2
    exit 1
fi

# Check if already migrated (object format)
if jq -e '.completed | type == "object"' "$COMPLETED_FILE" > /dev/null 2>&1; then
    echo "Already in object format, nothing to migrate."
    exit 0
fi

# Check it's in array format
if ! jq -e '.completed | type == "array"' "$COMPLETED_FILE" > /dev/null 2>&1; then
    echo "Error: Unexpected format in completed.json" >&2
    exit 1
fi

# Backup
if ! $DRY_RUN; then
    backup="$COMPLETED_FILE.backup-$(date +%s)"
    cp "$COMPLETED_FILE" "$backup"
    echo "Backup: $backup"
fi

# Build new format
total=$(jq '.completed | length' "$COMPLETED_FILE")
echo "Migrating $total entries..."

quality_count=0
needs_work_count=0

new_json='{"completed":{}}'

while IFS= read -r num; do
    [[ -z "$num" ]] && continue

    if "$HAS_QUALITY_ISSUES" "$num" 2>/dev/null; then
        status="needs-work"
        ((needs_work_count++))
    else
        status="quality"
        ((quality_count++))
    fi

    new_json=$(echo "$new_json" | jq \
        --arg num "$num" \
        --arg status "$status" \
        '.completed[$num] = {"status": $status, "enhanced_at": "2026-01-27T00:00:00Z", "agent": "legacy", "issues": []}')

done < <(jq -r '.completed[]' "$COMPLETED_FILE")

if $DRY_RUN; then
    echo ""
    echo "DRY RUN - would write:"
    echo "  Quality: $quality_count"
    echo "  Needs work: $needs_work_count"
    echo "  Total: $total"
    echo ""
    echo "Preview (first 5 entries):"
    echo "$new_json" | jq '.completed | to_entries[:5]'
else
    echo "$new_json" | jq '.' > "$COMPLETED_FILE"
    echo ""
    echo "Migration complete:"
    echo "  Quality: $quality_count"
    echo "  Needs work: $needs_work_count"
    echo "  Total: $(jq '.completed | length' "$COMPLETED_FILE")"
fi
