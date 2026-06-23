#!/bin/bash
#
# has-quality-issues.sh - Check if an Erdős entry has quality issues
#
# Usage:
#   ./has-quality-issues.sh <erdos-number>
#
# Exit codes:
#   0 - Entry has quality issues
#   1 - Entry has no quality issues (is clean)
#   2 - Error (invalid arguments, etc.)

set -euo pipefail

if [[ -z "${1:-}" ]]; then
    echo "Usage: $0 <erdos-number>" >&2
    exit 2
fi

ERDOS_NUM="$1"

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

REPO_ROOT="$(find_repo_root)"
GALLERY_DIR="$REPO_ROOT/src/data/proofs"
PROOFS_DIR="$REPO_ROOT/proofs/Proofs"

has_garbage_description() {
    local meta_file="$1"
    python3 - "$meta_file" <<'PY'
import json
import sys

artifacts = ('Forum', 'Favourites', 'Random Solved', 'Dual View', 'Random Open')
try:
    with open(sys.argv[1], encoding='utf-8') as fh:
        data = json.load(fh)
except Exception:
    sys.exit(1)

descriptions = []
if isinstance(data.get('description'), str):
    descriptions.append(data['description'])
overview = data.get('overview')
if isinstance(overview, dict) and isinstance(overview.get('text'), str):
    descriptions.append(overview['text'])

has_artifact = any(
    artifact in text
    for artifact in artifacts
    for text in descriptions
)
sys.exit(0 if has_artifact else 1)
PY
}

entry_dir="$GALLERY_DIR/erdos-$ERDOS_NUM"
lean_file="$PROOFS_DIR/Erdos${ERDOS_NUM}Problem.lean"

has_issues=false

# Check placeholder proof
if [[ ! -f "$lean_file" ]]; then
    has_issues=true
elif grep -q 'True := trivial\|True := by trivial' "$lean_file" 2>/dev/null; then
    has_issues=true
fi

# Check empty annotations
if [[ -d "$entry_dir" ]]; then
    annotations_file="$entry_dir/annotations.json"
    if [[ ! -f "$annotations_file" ]]; then
        has_issues=true
    else
        # Check if fewer than 3 entries
        entry_count=$(python3 -c "
import json, sys
try:
    data = json.load(open('$annotations_file'))
    count = len(data) if isinstance(data, list) else len(data.keys())
    print(count)
except:
    print(0)
" 2>/dev/null || echo "0")
        if [[ "$entry_count" -lt 3 ]]; then
            has_issues=true
        fi
    fi

    # Check garbage description
    meta_file="$entry_dir/meta.json"
    if [[ -f "$meta_file" ]]; then
        if has_garbage_description "$meta_file"; then
            has_issues=true
        fi
    fi
fi

if $has_issues; then
    exit 0
else
    exit 1
fi
