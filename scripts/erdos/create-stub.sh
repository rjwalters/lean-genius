#!/bin/bash
#
# create-stub.sh - Create a new Erdős problem stub from scraped data
#
# Usage:
#   ./create-stub.sh <erdos-number>     Create stub for specific problem
#   ./create-stub.sh --list-missing     List all missing problem numbers
#   ./create-stub.sh --random-missing   Output a random missing problem number
#
# Creates:
#   - src/data/proofs/erdos-{N}/meta.json
#   - src/data/proofs/erdos-{N}/annotations.json
#   - src/data/proofs/erdos-{N}/index.ts
#   - proofs/Proofs/Erdos{N}Problem.lean

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
ENRICHED_PROBLEMS="$REPO_ROOT/scripts/erdos/data/enriched-problems.json"
GALLERY_DIR="$REPO_ROOT/src/data/proofs"
PROOFS_DIR="$REPO_ROOT/proofs/Proofs"
FORMAL_CONJECTURES="$REPO_ROOT/external/formal-conjectures/FormalConjectures/ErdosProblems"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

print_error() { echo -e "${RED}✗ $1${NC}" >&2; }
print_success() { echo -e "${GREEN}✓ $1${NC}"; }
print_info() { echo -e "${BLUE}ℹ $1${NC}"; }

# Get list of missing problem numbers
get_missing_problems() {
    local all_problems existing_stubs
    all_problems=$(jq -r '.[].number' "$ENRICHED_PROBLEMS" | sort -n)
    existing_stubs=$(ls -d "$GALLERY_DIR"/erdos-*/ 2>/dev/null | sed 's/.*erdos-//' | sed 's/\///' | grep '^[0-9]*$' | sort -n || true)
    comm -23 <(echo "$all_problems") <(echo "$existing_stubs")
}

# Check if problem exists in enriched data
problem_exists() {
    local num="$1"
    jq -e ".[] | select(.number == $num)" "$ENRICHED_PROBLEMS" > /dev/null 2>&1
}

# Get problem data from enriched-problems.json
get_problem_data() {
    local num="$1"
    jq ".[] | select(.number == $num)" "$ENRICHED_PROBLEMS"
}

# Create the stub directory structure
create_stub() {
    local num="$1"
    local gallery_path="$GALLERY_DIR/erdos-$num"
    local proof_file="$PROOFS_DIR/Erdos${num}Problem.lean"

    # Check if already exists
    if [[ -d "$gallery_path" ]]; then
        print_error "Stub already exists: $gallery_path"
        return 1
    fi

    # Check if problem exists in source data
    if ! problem_exists "$num"; then
        print_error "Problem #$num not found in enriched-problems.json"
        return 1
    fi

    print_info "Creating stub for Erdős Problem #$num..."

    # Get problem data
    local problem_data
    problem_data=$(get_problem_data "$num")

    local title status statement tags
    title=$(echo "$problem_data" | jq -r '.title // "Erdős Problem #\(.number)"')
    status=$(echo "$problem_data" | jq -r '.status // "open"' | tr '[:upper:]' '[:lower:]')
    statement=$(echo "$problem_data" | jq -r '.statement // .htmlStatement // "Problem statement pending."' | head -c 500)
    tags=$(echo "$problem_data" | jq -c '.tags // ["erdos"]')

    # Create gallery directory
    mkdir -p "$gallery_path"

    # Create meta.json
    cat > "$gallery_path/meta.json" << EOF
{
  "id": "erdos-$num",
  "title": "Erdős Problem #$num: $title",
  "slug": "erdos-$num",
  "description": "$(echo "$statement" | tr '\n' ' ' | sed 's/"/\\"/g' | head -c 200)",
  "meta": {
    "author": "Erdős",
    "sourceUrl": "https://erdosproblems.com/$num",
    "status": "stub",
    "proofRepoPath": "Proofs/Erdos${num}Problem.lean",
    "tags": $tags,
    "badge": "stub",
    "sorries": 1,
    "erdosNumber": $num,
    "erdosUrl": "https://erdosproblems.com/$num",
    "erdosProblemStatus": "$status"
  },
  "overview": {
    "historicalContext": "This is a stub entry for Erdős Problem #$num. The problem was posed by Paul Erdős. Full historical context pending enhancement.",
    "problemStatement": "$(echo "$statement" | tr '\n' ' ' | sed 's/"/\\"/g')",
    "proofStrategy": "Pending enhancement.",
    "keyInsights": ["Pending enhancement"]
  },
  "sections": [],
  "conclusion": {
    "summary": "Stub entry - enhancement needed.",
    "implications": "Pending.",
    "openQuestions": []
  }
}
EOF

    # Create minimal annotations.json
    cat > "$gallery_path/annotations.json" << EOF
[
  {
    "id": "erdos-$num-stub",
    "proofId": "erdos-$num",
    "type": "context",
    "range": { "startLine": 1, "endLine": 10 },
    "title": "Stub Entry",
    "content": "This is a stub entry for Erdős Problem #$num. Enhancement needed to add proper formalization and annotations.",
    "significance": "supporting"
  }
]
EOF

    # Create index.ts
    cat > "$gallery_path/index.ts" << EOF
import meta from './meta.json'
import annotations from './annotations.json'

export { meta, annotations }
EOF

    # Create Lean proof file if it doesn't exist
    if [[ ! -f "$proof_file" ]]; then
        # Check if formal-conjectures has this problem
        local fc_file="$FORMAL_CONJECTURES/$num.lean"
        if [[ -f "$fc_file" ]]; then
            print_info "Using formal-conjectures source for Lean file"
            # Copy and adapt formal-conjectures file
            cat > "$proof_file" << EOF
/-
Erdős Problem #$num

$statement

Reference: https://erdosproblems.com/$num
-/

import Mathlib

-- Adapted from formal-conjectures
-- TODO: Enhance with proper formalization

$(cat "$fc_file" | grep -v '^import' | grep -v '^/-' | head -100)

-- Placeholder for main result
theorem erdos_${num}_placeholder : True := trivial
EOF
        else
            # Create placeholder Lean file
            cat > "$proof_file" << EOF
/-
Erdős Problem #$num

$statement

Reference: https://erdosproblems.com/$num
-/

import Mathlib

-- TODO: Add proper formalization
-- This is a placeholder stub

/-- Placeholder theorem for Erdős Problem #$num -/
theorem erdos_${num}_placeholder : True := trivial
EOF
        fi
    fi

    print_success "Created stub for Erdős Problem #$num"
    echo "  Gallery: $gallery_path"
    echo "  Proof: $proof_file"
}

# Main command dispatch
case "${1:-}" in
    --list-missing)
        get_missing_problems
        ;;
    --random-missing)
        missing=$(get_missing_problems)
        if [[ -z "$missing" ]]; then
            print_error "No missing problems found"
            exit 1
        fi
        echo "$missing" | shuf | head -1
        ;;
    --count-missing)
        get_missing_problems | wc -l | tr -d ' '
        ;;
    --help|-h)
        cat << EOF
Create Erdős Problem Stubs

Creates new gallery stubs from scraped erdosproblems.com data.

Usage:
  ./create-stub.sh <number>         Create stub for problem #N
  ./create-stub.sh --list-missing   List all missing problem numbers
  ./create-stub.sh --random-missing Output one random missing number
  ./create-stub.sh --count-missing  Count missing problems
  ./create-stub.sh --help           Show this help

Examples:
  ./create-stub.sh 42               Create stub for problem #42
  ./create-stub.sh --list-missing | head -10   First 10 missing

The script uses data from scripts/erdos/data/enriched-problems.json
EOF
        ;;
    [0-9]*)
        create_stub "$1"
        ;;
    *)
        print_error "Usage: $0 <erdos-number> | --list-missing | --random-missing"
        exit 1
        ;;
esac
