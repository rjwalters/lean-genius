#!/bin/bash
#
# find-candidates.sh - Find Lean files suitable for Aristotle submission
#
# Usage:
#   ./find-candidates.sh              # List all candidates
#   ./find-candidates.sh --count      # Just count candidates
#   ./find-candidates.sh --best N     # Top N candidates (fewest sorries)
#   ./find-candidates.sh --json       # Output as JSON
#
# Candidates are files that:
#   - Have theorem/lemma sorries (something to prove)
#   - Have NOT been submitted to Aristotle yet
#   - Preferably have no definition sorries (Aristotle skips these)
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
PROOFS_DIR="$PROJECT_ROOT/proofs/Proofs"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"

# Parse arguments
COUNT_ONLY=false
BEST_N=0
JSON_OUTPUT=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --count) COUNT_ONLY=true; shift ;;
        --best) BEST_N="$2"; shift 2 ;;
        --json) JSON_OUTPUT=true; shift ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# Get list of already-submitted files
get_submitted_files() {
    if [[ -f "$JOBS_FILE" ]]; then
        jq -r '.jobs[].file' "$JOBS_FILE" 2>/dev/null | xargs -I{} basename {} .lean | sort -u
    fi
}

# Analyze a single file
analyze_file() {
    local file="$1"
    local basename=$(basename "$file" .lean)

    # Count different types of sorries (tr -d to remove any whitespace/newlines)
    local total_sorry=$(grep -c "sorry" "$file" 2>/dev/null | tr -d '[:space:]' || echo 0)
    local def_sorry=$(grep -cE "^def.*:=.*sorry|^def.*sorry$" "$file" 2>/dev/null | tr -d '[:space:]' || echo 0)
    local axiom_count=$(grep -c "^axiom " "$file" 2>/dev/null | tr -d '[:space:]' || echo 0)

    # Ensure we have numbers
    [[ -z "$total_sorry" ]] && total_sorry=0
    [[ -z "$def_sorry" ]] && def_sorry=0
    [[ -z "$axiom_count" ]] && axiom_count=0

    # Theorem sorries = total - definition sorries (approximate)
    local thm_sorry=$((total_sorry - def_sorry))

    # Score: lower is better
    # - Files with def sorries are penalized heavily (Aristotle skips them)
    # - Files with axioms need conversion (medium penalty)
    # - Fewer sorries = easier to prove
    local score=$((thm_sorry + def_sorry * 100 + axiom_count * 10))

    echo "$basename|$total_sorry|$def_sorry|$axiom_count|$thm_sorry|$score"
}

# Main logic
main() {
    local submitted_files
    submitted_files=$(get_submitted_files)

    local candidates=()
    local candidate_data=()

    for file in "$PROOFS_DIR"/Erdos*Problem.lean; do
        [[ -f "$file" ]] || continue

        local basename=$(basename "$file" .lean)

        # Skip if already submitted
        if echo "$submitted_files" | grep -q "^${basename}$"; then
            continue
        fi

        # Analyze file
        local analysis=$(analyze_file "$file")
        local total_sorry=$(echo "$analysis" | cut -d'|' -f2)

        # Skip files with no sorries (nothing to prove)
        if [[ "$total_sorry" -eq 0 ]]; then
            continue
        fi

        candidate_data+=("$analysis")
    done

    # Sort by score (lower is better)
    local sorted_data=$(printf '%s\n' "${candidate_data[@]}" | sort -t'|' -k6 -n)

    if [[ "$COUNT_ONLY" == true ]]; then
        echo "$sorted_data" | wc -l | tr -d ' '
        return
    fi

    if [[ "$BEST_N" -gt 0 ]]; then
        sorted_data=$(echo "$sorted_data" | head -n "$BEST_N")
    fi

    if [[ "$JSON_OUTPUT" == true ]]; then
        echo "["
        local first=true
        while IFS='|' read -r name total def axiom thm score; do
            [[ -z "$name" ]] && continue
            if [[ "$first" == true ]]; then
                first=false
            else
                echo ","
            fi
            cat <<EOF
  {
    "file": "proofs/Proofs/${name}.lean",
    "total_sorries": $total,
    "def_sorries": $def,
    "axioms": $axiom,
    "theorem_sorries": $thm,
    "score": $score
  }
EOF
        done <<< "$sorted_data"
        echo ""
        echo "]"
    else
        echo "=== Aristotle Candidates ==="
        echo ""
        printf "%-40s %8s %8s %8s %8s\n" "File" "Sorries" "DefSorry" "Axioms" "Score"
        printf "%-40s %8s %8s %8s %8s\n" "----" "-------" "--------" "------" "-----"

        while IFS='|' read -r name total def axiom thm score; do
            [[ -z "$name" ]] && continue
            printf "%-40s %8d %8d %8d %8d\n" "$name" "$total" "$def" "$axiom" "$score"
        done <<< "$sorted_data"

        echo ""
        echo "Total candidates: $(echo "$sorted_data" | grep -c '|' || echo 0)"
        echo "Best candidates have low score (few sorries, no def sorries)"
    fi
}

main
