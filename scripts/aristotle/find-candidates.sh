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
#   - Have NOT been submitted to Aristotle yet (or were modified since last failure)
#   - Have no definition sorries (hard reject - Aristotle skips these)
#   - Are not all-True placeholder theorems (hard reject - no value)
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

# Helper: count grep matches safely (grep -c exits 1 on 0 matches)
count_matches() {
    grep -cE "$1" "$2" 2>/dev/null || true
}

# Get list of already-submitted files (active or successful jobs)
get_submitted_files() {
    if [[ -f "$JOBS_FILE" ]]; then
        # Only exclude files with active or successful jobs
        # Expired and failed files are eligible for resubmission (handled by blocked check)
        jq -r '.jobs[] | select(.status == "submitted" or .status == "completed" or .status == "integrated") | .file' "$JOBS_FILE" 2>/dev/null | xargs -I{} basename {} .lean | sort -u
    fi
}

# Get files blocked from resubmission (2+ failures, not modified since last attempt)
get_blocked_files() {
    if [[ ! -f "$JOBS_FILE" ]]; then
        return
    fi

    # Find files with 2+ failed/expired jobs where no theorems were proven
    jq -r '
        [.jobs[] | select(.status == "failed" or .status == "expired")]
        | group_by(.file)
        | map(select(length >= 2))
        | map({
            file: .[0].file,
            count: length,
            last_submitted: (map(.submitted) | sort | last)
          })
        | .[]
        | "\(.file)|\(.last_submitted)"
    ' "$JOBS_FILE" 2>/dev/null | while IFS='|' read -r file last_submitted; do
        [[ -z "$file" ]] && continue

        # Resolve to absolute path
        local abs_file="$PROJECT_ROOT/$file"
        [[ -f "$abs_file" ]] || continue

        # Check if file was modified since last submission
        local file_mtime
        file_mtime=$(stat -f '%m' "$abs_file" 2>/dev/null || stat -c '%Y' "$abs_file" 2>/dev/null || echo 0)

        local submit_epoch
        submit_epoch=$(date -j -f '%Y-%m-%dT%H:%M:%SZ' "$last_submitted" '+%s' 2>/dev/null || \
                       date -d "$last_submitted" '+%s' 2>/dev/null || echo 0)

        # If file hasn't been modified since last submission, block it
        if [[ "$file_mtime" -le "$submit_epoch" ]]; then
            basename "$abs_file" .lean
        fi
    done | sort -u
}

# Analyze a single file. Returns score -1 for hard rejects.
analyze_file() {
    local file="$1"
    local basename=$(basename "$file" .lean)

    # Count different types of sorries
    local total_sorry=$(count_matches "sorry" "$file")
    local def_sorry=$(count_matches "^(noncomputable )?def[[:space:]].*(:=.*sorry|sorry$)" "$file")
    local axiom_count=$(count_matches "^axiom " "$file")

    # Hard reject: files with definition sorries
    if [[ "$def_sorry" -gt 0 ]]; then
        echo "$basename|$total_sorry|$def_sorry|$axiom_count|0|-1"
        return
    fi

    # Check for all-True placeholder theorems
    local thm_sorry_count=$(count_matches "^(theorem|lemma)[[:space:]].*sorry" "$file")
    local true_thm_count=$(count_matches "^(theorem|lemma)[[:space:]].*:[[:space:]]*True[[:space:]]*:=" "$file")

    # Hard reject: all theorem sorries are True placeholders
    if [[ "$thm_sorry_count" -gt 0 && "$thm_sorry_count" -eq "$true_thm_count" ]]; then
        echo "$basename|$total_sorry|$def_sorry|$axiom_count|0|-1"
        return
    fi

    # Theorem sorries = total - definition sorries (approximate)
    local thm_sorry=$((total_sorry - def_sorry))

    # Score: lower is better
    # - Axioms get small penalty (auto-converted by preprocessing now, but still slightly harder)
    # - Fewer sorries = easier to prove
    local score=$((thm_sorry + axiom_count * 2))

    echo "$basename|$total_sorry|$def_sorry|$axiom_count|$thm_sorry|$score"
}

# Main logic
main() {
    local submitted_files
    submitted_files=$(get_submitted_files)

    local blocked_files
    blocked_files=$(get_blocked_files)

    local candidate_data=()

    for file in "$PROOFS_DIR"/Erdos*Problem.lean; do
        [[ -f "$file" ]] || continue

        local basename=$(basename "$file" .lean)

        # Skip if already submitted (active/successful)
        if echo "$submitted_files" | grep -q "^${basename}$"; then
            continue
        fi

        # Skip if blocked (repeatedly failed, not modified)
        if echo "$blocked_files" | grep -q "^${basename}$"; then
            continue
        fi

        # Analyze file
        local analysis=$(analyze_file "$file")
        local total_sorry=$(echo "$analysis" | cut -d'|' -f2)
        local score=$(echo "$analysis" | cut -d'|' -f6)

        # Skip files with no sorries (nothing to prove)
        if [[ "$total_sorry" -eq 0 ]]; then
            continue
        fi

        # Skip hard rejects (score -1)
        if [[ "$score" -eq -1 ]]; then
            continue
        fi

        candidate_data+=("$analysis")
    done

    if [[ ${#candidate_data[@]} -eq 0 ]]; then
        if [[ "$COUNT_ONLY" == true ]]; then
            echo 0
        elif [[ "$JSON_OUTPUT" == true ]]; then
            echo "[]"
        else
            echo "=== Aristotle Candidates ==="
            echo ""
            echo "No candidates found"
        fi
        return
    fi

    # Sort by score (lower is better)
    local sorted_data
    sorted_data=$(printf '%s\n' "${candidate_data[@]}" | sort -t'|' -k6 -n)

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
