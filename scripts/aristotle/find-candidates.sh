#!/bin/bash
#
# find-candidates.sh - Find Lean files suitable for Aristotle submission
#
# Usage:
#   ./find-candidates.sh              # List all candidates (both tiers)
#   ./find-candidates.sh --count      # Just count candidates
#   ./find-candidates.sh --best N     # Top N candidates (fewest sorries)
#   ./find-candidates.sh --json       # Output as JSON
#   ./find-candidates.sh --tier1-only # Return only companion files (Tier 1)
#
# Four-tier candidate system:
#   Tier 0 (highest priority): *StatementOnly.lean files (Harmonic format)
#     - One theorem per file with informal /- problem block and standard set_option block
#     - Mirrors Harmonic's HarmonicLean/StatementOnly_*.lean convention
#     - Score = theorem_sorries only
#   Tier 1: *Aristotle.lean companion files
#     - Purpose-built for Aristotle: only routine lemma sorries, no axioms
#     - Created by Researchers alongside main proof files
#     - Score = theorem_sorries only (no axiom penalty)
#   Tier 2 (fallback): Research output files (non-Erdos, non-Test, non-Aristotle, non-StatementOnly)
#     - Researcher-produced files with complete definitions and routine lemma sorries
#     - Score = theorem_sorries only
#   Tier 3 (opt-in, rate-limited): Open-conjecture targets from research/open-conjectures.json
#     - Long-haul research targets — the headline conjecture STAYS a sorry; the system attempts it
#     - Failures DO NOT block future attempts; the registry enforces a per-file cadence (default 7d)
#     - Returned only when the per-target cadence allows another attempt
#     - If research/open-conjectures.json does not exist, Tier 3 is silent and overall behavior
#       is identical to the prior three-tier system.
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
OPEN_CONJ_REGISTRY="$PROJECT_ROOT/research/open-conjectures.json"
ARISTOTLE_RUNS_DIR="$PROJECT_ROOT/research/aristotle-runs"

# Repeat-submission dedup guard (issue #43033). A file submitted this many
# times or more (any status, summed across the whole jobs.json history)
# without ever reaching "integrated" is a repeat offender: further
# resubmission is unlikely to make progress and just burns server capacity.
# This is a backstop independent of get_submitted_files()/get_blocked_files()
# above, which key off the *current* status of the *most recent* job(s) and
# can be fooled by a jobs.json history that lost or never recorded
# intermediate attempts (the root cause of #43006's 90-duplicate incident).
ARISTOTLE_DEDUP_MAX_ATTEMPTS="${ARISTOTLE_DEDUP_MAX_ATTEMPTS:-3}"

# Parse arguments
COUNT_ONLY=false
BEST_N=0
JSON_OUTPUT=false
TIER1_ONLY=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --count) COUNT_ONLY=true; shift ;;
        --best) BEST_N="$2"; shift 2 ;;
        --json) JSON_OUTPUT=true; shift ;;
        --tier1-only) TIER1_ONLY=true; shift ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# Helper: count grep matches safely (grep -c exits 1 on 0 matches)
count_matches() {
    grep -cE "$1" "$2" 2>/dev/null || true
}

# Get list of files already handled by active, successful, or terminal jobs
get_submitted_files() {
    if [[ -f "$JOBS_FILE" ]]; then
        # Exclude files with active, successful, or explicit terminal jobs.
        # Expired and failed files are eligible for resubmission (handled by blocked check)
        jq -r '.jobs[] | select(
            .status == "submitted" or
            .status == "completed" or
            .status == "integrated" or
            .status == "resolved_manually" or
            .status == "blocked"
        ) | .file' "$JOBS_FILE" 2>/dev/null | xargs -I{} basename {} .lean | sort -u
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

# Files submitted ARISTOTLE_DEDUP_MAX_ATTEMPTS+ times across all of jobs.json
# history (any status) with no "integrated" job among them. Excluded from
# candidate selection regardless of the current-status filters above.
get_repeat_offender_files() {
    if [[ ! -f "$JOBS_FILE" ]]; then
        return
    fi

    jq -r --argjson max "$ARISTOTLE_DEDUP_MAX_ATTEMPTS" '
        .jobs
        | group_by(.file)
        | map(select(length >= $max and all(.[]; .status != "integrated")))
        | map(.[0].file)
        | .[]
    ' "$JOBS_FILE" 2>/dev/null | xargs -I{} basename {} .lean | sort -u
}

# Analyze a single file. Returns score -1 for hard rejects.
# Args: file, tier (0, 1 or 2)
analyze_file() {
    local file="$1"
    local tier="${2:-2}"
    local basename=$(basename "$file" .lean)

    # Count different types of sorries
    local total_sorry=$(count_matches "sorry" "$file")
    local def_sorry=$(count_matches "^(noncomputable )?def[[:space:]].*(:=.*sorry|sorry$)" "$file")
    local axiom_count=$(count_matches "^axiom " "$file")

    # Hard reject: files with definition sorries
    if [[ "$def_sorry" -gt 0 ]]; then
        echo "$basename|$total_sorry|$def_sorry|$axiom_count|0|-1|$tier"
        return
    fi

    # Check for all-True placeholder theorems
    local thm_sorry_count=$(count_matches "^(theorem|lemma)[[:space:]].*sorry" "$file")
    local true_thm_count=$(count_matches "^(theorem|lemma)[[:space:]].*:[[:space:]]*True[[:space:]]*:=" "$file")

    # Hard reject: all theorem sorries are True placeholders
    if [[ "$thm_sorry_count" -gt 0 && "$thm_sorry_count" -eq "$true_thm_count" ]]; then
        echo "$basename|$total_sorry|$def_sorry|$axiom_count|0|-1|$tier"
        return
    fi

    # Theorem sorries = total - definition sorries (approximate)
    local thm_sorry=$((total_sorry - def_sorry))

    # Score: lower is better
    # Axiom penalty removed — axioms are background facts, not obstacles.
    # Companion files explicitly shouldn't have axioms; regular files are scored
    # purely on theorem sorry count.
    local score="$thm_sorry"

    echo "$basename|$total_sorry|$def_sorry|$axiom_count|$thm_sorry|$score|$tier"
}

# Collect candidates from a set of files
collect_candidates() {
    local tier="$1"
    local submitted_files="$2"
    local blocked_files="$3"
    local repeat_offender_files="$4"
    shift 4
    local files=("$@")

    for file in "${files[@]}"; do
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

        # Skip repeat offenders (ARISTOTLE_DEDUP_MAX_ATTEMPTS+ submissions,
        # never integrated) — see get_repeat_offender_files().
        if echo "$repeat_offender_files" | grep -q "^${basename}$"; then
            continue
        fi

        # Analyze file
        local analysis=$(analyze_file "$file" "$tier")
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

        echo "$analysis"
    done
}

# ---------------------------------------------------------------------------
# Tier 3: open-conjecture registry helpers
#
# Tier 3 targets are opt-in via research/open-conjectures.json. Each entry has
# a per-file `cadence` (default 7d). A target is eligible for re-submission iff
# its most recent attempt artifact (research/aristotle-runs/<slug>/<ts>/) is
# older than the cadence — or no attempt exists yet.
#
# Failures DO NOT block Tier 3 candidates. This is intentional: the whole point
# of Tier 3 is to keep trying hard problems, not single-shot them and give up.
# ---------------------------------------------------------------------------

# Returns 0 (success) if the registry is present, non-zero otherwise.
tier3_registry_present() {
    [[ -f "$OPEN_CONJ_REGISTRY" ]]
}

# Print one basename (no .lean) per line for every file referenced by the
# Tier-3 registry. Used to suppress duplicate Tier-2 emissions for files that
# are also Tier-3 targets — a Tier-3 entry takes precedence so the routine
# blocked/submitted filters do not silence the long-haul target.
tier3_registered_basenames() {
    tier3_registry_present || return 0
    jq -r '.targets[]? | .file' "$OPEN_CONJ_REGISTRY" 2>/dev/null \
        | while IFS= read -r rel; do
            [[ -z "$rel" ]] && continue
            basename "$rel" .lean
        done | sort -u
}

# Parse a cadence string like "7d" / "12h" / "30m" into seconds. Defaults to
# 604800 (7 days) on parse failure.
cadence_to_seconds() {
    local cad="$1"
    if [[ -z "$cad" ]]; then
        echo 604800
        return
    fi
    local n="${cad%[a-zA-Z]*}"
    local unit="${cad##*[0-9]}"
    if [[ ! "$n" =~ ^[0-9]+$ ]]; then
        echo 604800
        return
    fi
    case "$unit" in
        s) echo "$n" ;;
        m) echo $((n * 60)) ;;
        h) echo $((n * 3600)) ;;
        d) echo $((n * 86400)) ;;
        w) echo $((n * 604800)) ;;
        *) echo 604800 ;;
    esac
}

# Print the epoch-seconds of the most recent artifact directory for a given
# Tier-3 slug, or 0 if none exists.
tier3_last_attempt_epoch() {
    local slug="$1"
    local dir="$ARISTOTLE_RUNS_DIR/$slug"
    [[ -d "$dir" ]] || { echo 0; return; }
    # Artifact subdirs are timestamp-named (e.g., 2026-06-10T03-15Z). Use mtime
    # of the most recently-created subdir as the attempt epoch.
    local latest
    latest=$(find "$dir" -mindepth 1 -maxdepth 1 -type d \
        -exec stat -f '%m' {} \; 2>/dev/null \
        || find "$dir" -mindepth 1 -maxdepth 1 -type d \
        -exec stat -c '%Y' {} \; 2>/dev/null \
        || echo "")
    if [[ -z "$latest" ]]; then
        echo 0
        return
    fi
    # Highest mtime among subdirs is the most recent attempt.
    echo "$latest" | sort -n | tail -1
}

# Collect Tier-3 candidates from the open-conjectures registry. Emits the same
# pipe-delimited format as collect_candidates() for the main pipeline.
collect_tier3_candidates() {
    tier3_registry_present || return 0

    local default_cadence
    default_cadence=$(jq -r '.defaults.cadence // "7d"' "$OPEN_CONJ_REGISTRY" 2>/dev/null || echo "7d")

    local now_epoch
    now_epoch=$(date +%s)

    # Iterate registry entries
    jq -r '.targets[]? | [.slug, .file, (.cadence // ""), .theorem] | @tsv' \
        "$OPEN_CONJ_REGISTRY" 2>/dev/null | while IFS=$'\t' read -r slug rel_file cadence theorem; do
        [[ -z "$slug" ]] && continue
        [[ -z "$rel_file" ]] && continue

        local abs_file="$PROJECT_ROOT/$rel_file"
        [[ -f "$abs_file" ]] || continue

        local effective_cadence="${cadence:-$default_cadence}"
        local cad_secs
        cad_secs=$(cadence_to_seconds "$effective_cadence")

        local last_epoch
        last_epoch=$(tier3_last_attempt_epoch "$slug")

        local elapsed=$((now_epoch - last_epoch))
        # If most recent attempt is within the cadence window, skip.
        if [[ "$last_epoch" -gt 0 && "$elapsed" -lt "$cad_secs" ]]; then
            continue
        fi

        # Analyze the file (tier 3). Score is theorem_sorries.
        local analysis
        analysis=$(analyze_file "$abs_file" 3)
        local score
        score=$(echo "$analysis" | cut -d'|' -f6)
        # Skip hard rejects (definition sorries or all-True placeholders).
        [[ "$score" -eq -1 ]] && continue

        echo "$analysis"
    done
}

# Main logic
main() {
    local submitted_files
    submitted_files=$(get_submitted_files)

    local blocked_files
    blocked_files=$(get_blocked_files)

    local repeat_offender_files
    repeat_offender_files=$(get_repeat_offender_files)

    local candidate_data=()

    # Tier 0: StatementOnly files (*StatementOnly.lean) — Harmonic format
    local tier0_files=()
    while IFS= read -r f; do
        tier0_files+=("$f")
    done < <(find "$PROOFS_DIR" -name "*StatementOnly.lean" -type f 2>/dev/null | sort)

    if [[ ${#tier0_files[@]} -gt 0 ]]; then
        while IFS= read -r line; do
            [[ -n "$line" ]] && candidate_data+=("$line")
        done < <(collect_candidates 0 "$submitted_files" "$blocked_files" "$repeat_offender_files" "${tier0_files[@]}")
    fi

    # Tier 1: Companion files (*Aristotle.lean)
    local tier1_files=()
    while IFS= read -r f; do
        tier1_files+=("$f")
    done < <(find "$PROOFS_DIR" -name "*Aristotle.lean" -type f 2>/dev/null | sort)

    if [[ ${#tier1_files[@]} -gt 0 ]]; then
        while IFS= read -r line; do
            [[ -n "$line" ]] && candidate_data+=("$line")
        done < <(collect_candidates 1 "$submitted_files" "$blocked_files" "$repeat_offender_files" "${tier1_files[@]}")
    fi

    # Tier 2: Regular proof files (unless --tier1-only).
    # Files registered as Tier-3 open-conjecture targets are excluded from
    # Tier 2 so the same file is not emitted twice (and so the Tier-2
    # blocked/submitted filters do not silence a long-haul T3 target).
    if [[ "$TIER1_ONLY" != true ]]; then
        local tier3_basenames
        tier3_basenames=$(tier3_registered_basenames)

        local tier2_files=()
        while IFS= read -r f; do
            local bn
            bn=$(basename "$f" .lean)
            if [[ -n "$tier3_basenames" ]] && echo "$tier3_basenames" | grep -q "^${bn}$"; then
                continue
            fi
            tier2_files+=("$f")
        done < <(find "$PROOFS_DIR" -name "*.lean" -type f \
            ! -name "Erdos*" ! -name "Test*" ! -name "*Aristotle.lean" ! -name "*StatementOnly.lean" \
            2>/dev/null | sort)

        if [[ ${#tier2_files[@]} -gt 0 ]]; then
            while IFS= read -r line; do
                [[ -n "$line" ]] && candidate_data+=("$line")
            done < <(collect_candidates 2 "$submitted_files" "$blocked_files" "$repeat_offender_files" "${tier2_files[@]}")
        fi
    fi

    # Tier 3: Open-conjecture registry (opt-in, rate-limited, no submitted/blocked filters)
    # Tier-3 entries are gated by cadence rather than the success/failure status
    # of prior jobs. The whole point is to keep attempting — failures DO NOT block.
    if [[ "$TIER1_ONLY" != true ]]; then
        while IFS= read -r line; do
            [[ -n "$line" ]] && candidate_data+=("$line")
        done < <(collect_tier3_candidates)
    fi

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

    # Sort: Tier 1 first (by score), then Tier 2 (by score)
    # Use stable sort: primary key = tier, secondary key = score
    local sorted_data
    sorted_data=$(printf '%s\n' "${candidate_data[@]}" | sort -t'|' -k7 -n -k6 -n)

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
        while IFS='|' read -r name total def axiom thm score tier; do
            [[ -z "$name" ]] && continue
            if [[ "$first" == true ]]; then
                first=false
            else
                echo ","
            fi
            # companion_file is true for Tier 0 (StatementOnly) AND Tier 1 (Aristotle).
            # Both are purpose-built files for Aristotle submission.
            local companion_flag="false"
            if [[ "$tier" -eq 0 || "$tier" -eq 1 ]]; then
                companion_flag="true"
            fi
            cat <<EOF
  {
    "file": "proofs/Proofs/${name}.lean",
    "total_sorries": $total,
    "def_sorries": $def,
    "axioms": $axiom,
    "theorem_sorries": $thm,
    "score": $score,
    "tier": $tier,
    "companion_file": $companion_flag
  }
EOF
        done <<< "$sorted_data"
        echo ""
        echo "]"
    else
        echo "=== Aristotle Candidates ==="
        echo ""
        printf "%-40s %5s %8s %8s %8s %8s\n" "File" "Tier" "Sorries" "DefSorry" "Axioms" "Score"
        printf "%-40s %5s %8s %8s %8s %8s\n" "----" "----" "-------" "--------" "------" "-----"

        while IFS='|' read -r name total def axiom thm score tier; do
            [[ -z "$name" ]] && continue
            local tier_label
            case "$tier" in
                0) tier_label="T0" ;;
                1) tier_label="T1" ;;
                2) tier_label="T2" ;;
                3) tier_label="T3" ;;
                *) tier_label="T2" ;;
            esac
            printf "%-40s %5s %8d %8d %8d %8d\n" "$name" "$tier_label" "$total" "$def" "$axiom" "$score"
        done <<< "$sorted_data"

        local total_count tier0_count tier1_count tier2_count tier3_count
        total_count=$(echo "$sorted_data" | grep -c '|' 2>/dev/null; true)
        tier0_count=$(echo "$sorted_data" | grep -c '|0$' 2>/dev/null; true)
        tier1_count=$(echo "$sorted_data" | grep -c '|1$' 2>/dev/null; true)
        tier2_count=$(echo "$sorted_data" | grep -c '|2$' 2>/dev/null; true)
        tier3_count=$(echo "$sorted_data" | grep -c '|3$' 2>/dev/null; true)
        total_count="${total_count:-0}"
        tier0_count="${tier0_count:-0}"
        tier1_count="${tier1_count:-0}"
        tier2_count="${tier2_count:-0}"
        tier3_count="${tier3_count:-0}"
        echo ""
        echo "Total candidates: $total_count (T0 statement-only: $tier0_count, T1 companion: $tier1_count, T2 regular: $tier2_count, T3 open-conjecture: $tier3_count)"
        echo "T0 StatementOnly files (Harmonic format) have top priority. T1 companion files are next."
        echo "T2 research output files are fallback when T0+T1 slots exhausted."
        echo "T3 open-conjecture targets (research/open-conjectures.json) are rate-limited long-haul attempts."
        echo "Best candidates have low score (few sorries, no def sorries)"
    fi
}

main
