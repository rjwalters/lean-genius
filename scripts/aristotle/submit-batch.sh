#!/bin/bash
#
# submit-batch.sh - Submit a batch of files to Aristotle
#
# Usage:
#   ./submit-batch.sh                    # Submit up to TARGET (default 10) total active
#   ./submit-batch.sh --count N          # Submit exactly N files
#   ./submit-batch.sh --dry-run          # Show what would be submitted
#   ./submit-batch.sh --target N         # Maintain N active jobs (default 10)
#
# Environment:
#   ARISTOTLE_API_KEY - Required for submission
#   ARISTOTLE_TARGET  - Target number of active jobs (default 10)
#
# Submission order: Tier 0 StatementOnly files (*StatementOnly.lean) first,
# then Tier 1 companion files (*Aristotle.lean), then Tier 2 research output
# files to fill remaining slots.
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"
FIND_CANDIDATES="$SCRIPT_DIR/find-candidates.sh"
PREPROCESS="$SCRIPT_DIR/preprocess-for-aristotle.sh"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

# Defaults
TARGET_ACTIVE="${ARISTOTLE_TARGET:-10}"
SUBMIT_COUNT=0
DRY_RUN=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --count) SUBMIT_COUNT="$2"; shift 2 ;;
        --target) TARGET_ACTIVE="$2"; shift 2 ;;
        --dry-run) DRY_RUN=true; shift ;;
        -h|--help)
            echo "Usage: $0 [--count N] [--target N] [--dry-run]"
            echo ""
            echo "Options:"
            echo "  --count N    Submit exactly N files"
            echo "  --target N   Maintain N active jobs (default: 10)"
            echo "  --dry-run    Show what would be submitted"
            echo ""
            echo "Submission order: Tier 0 StatementOnly files (*StatementOnly.lean) first,"
            echo "then Tier 1 companion files (*Aristotle.lean), then Tier 2 research files."
            exit 0
            ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# Check API key
if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
    if [[ -f "$HOME/.aristotle_key" ]]; then
        export ARISTOTLE_API_KEY=$(cat "$HOME/.aristotle_key")
    else
        echo -e "${RED}ERROR: ARISTOTLE_API_KEY not set${NC}" >&2
        echo "Set via environment or create ~/.aristotle_key" >&2
        exit 1
    fi
fi

# Count locally tracked active (submitted) jobs
count_active_jobs() {
    if [[ ! -f "$JOBS_FILE" ]]; then
        echo 0
        return
    fi
    jq '[.jobs[] | select(.status == "submitted")] | length' "$JOBS_FILE"
}

# Server capacity limit (hard limit is 5, use safe margin)
SERVER_CAPACITY_LIMIT=3

# Check server capacity using the Aristotle CLI.
# Returns 0 if under limit, 1 if at/over limit.
# Sets SERVER_ACTIVE to the count.
check_server_capacity() {
    local active=0
    local breakdown=""

    # Query active statuses via CLI (exclude NOT_STARTED — these are old zombies that will never run)
    for status in QUEUED IN_PROGRESS; do
        local output
        output=$(uvx --from aristotlelib aristotle list --status "$status" --limit 100 2>&1) || {
            echo -e "${RED}Server capacity check failed for status $status${NC}" >&2
            echo -e "${YELLOW}Proceeding with local count only${NC}" >&2
            SERVER_ACTIVE=-1
            return 0
        }

        # Count lines that look like project entries (UUID at start of line)
        local count
        count=$(echo "$output" | grep -cE '^[0-9a-f]{8}-' 2>/dev/null || true)

        if [[ "$count" -gt 0 ]]; then
            active=$((active + count))
            if [[ -n "$breakdown" ]]; then
                breakdown="$breakdown, $status: $count"
            else
                breakdown="$status: $count"
            fi
        fi
    done

    SERVER_ACTIVE="$active"

    echo "Server active projects: $SERVER_ACTIVE (limit: $SERVER_CAPACITY_LIMIT)"
    if [[ -n "$breakdown" ]]; then
        echo "  Breakdown: $breakdown"
    fi

    if [[ "$SERVER_ACTIVE" -ge "$SERVER_CAPACITY_LIMIT" ]]; then
        echo -e "${YELLOW}At or over server capacity limit ($SERVER_ACTIVE >= $SERVER_CAPACITY_LIMIT)${NC}"
        echo -e "${YELLOW}Skipping batch to avoid creating zombie projects${NC}"
        return 1
    fi

    return 0
}

# Convert Lean file names like Erdos1002OQ01OQ01.lean to canonical
# research ids like erdos-1002-oq-01-oq-01.
lean_file_to_problem_id() {
    local stem
    stem=$(basename "$1" .lean)
    stem="${stem%Aristotle}"
    stem="${stem%Problem}"

    if [[ "$stem" =~ ^Erdos([0-9]+)(.*)$ ]]; then
        local number="${BASH_REMATCH[1]}"
        local suffix="${BASH_REMATCH[2]}"
        local problem_id="erdos-$number"

        if [[ -n "$suffix" ]]; then
            local suffix_slug
            suffix_slug=$(printf '%s\n' "$suffix" |
                sed -E 's/([A-Za-z]+)([0-9]+)/\1-\2/g; s/([0-9])([A-Za-z])/\1-\2/g; s/([a-z])([A-Z])/\1-\2/g; s/^-//; s/-+/-/g' |
                tr '[:upper:]' '[:lower:]')
            problem_id="$problem_id-$suffix_slug"
        fi

        echo "$problem_id"
        return 0
    fi

    basename "$1" .lean | tr '[:upper:]' '[:lower:]'
}

# Submit a single file to Aristotle
# Returns: 0=success, 1=error, 2=rate-limited (caller should stop submitting), 3=rejected by preprocessing
submit_file() {
    local file="$1"
    local problem_id
    problem_id=$(lean_file_to_problem_id "$file")

    local is_companion=false
    [[ "$file" == *Aristotle.lean ]] && is_companion=true
    local is_statement_only=false
    [[ "$file" == *StatementOnly.lean ]] && is_statement_only=true

    if [[ "$is_statement_only" == true ]]; then
        echo -e "${BLUE}Submitting [T0 statement-only]:${NC} $file"
    elif [[ "$is_companion" == true ]]; then
        echo -e "${BLUE}Submitting [T1 companion]:${NC} $file"
    else
        echo -e "${BLUE}Submitting [T2 regular]:${NC} $file"
    fi

    # Preprocess the file (fix docstrings, reject unsuitable files)
    local preprocess_log=""
    local submit_file="$file"
    local preprocessed_tmp=""

    if [[ -x "$PREPROCESS" ]]; then
        local preprocess_output
        preprocess_output=$("$PREPROCESS" "$file" 2>&1) || {
            local reject_reason
            reject_reason=$(echo "$preprocess_output" | grep "^REJECT:" | head -1 || true)
            echo -e "  ${YELLOW}Skipped (preprocessing):${NC} ${reject_reason:-rejected}"
            return 3
        }

        # Last line = temp file path, preceding lines = log
        preprocessed_tmp=$(echo "$preprocess_output" | tail -1)
        preprocess_log=$(echo "$preprocess_output" | grep "^PREPROCESS:" | grep -v "^PREPROCESS: Result has\|^PREPROCESS: No changes needed" | sed 's/^PREPROCESS: //' | paste -sd '; ' - || true)

        if [[ -n "$preprocessed_tmp" && -f "$preprocessed_tmp" ]]; then
            submit_file="$preprocessed_tmp"
            if [[ -n "$preprocess_log" ]]; then
                echo -e "  ${CYAN}Preprocessed:${NC} $preprocess_log"
            fi
        fi
    fi

    if [[ "$DRY_RUN" == true ]]; then
        echo -e "  ${YELLOW}[DRY RUN]${NC} Would submit $problem_id"
        [[ -n "$preprocessed_tmp" && -f "$preprocessed_tmp" ]] && rm -rf "$(dirname "$preprocessed_tmp")"
        return 0
    fi

    # Determine the project directory for submission.
    # The preprocessor creates a temp dir with the lean file + lakefile.toml + lean-toolchain.
    # If preprocessing was done, use that temp dir. Otherwise, create one for the raw file.
    local project_dir=""
    if [[ -n "$preprocessed_tmp" && -f "$preprocessed_tmp" ]]; then
        project_dir="$(dirname "$preprocessed_tmp")"
    else
        # Create a temp project dir with the file and Lean project metadata
        project_dir=$(mktemp -d "${TMPDIR:-/tmp}/aristotle-submit-XXXXXX")
        cp "$submit_file" "$project_dir/"
        cp "$PROJECT_ROOT/proofs/lakefile.toml" "$project_dir/"
        cp "$PROJECT_ROOT/proofs/lean-toolchain" "$project_dir/"
    fi

    # Submit using the new Aristotle CLI (default is async, no --wait needed)
    local output
    output=$(uvx --from aristotlelib aristotle submit --project-dir "$project_dir" "Prove all sorry lemmas in $(basename "$submit_file")" 2>&1) || {
        # Clean up temp directory
        rm -rf "$project_dir"

        # Check for rate limiting (429) - stop batch immediately
        if echo "$output" | grep -qi "429\|rate.limit\|too many\|already have.*projects"; then
            echo -e "  ${YELLOW}Rate limited:${NC} $output"
            echo -e "  ${YELLOW}Stopping batch to avoid creating zombie projects${NC}"
            return 2
        fi
        echo -e "  ${RED}Failed:${NC} $output"
        return 1
    }

    # Clean up temp directory after submission
    rm -rf "$project_dir"

    # Extract project ID from output (format: "INFO - Project created: <UUID>")
    local project_id=$(echo "$output" | grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' | head -1)

    if [[ -z "$project_id" ]]; then
        echo -e "  ${RED}Failed to get project ID${NC}"
        echo "  Output: $output"
        return 1
    fi

    echo -e "  ${GREEN}Submitted:${NC} $project_id"

    # Log to jobs file (include preprocessing metadata)
    local now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    local tmp_file=$(mktemp)
    local preprocessed_flag="false"
    [[ -n "$preprocess_log" ]] && preprocessed_flag="true"
    # companion_file flag captures both T0 (statement-only) and T1 (companion)
    # files — both are purpose-built Aristotle submissions.
    local companion_flag="false"
    if [[ "$is_companion" == true || "$is_statement_only" == true ]]; then
        companion_flag="true"
    fi
    local submission_tier="T2"
    local submission_note="Batch submission (T2)"
    if [[ "$is_statement_only" == true ]]; then
        submission_tier="T0"
        submission_note="StatementOnly submission (T0)"
    elif [[ "$is_companion" == true ]]; then
        submission_tier="T1"
        submission_note="Companion file submission (T1)"
    fi

    jq --arg pid "$project_id" \
       --arg file "$file" \
       --arg prob "$problem_id" \
       --arg now "$now" \
       --argjson preprocessed "$preprocessed_flag" \
       --arg preprocess_log "${preprocess_log:-}" \
       --argjson companion "$companion_flag" \
       --arg tier "$submission_tier" \
       --arg note "$submission_note" \
       '.jobs += [{
         project_id: $pid,
         file: $file,
         problem_id: $prob,
         submitted: $now,
         status: "submitted",
         preprocessed: $preprocessed,
         preprocessing_log: (if $preprocess_log != "" then $preprocess_log else null end),
         companion_file: $companion,
         tier: $tier,
         notes: $note
       }]' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"

    # Create completion signal for daemon stats tracking
    local completions_dir="$PROJECT_ROOT/.loom/signals/completions"
    mkdir -p "$completions_dir"
    touch "$completions_dir/proof-submitted-$problem_id-$(date +%s)"

    return 0
}

# Main logic
main() {
    echo -e "${BLUE}=== Aristotle Batch Submission ===${NC}"
    echo ""

    # Initialize jobs file if needed
    if [[ ! -f "$JOBS_FILE" ]]; then
        echo '{"jobs": []}' > "$JOBS_FILE"
    fi

    local active=$(count_active_jobs)
    echo "Currently active jobs (local): $active"
    echo "Target active jobs: $TARGET_ACTIVE"
    echo ""

    # Pre-flight: check actual server capacity before submitting
    if [[ "$DRY_RUN" != true ]]; then
        if ! check_server_capacity; then
            return 0
        fi
        echo ""

        # Safety check: if many COMPLETE projects on server are not tracked locally
        # at all, the recovery pipeline may be broken. This prevents wasting server
        # resources by resubmitting files whose results were never retrieved.
        local server_complete_ids
        server_complete_ids=$(uvx --from aristotlelib aristotle list --status COMPLETE --limit 100 2>&1 | grep -oE '^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' 2>/dev/null || true)
        if [[ -n "$server_complete_ids" ]]; then
            local tracked_ids
            tracked_ids=$(jq -r '.jobs[].project_id // empty' "$JOBS_FILE" 2>/dev/null | sort -u)
            local untracked=0
            while IFS= read -r pid; do
                [[ -z "$pid" ]] && continue
                if ! echo "$tracked_ids" | grep -q "^${pid}$"; then
                    untracked=$((untracked + 1))
                fi
            done <<< "$server_complete_ids"
            if [[ "$untracked" -gt 10 ]]; then
                echo -e "${RED}WARNING: $untracked COMPLETE projects on server not tracked locally${NC}"
                echo -e "${RED}Recovery pipeline may be broken — skipping submissions until resolved${NC}"
                echo -e "${YELLOW}Run: ./scripts/aristotle/retrieve-integrate.sh to recover results${NC}"
                return 0
            fi
        fi
    fi

    # Calculate how many to submit
    local to_submit
    if [[ "$SUBMIT_COUNT" -gt 0 ]]; then
        to_submit="$SUBMIT_COUNT"
    else
        to_submit=$((TARGET_ACTIVE - active))
        if [[ "$to_submit" -lt 0 ]]; then
            to_submit=0
        fi
    fi

    # Cap submissions to stay within server capacity
    if [[ "$DRY_RUN" != true && "$SERVER_ACTIVE" -ge 0 ]]; then
        local server_headroom=$((SERVER_CAPACITY_LIMIT - SERVER_ACTIVE))
        if [[ "$server_headroom" -lt "$to_submit" ]]; then
            echo -e "${YELLOW}Capping submissions to $server_headroom (server headroom)${NC}"
            to_submit="$server_headroom"
        fi
    fi

    if [[ "$to_submit" -le 0 ]]; then
        echo -e "${GREEN}No submissions needed (at capacity or target).${NC}"
        return 0
    fi

    echo "Will submit: $to_submit files"
    echo ""

    # Get best candidates — three-tier system:
    # Tier 0 (*StatementOnly.lean) first, then Tier 1 (companion *Aristotle.lean),
    # then Tier 2 (regular files). Ordering is enforced by find-candidates.sh.
    local candidates
    candidates=$("$FIND_CANDIDATES" --json --best "$to_submit" 2>/dev/null)

    if [[ -z "$candidates" || "$candidates" == "[]" ]]; then
        echo -e "${YELLOW}No candidates found${NC}"
        return 0
    fi

    local tier0_count
    tier0_count=$(echo "$candidates" | jq '[.[] | select(.tier == 0)] | length')
    local tier1_count
    tier1_count=$(echo "$candidates" | jq '[.[] | select(.tier == 1)] | length')
    local tier2_count
    tier2_count=$(echo "$candidates" | jq '[.[] | select(.tier == 2)] | length')

    echo "Candidates: $tier0_count Tier 0 StatementOnly + $tier1_count Tier 1 companion + $tier2_count Tier 2 regular files"
    echo ""

    # Submit each candidate (already sorted: T1 first, then T2)
    local submitted=0
    local failed=0
    local skipped=0
    local rate_limited=false

    while IFS= read -r file; do
        [[ -z "$file" ]] && continue

        local rc=0
        submit_file "$file" || rc=$?

        if [[ $rc -eq 0 ]]; then
            ((++submitted))
        elif [[ $rc -eq 2 ]]; then
            # Rate limited - stop batch immediately
            rate_limited=true
            break
        elif [[ $rc -eq 3 ]]; then
            # Rejected by preprocessing - skip but don't count as failure
            ((++skipped))
        else
            ((++failed))
        fi

        # Delay between submissions to avoid rate limits
        if [[ $rc -eq 0 ]]; then
            sleep 3
        fi
    done < <(echo "$candidates" | jq -r '.[].file')

    echo ""
    echo -e "${GREEN}Submitted: $submitted${NC}"
    if [[ "$skipped" -gt 0 ]]; then
        echo -e "${YELLOW}Skipped (preprocessing): $skipped${NC}"
    fi
    if [[ "$failed" -gt 0 ]]; then
        echo -e "${RED}Failed: $failed${NC}"
    fi
    if [[ "$rate_limited" == true ]]; then
        echo -e "${YELLOW}Stopped early due to rate limiting${NC}"
    fi

    local new_active=$(count_active_jobs)
    echo "Active jobs now: $new_active"
}

main
