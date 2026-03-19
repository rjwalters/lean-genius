#!/bin/bash
#
# retrieve-integrate.sh - Retrieve completed Aristotle solutions and integrate
#
# Usage:
#   ./retrieve-integrate.sh              # Retrieve and integrate all completed
#   ./retrieve-integrate.sh --retrieve   # Only retrieve, don't integrate
#   ./retrieve-integrate.sh --dry-run    # Show what would be done
#
# This script:
#   1. Finds completed jobs in jobs.json
#   2. Downloads solutions from Aristotle
#   3. Compares with original to check if improved
#   4. Copies improved proofs to proofs/Proofs/
#   5. Updates job status to "integrated"
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"
RESULTS_DIR="$PROJECT_ROOT/aristotle-results/new"
PROCESSED_DIR="$PROJECT_ROOT/aristotle-results/processed"
PROOFS_DIR="$PROJECT_ROOT/proofs/Proofs"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

RETRIEVE_ONLY=false
DRY_RUN=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --retrieve) RETRIEVE_ONLY=true; shift ;;
        --dry-run) DRY_RUN=true; shift ;;
        *) echo "Unknown option: $1" >&2; exit 1 ;;
    esac
done

# Check API key
if [[ -z "${ARISTOTLE_API_KEY:-}" ]]; then
    if [[ -f "$HOME/.aristotle_key" ]]; then
        export ARISTOTLE_API_KEY=$(cat "$HOME/.aristotle_key")
    else
        echo -e "${RED}ERROR: ARISTOTLE_API_KEY not set${NC}" >&2
        exit 1
    fi
fi

mkdir -p "$RESULTS_DIR" "$PROCESSED_DIR"

# Python script to retrieve solution
PYTHON_RETRIEVE='
import asyncio
import sys
from aristotlelib import Project

async def retrieve(project_id, output_path):
    try:
        projects, _ = await Project.list_projects()
        project = next((p for p in projects if p.project_id == project_id), None)

        if not project:
            print(f"ERROR: Project {project_id} not found")
            return False

        if project.status.name != "COMPLETE":
            print(f"ERROR: Project not complete (status: {project.status.name})")
            return False

        await project.get_solution(output_path)
        print(f"SUCCESS: Retrieved to {output_path}")
        return True
    except Exception as e:
        print(f"ERROR: {e}")
        return False

asyncio.run(retrieve(sys.argv[1], sys.argv[2]))
'

# Retrieve a single solution
retrieve_solution() {
    local project_id="$1"
    local output_path="$2"

    uvx --from aristotlelib python3 -c "$PYTHON_RETRIEVE" "$project_id" "$output_path" 2>&1
}

# Count sorries in a file
count_sorries() {
    grep -c "sorry" "$1" 2>/dev/null || echo 0
}

# Count theorems proved (sorries eliminated) by comparing original and solution
count_theorems_proved() {
    local original="$1"
    local solution="$2"

    # Count sorry occurrences in each file (grep -c counts lines, but that's close enough)
    local orig_count new_count
    orig_count=$(grep -c "sorry" "$original" 2>/dev/null || echo 0)
    new_count=$(grep -c "sorry" "$solution" 2>/dev/null || echo 0)

    local proved=$((orig_count - new_count))
    if [[ "$proved" -lt 0 ]]; then
        proved=0
    fi
    echo "$proved"
}

# Integrate a solution
integrate_solution() {
    local job="$1"
    local project_id=$(echo "$job" | jq -r '.project_id')
    local original_file=$(echo "$job" | jq -r '.file')
    local problem_id=$(echo "$job" | jq -r '.problem_id')
    local is_companion=$(echo "$job" | jq -r '.companion_file // false')

    local basename=$(basename "$original_file" .lean)
    local solution_file="$RESULTS_DIR/${basename}-solved.lean"

    # --- Ghost/stale job detection ---
    # If the file path points to a temp directory and the file doesn't exist,
    # this is a ghost job from reconciliation. Mark it stale and skip.
    if [[ "$original_file" == /var/folders/* || "$original_file" == /tmp/* ]]; then
        if [[ ! -f "$original_file" ]]; then
            echo -e "  ${YELLOW}WARNING:${NC} Job $project_id ($problem_id) has temp file path that no longer exists: $original_file"
            echo -e "  ${YELLOW}Marking as stale (ghost job from reconciliation)${NC}"
            if [[ "$DRY_RUN" != true ]]; then
                update_job_status "$project_id" "stale" "Ghost job: temp file path no longer exists ($original_file)"
            fi
            return 1
        fi
    fi

    # If the file path is a temp/absolute path (from preprocessing), map to proofs/Proofs/
    local original_path
    if [[ "$original_file" == /* ]]; then
        original_path="$PROOFS_DIR/${basename}.lean"
        if [[ ! -f "$original_path" ]]; then
            echo -e "  ${RED}ERROR:${NC} Job $project_id ($problem_id): temp path, no matching proof file found"
            echo -e "  ${RED}  Looked for:${NC} $original_path"
            echo -e "  ${RED}  Original file field:${NC} $original_file"
            echo -e "  ${RED}  Basename used:${NC} ${basename}.lean"
            if [[ "$DRY_RUN" != true ]]; then
                update_job_status "$project_id" "stale" "Cannot map temp path to proof file: looked for $PROOFS_DIR/${basename}.lean"
            fi
            return 1
        fi
    else
        original_path="$PROJECT_ROOT/$original_file"
        if [[ ! -f "$original_path" ]]; then
            echo -e "  ${RED}ERROR:${NC} Job $project_id ($problem_id): original file does not exist"
            echo -e "  ${RED}  Path:${NC} $original_path"
            if [[ "$DRY_RUN" != true ]]; then
                update_job_status "$project_id" "stale" "Original file missing: $original_path"
            fi
            return 1
        fi
    fi

    if [[ "$is_companion" == "true" ]]; then
        echo -e "${BLUE}Processing [companion]:${NC} $problem_id ($project_id)"
    else
        echo -e "${BLUE}Processing:${NC} $problem_id ($project_id)"
    fi

    # Retrieve solution
    if [[ "$DRY_RUN" == true ]]; then
        echo -e "  ${YELLOW}[DRY RUN]${NC} Would retrieve to $solution_file"
    else
        local result
        result=$(retrieve_solution "$project_id" "$solution_file")

        if echo "$result" | grep -q "ERROR"; then
            echo -e "  ${RED}ERROR:${NC} Retrieve failed for job $project_id ($problem_id): $result"

            # If project no longer exists on server, mark as expired
            if echo "$result" | grep -q "not found"; then
                echo -e "  ${YELLOW}Project expired on server — marking as expired${NC}"
                update_job_status "$project_id" "expired" "Project not found on server during retrieval"
            fi

            return 1
        fi

        echo -e "  ${GREEN}Retrieved${NC}"
    fi

    if [[ "$RETRIEVE_ONLY" == true ]]; then
        return 0
    fi

    # Compare sorry counts
    if [[ -f "$solution_file" && -f "$original_path" ]]; then
        local orig_sorries=$(count_sorries "$original_path")
        local new_sorries=$(count_sorries "$solution_file")

        echo -e "  Original sorries: $orig_sorries"
        echo -e "  Solution sorries: $new_sorries"

        if [[ "$new_sorries" -lt "$orig_sorries" ]]; then
            local theorems_proved
            theorems_proved=$(count_theorems_proved "$original_path" "$solution_file")
            echo -e "  ${GREEN}Improvement!${NC} ($orig_sorries -> $new_sorries, $theorems_proved theorems proved)"

            if [[ "$DRY_RUN" == true ]]; then
                echo -e "  ${YELLOW}[DRY RUN]${NC} Would copy to $original_path"
            else
                # Backup original
                cp "$original_path" "$original_path.bak"

                # Copy solution directly - the header is informative
                cp "$solution_file" "$original_path"

                echo -e "  ${GREEN}Integrated${NC}"

                # For companion files, remind Researcher to incorporate into main proof
                if [[ "$is_companion" == "true" ]]; then
                    local main_file="${basename/Aristotle/Problem}"
                    echo -e "  ${CYAN}[Companion file]${NC} Proved lemmas available in ${basename}.lean"
                    echo -e "  ${CYAN}→ Researcher should incorporate into ${main_file}.lean${NC}"
                fi

                # Move to processed
                mv "$solution_file" "$PROCESSED_DIR/"

                # Update job status with theorems_proved
                local outcome_note="$new_sorries sorries remaining"
                [[ "$is_companion" == "true" ]] && outcome_note="$new_sorries sorries remaining (companion file — merge into ${basename/Aristotle/Problem}.lean)"
                update_job_status_with_theorems "$project_id" "integrated" "$outcome_note" "$theorems_proved"

                # Create completion signal for daemon stats tracking
                local completions_dir="$PROJECT_ROOT/.loom/signals/completions"
                mkdir -p "$completions_dir"
                touch "$completions_dir/proof-integrated-$problem_id-$(date +%s)"
            fi
        elif [[ "$new_sorries" -eq 0 && "$orig_sorries" -eq 0 ]]; then
            echo -e "  ${YELLOW}Already complete${NC} (both have 0 sorries)"

            if [[ "$DRY_RUN" != true ]]; then
                mv "$solution_file" "$PROCESSED_DIR/" 2>/dev/null || true
                update_job_status_with_theorems "$project_id" "integrated" "Already had 0 sorries" "0"
            fi
        else
            echo -e "  ${YELLOW}No improvement${NC} ($orig_sorries -> $new_sorries)"

            if [[ "$DRY_RUN" != true ]]; then
                mv "$solution_file" "$PROCESSED_DIR/" 2>/dev/null || true
                update_job_status "$project_id" "completed" "$new_sorries sorries remaining"
            fi
        fi
    else
        echo -e "  ${RED}ERROR:${NC} Job $project_id ($problem_id): solution_file or original_path missing after retrieval"
        [[ ! -f "$solution_file" ]] && echo -e "  ${RED}  Missing solution:${NC} $solution_file"
        [[ ! -f "$original_path" ]] && echo -e "  ${RED}  Missing original:${NC} $original_path"
        return 1
    fi

    return 0
}

# Update job status in jobs.json
update_job_status() {
    local project_id="$1"
    local status="$2"
    local outcome="$3"

    local tmp_file=$(mktemp)
    jq --arg pid "$project_id" --arg status "$status" --arg outcome "$outcome" '
        .jobs |= map(if .project_id == $pid then .status = $status | .outcome = $outcome else . end)
    ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"
}

# Update job status with theorems_proved count
update_job_status_with_theorems() {
    local project_id="$1"
    local status="$2"
    local outcome="$3"
    local theorems_proved="$4"

    local tmp_file=$(mktemp)
    jq --arg pid "$project_id" --arg status "$status" --arg outcome "$outcome" \
       --argjson proved "${theorems_proved:-0}" '
        .jobs |= map(if .project_id == $pid then
            .status = $status | .outcome = $outcome | .theorems_proved = $proved
        else . end)
    ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"
}

# Main logic
main() {
    echo -e "${BLUE}=== Aristotle Retrieve & Integrate ===${NC}"
    echo ""

    if [[ ! -f "$JOBS_FILE" ]]; then
        echo "No jobs file found"
        exit 0
    fi

    # Find completed jobs that haven't been integrated
    local completed_jobs
    completed_jobs=$(jq -c '.jobs[] | select(.status == "completed")' "$JOBS_FILE")

    if [[ -z "$completed_jobs" ]]; then
        echo "No completed jobs to process"

        # Check for jobs that need status update
        echo ""
        echo "Checking submitted jobs for completion..."
        "$SCRIPT_DIR/check-jobs.sh" --update
        exit 0
    fi

    local count=$(echo "$completed_jobs" | wc -l | tr -d ' ')
    echo "Found $count completed jobs to process"
    echo ""

    local integrated=0
    local failed=0

    while IFS= read -r job; do
        [[ -z "$job" ]] && continue

        if integrate_solution "$job"; then
            ((integrated++))
        else
            ((failed++))
        fi
        echo ""
    done <<< "$completed_jobs"

    echo -e "${GREEN}Processed: $integrated${NC}"
    if [[ "$failed" -gt 0 ]]; then
        echo -e "${RED}Failed: $failed${NC}"
    fi
}

main
