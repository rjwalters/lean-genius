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

# Retrieve a single solution using the Aristotle CLI.
# The CLI downloads a gzip tar archive; we extract the lean file from it.
retrieve_solution() {
    local project_id="$1"
    local output_path="$2"

    local tmp_dir
    tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/aristotle-retrieve-XXXXXX")
    local archive_path="$tmp_dir/result.tar.gz"

    # Download the result archive
    local cli_output
    cli_output=$(uvx --from aristotlelib aristotle result "$project_id" --destination "$archive_path" 2>&1) || {
        rm -rf "$tmp_dir"
        # Check for common error patterns
        if echo "$cli_output" | grep -qi "not found\|404\|does not exist"; then
            echo "ERROR: Project $project_id not found on server"
        else
            echo "ERROR: Failed to retrieve $project_id: $cli_output"
        fi
        return 1
    }

    # The result is a gzip-compressed tar archive containing output.lean
    local extract_dir="$tmp_dir/extracted"
    mkdir -p "$extract_dir"

    # Decompress and extract
    if file "$archive_path" | grep -q "gzip"; then
        gunzip -f "$archive_path" 2>/dev/null
        local tar_path="${archive_path%.gz}"
        [[ ! -f "$tar_path" ]] && tar_path="$archive_path"  # gunzip may rename in place
        tar xf "$tar_path" -C "$extract_dir" 2>/dev/null || {
            rm -rf "$tmp_dir"
            echo "ERROR: Failed to extract archive for $project_id"
            return 1
        }
    elif file "$archive_path" | grep -q "tar"; then
        tar xf "$archive_path" -C "$extract_dir" 2>/dev/null || {
            rm -rf "$tmp_dir"
            echo "ERROR: Failed to extract archive for $project_id"
            return 1
        }
    else
        # Might be a plain lean file
        cp "$archive_path" "$extract_dir/output.lean" 2>/dev/null || {
            rm -rf "$tmp_dir"
            echo "ERROR: Unknown file format for result of $project_id"
            return 1
        }
    fi

    # Find the lean file in the extracted directory
    local lean_file
    lean_file=$(find "$extract_dir" -name "*.lean" -type f | head -1)

    if [[ -z "$lean_file" || ! -f "$lean_file" ]]; then
        rm -rf "$tmp_dir"
        echo "ERROR: No .lean file found in result archive for $project_id"
        return 1
    fi

    # Copy to the desired output path
    cp "$lean_file" "$output_path"
    rm -rf "$tmp_dir"

    echo "SUCCESS: Retrieved to $output_path"
    return 0
}

# Safety check: refuse to overwrite a file if the solution looks like companion
# content or is drastically shorter (prevents destroying main formalizations).
# Returns 0 if safe to overwrite, 1 if blocked.
safe_to_overwrite() {
    local original="$1"
    local solution="$2"

    local orig_lines sol_lines
    orig_lines=$(wc -l < "$original" 2>/dev/null | tr -d ' ')
    sol_lines=$(wc -l < "$solution" 2>/dev/null | tr -d ' ')

    # Guard 1: If the solution contains "Aristotle targets" header, it is companion
    # content and must only overwrite *Aristotle.lean files, never *Problem.lean
    if grep -q "Aristotle targets" "$solution" 2>/dev/null; then
        local orig_basename
        orig_basename=$(basename "$original")
        if [[ "$orig_basename" != *Aristotle* ]]; then
            echo -e "  ${RED}BLOCKED:${NC} Solution contains 'Aristotle targets' header but target is $orig_basename (not a companion file)"
            echo -e "  ${RED}  This would overwrite the main formalization with companion content${NC}"
            return 1
        fi
    fi

    # Guard 2: If the solution is less than 50% of the original's line count,
    # refuse to overwrite — this catches content regression from mismatched files
    if [[ "$orig_lines" -gt 20 && "$sol_lines" -gt 0 ]]; then
        local ratio=$((sol_lines * 100 / orig_lines))
        if [[ "$ratio" -lt 50 ]]; then
            echo -e "  ${RED}BLOCKED:${NC} Solution is $sol_lines lines vs original $orig_lines lines (${ratio}%% of original)"
            echo -e "  ${RED}  Refusing to overwrite — possible file mismatch${NC}"
            return 1
        fi
    fi

    return 0
}

# Count sorries in a file
count_sorries() {
    local count
    count=$(grep -c "sorry" "$1" 2>/dev/null) || true
    echo "${count:-0}"
}

# Count theorems proved (sorries eliminated) by comparing original and solution
count_theorems_proved() {
    local original="$1"
    local solution="$2"

    # Count sorry occurrences in each file (grep -c counts lines, but that's close enough)
    local orig_count new_count
    orig_count=$(grep -c "sorry" "$original" 2>/dev/null || echo 0)
    orig_count=${orig_count//[^0-9]/}
    new_count=$(grep -c "sorry" "$solution" 2>/dev/null || echo 0)
    new_count=${new_count//[^0-9]/}

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
                # Safety check: refuse if solution looks like companion content
                # overwriting a main file, or is drastically shorter
                if ! safe_to_overwrite "$original_path" "$solution_file"; then
                    echo -e "  ${RED}Skipping integration for safety${NC}"
                    mv "$solution_file" "$PROCESSED_DIR/" 2>/dev/null || true
                    update_job_status "$project_id" "blocked" "Safety check failed: possible file mismatch (see issue #8061)"
                    return 1
                fi

                # Backup original
                cp "$original_path" "$original_path.bak"

                # Copy solution
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

# Recover completed jobs from the Aristotle server that are not tracked locally.
# Downloads each result, maps it to a local proof file, and integrates if possible.
recover_server_completed() {
    echo -e "${BLUE}=== Recovering Completed Server Jobs ===${NC}"
    echo ""

    # Get completed projects from server
    local output
    output=$(uvx --from aristotlelib aristotle list --status COMPLETE --limit 100 2>&1) || {
        echo -e "${RED}Failed to query server for completed projects${NC}"
        return 1
    }

    # Parse project IDs from the table output
    local server_ids
    server_ids=$(echo "$output" | grep -oE '^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' 2>/dev/null)

    if [[ -z "$server_ids" ]]; then
        echo "No completed projects found on server"
        return 0
    fi

    local total_server
    total_server=$(echo "$server_ids" | wc -l | tr -d ' ')
    echo "Found $total_server completed projects on server"

    # Get locally tracked project IDs
    local tracked_ids
    tracked_ids=$(jq -r '.jobs[].project_id // empty' "$JOBS_FILE" 2>/dev/null | sort -u)

    local recovered=0
    local skipped=0
    local failed_recover=0

    while IFS= read -r pid; do
        [[ -z "$pid" ]] && continue

        # Skip if already tracked locally
        if echo "$tracked_ids" | grep -q "^${pid}$"; then
            continue
        fi

        echo -e "${CYAN}Recovering:${NC} $pid"

        if [[ "$DRY_RUN" == true ]]; then
            echo -e "  ${YELLOW}[DRY RUN]${NC} Would attempt recovery"
            ((recovered++))
            continue
        fi

        # Download the result to a temp location
        local tmp_solution
        tmp_solution=$(mktemp "${TMPDIR:-/tmp}/aristotle-recover-XXXXXX.lean")
        local result
        result=$(retrieve_solution "$pid" "$tmp_solution")

        if echo "$result" | grep -q "ERROR"; then
            echo -e "  ${RED}Failed to retrieve:${NC} $result"
            rm -f "$tmp_solution"
            ((failed_recover++))
            continue
        fi

        # Try to identify the original file from the solution content
        # Look for filename hints in the Aristotle header comment
        local original_basename=""
        original_basename=$(sed -nE 's/.*project request had uuid: (.*)/\1/p' "$tmp_solution" 2>/dev/null | head -1) || true

        # Try to find the Lean module name from the file content
        # Look for namespace or import patterns that might hint at the original file
        local lean_basename=""
        # Check if there's a namespace declaration
        lean_basename=$(sed -nE 's/^namespace[[:space:]]+([A-Za-z0-9_]+).*/\1/p' "$tmp_solution" 2>/dev/null | head -1) || true

        # Try to map the namespace to a file
        local target_file=""
        if [[ -n "$lean_basename" ]]; then
            # Check common naming patterns
            for candidate in "$PROOFS_DIR/${lean_basename}.lean" "$PROOFS_DIR/${lean_basename}Problem.lean" "$PROOFS_DIR/${lean_basename}Aristotle.lean"; do
                if [[ -f "$candidate" ]]; then
                    target_file="$candidate"
                    break
                fi
            done
        fi

        # Fallback 1: try "import Proofs.XXX" patterns in the file content
        if [[ -z "$target_file" ]]; then
            local module_name=""
            module_name=$(sed -nE 's/^import[[:space:]]+Proofs\.([A-Za-z0-9_]+).*/\1/p' "$tmp_solution" 2>/dev/null | head -1) || true
            if [[ -n "$module_name" && -f "$PROOFS_DIR/${module_name}.lean" ]]; then
                target_file="$PROOFS_DIR/${module_name}.lean"
            fi
        fi

        # Fallback 2: extract Erdos problem number from file content and try
        # common filename patterns. Most solution files reference "Erdos Problem #NNN"
        # or use "ErdosNNN" in definitions/theorems even without a namespace.
        if [[ -z "$target_file" ]]; then
            local erdos_num=""
            # Try: "Erdős Problem #NNN" or "Erdos Problem #NNN" in comments
            erdos_num=$(sed -nE 's/.*(Erdős|Erdos)[[:space:]]+Problem[[:space:]]+#([0-9]+).*/\2/p' "$tmp_solution" 2>/dev/null | head -1) || true
            # Try: "erdosproblems.com/NNN" URL
            if [[ -z "$erdos_num" ]]; then
                erdos_num=$(sed -nE 's/.*erdosproblems\.com\/([0-9]+).*/\1/p' "$tmp_solution" 2>/dev/null | head -1) || true
            fi
            # Try: "ErdosNNN" in definition/theorem names
            if [[ -z "$erdos_num" ]]; then
                erdos_num=$(grep -oE 'Erdos[0-9]+' "$tmp_solution" 2>/dev/null | head -1 | grep -oE '[0-9]+') || true
            fi

            if [[ -n "$erdos_num" ]]; then
                for candidate in \
                    "$PROOFS_DIR/Erdos${erdos_num}Problem.lean" \
                    "$PROOFS_DIR/Erdos${erdos_num}Aristotle.lean" \
                    "$PROOFS_DIR/Erdos${erdos_num}ProblemProvable.lean" \
                    "$PROOFS_DIR/Erdos${erdos_num}.lean"; do
                    if [[ -f "$candidate" ]]; then
                        target_file="$candidate"
                        break
                    fi
                done
            fi
        fi

        # Fallback 3: if namespace was found but didn't match directly, try
        # with "Erdos" prefix variations (e.g., namespace "Erdos1005" -> Erdos1005Problem.lean)
        if [[ -z "$target_file" && -n "$lean_basename" ]]; then
            for candidate in \
                "$PROOFS_DIR/${lean_basename}Problem.lean" \
                "$PROOFS_DIR/${lean_basename}Aristotle.lean" \
                "$PROOFS_DIR/${lean_basename}ProblemProvable.lean"; do
                if [[ -f "$candidate" ]]; then
                    target_file="$candidate"
                    break
                fi
            done
        fi

        # Fallback 4: "See XYZ.lean" docstring hint
        # Many companion files contain "See AreaOfCircleOQ01OQ03.lean for the main formalization."
        if [[ -z "$target_file" ]]; then
            local see_ref=""
            see_ref=$(sed -nE 's/.*See ([A-Z][A-Za-z0-9]+)\.lean.*/\1/p' "$tmp_solution" 2>/dev/null | head -1) || true
            if [[ -n "$see_ref" ]]; then
                for candidate in \
                    "$PROOFS_DIR/${see_ref}Aristotle.lean" \
                    "$PROOFS_DIR/${see_ref}.lean" \
                    "$PROOFS_DIR/${see_ref}Problem.lean"; do
                    if [[ -f "$candidate" ]]; then
                        target_file="$candidate"
                        break
                    fi
                done
            fi
        fi

        # Fallback 5: fuzzy namespace prefix matching
        # e.g., namespace "DescartesRuleOQ01" might match "DescartesRuleOfSignsOQ01.lean"
        if [[ -z "$target_file" && -n "$lean_basename" ]]; then
            local prefix
            prefix=$(echo "$lean_basename" | sed -E 's/(OQ[0-9].*|Aristotle)$//')
            if [[ -n "$prefix" && ${#prefix} -ge 5 ]]; then
                local fuzzy_match
                fuzzy_match=$(ls "$PROOFS_DIR"/ 2>/dev/null | grep -i "^${prefix}" | head -1) || true
                if [[ -n "$fuzzy_match" && -f "$PROOFS_DIR/$fuzzy_match" ]]; then
                    target_file="$PROOFS_DIR/$fuzzy_match"
                fi
            fi
        fi

        # Fallback 6: LLM-powered file mapping
        if [[ -z "$target_file" ]] && [[ -x "$SCRIPT_DIR/llm-map-file.sh" ]]; then
            echo -e "  ${CYAN}Attempting LLM mapping...${NC}"
            local llm_result
            llm_result=$("$SCRIPT_DIR/llm-map-file.sh" "$tmp_solution" 2>/dev/null) || true
            if [[ -n "$llm_result" && "$llm_result" != "UNMAPPED" ]]; then
                local llm_target="$PROOFS_DIR/$llm_result"
                if [[ -f "$llm_target" ]]; then
                    target_file="$llm_target"
                    echo -e "  ${GREEN}LLM mapped to:${NC} $target_file"
                else
                    echo -e "  ${YELLOW}LLM suggested $llm_result but file not found${NC}"
                fi
            else
                echo -e "  ${YELLOW}LLM could not map file${NC}"
            fi
        fi

        if [[ -z "$target_file" ]]; then
            echo -e "  ${YELLOW}Cannot map to local file (all fallbacks exhausted), saving to results${NC}"
            mv "$tmp_solution" "$RESULTS_DIR/recovered-${pid}.lean"

            # Track in jobs.json
            local now
            now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
            local tmp_file
            tmp_file=$(mktemp)
            jq --arg pid "$pid" --arg now "$now" '
                .jobs += [{
                    project_id: $pid,
                    file: "unknown",
                    problem_id: ("recovered-" + ($pid | split("-") | .[0])),
                    submitted: "unknown",
                    status: "completed",
                    notes: ("Recovered from server at " + $now + ". File mapping unknown — saved to aristotle-results/new/")
                }]
            ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"

            ((recovered++))
            continue
        fi

        local target_basename
        target_basename=$(basename "$target_file" .lean)
        local problem_id
        problem_id=$(echo "$target_basename" | sed 's/Problem$//' | sed 's/Aristotle$//' | tr '[:upper:]' '[:lower:]' | sed 's/erdos/erdos-/')

        echo -e "  ${GREEN}Mapped to:${NC} $target_file"

        # Compare sorry counts
        local orig_sorries new_sorries
        orig_sorries=$(count_sorries "$target_file")
        new_sorries=$(count_sorries "$tmp_solution")

        echo -e "  Original sorries: $orig_sorries, Solution sorries: $new_sorries"

        local now
        now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

        if [[ "$new_sorries" -lt "$orig_sorries" ]]; then
            local theorems_proved=$((orig_sorries - new_sorries))
            echo -e "  ${GREEN}Improvement!${NC} ($theorems_proved theorems proved)"

            # Safety check before overwriting
            if ! safe_to_overwrite "$target_file" "$tmp_solution"; then
                echo -e "  ${RED}Skipping recovery for safety${NC}"
                mv "$tmp_solution" "$PROCESSED_DIR/recovered-${pid}-blocked.lean"
                ((failed_recover++))
                continue
            fi

            # Backup and integrate
            cp "$target_file" "$target_file.bak"
            cp "$tmp_solution" "$target_file"
            mv "$tmp_solution" "$PROCESSED_DIR/recovered-${pid}.lean"

            # Track in jobs.json
            local tmp_jq
            tmp_jq=$(mktemp)
            jq --arg pid "$pid" --arg file "proofs/Proofs/${target_basename}.lean" \
               --arg prob "$problem_id" --arg now "$now" \
               --argjson proved "$theorems_proved" '
                .jobs += [{
                    project_id: $pid,
                    file: $file,
                    problem_id: $prob,
                    submitted: "unknown",
                    status: "integrated",
                    outcome: ("\($proved) theorems proved via server recovery"),
                    theorems_proved: $proved,
                    notes: ("Recovered and integrated from server at " + $now)
                }]
            ' "$JOBS_FILE" > "$tmp_jq" && mv "$tmp_jq" "$JOBS_FILE"

            ((recovered++))
        else
            echo -e "  ${YELLOW}No improvement${NC}"
            mv "$tmp_solution" "$PROCESSED_DIR/recovered-${pid}.lean"

            # Track in jobs.json
            local tmp_jq
            tmp_jq=$(mktemp)
            jq --arg pid "$pid" --arg file "proofs/Proofs/${target_basename}.lean" \
               --arg prob "$problem_id" --arg now "$now" '
                .jobs += [{
                    project_id: $pid,
                    file: $file,
                    problem_id: $prob,
                    submitted: "unknown",
                    status: "completed",
                    outcome: "No improvement (recovered from server)",
                    notes: ("Recovered from server at " + $now + ". No sorry reduction.")
                }]
            ' "$JOBS_FILE" > "$tmp_jq" && mv "$tmp_jq" "$JOBS_FILE"

            ((skipped++))
        fi
    done <<< "$server_ids"

    echo ""
    echo -e "${GREEN}Recovered: $recovered${NC}"
    if [[ "$skipped" -gt 0 ]]; then
        echo -e "${YELLOW}No improvement: $skipped${NC}"
    fi
    if [[ "$failed_recover" -gt 0 ]]; then
        echo -e "${RED}Failed: $failed_recover${NC}"
    fi
}

# Main logic
main() {
    echo -e "${BLUE}=== Aristotle Retrieve & Integrate ===${NC}"
    echo ""

    if [[ ! -f "$JOBS_FILE" ]]; then
        echo '{"jobs": []}' > "$JOBS_FILE"
    fi

    # Find completed jobs that haven't been integrated
    local completed_jobs
    completed_jobs=$(jq -c '.jobs[] | select(.status == "completed")' "$JOBS_FILE")

    if [[ -z "$completed_jobs" ]]; then
        echo "No locally tracked completed jobs to process"

        # Check for jobs that need status update
        echo ""
        echo "Checking submitted jobs for completion..."
        "$SCRIPT_DIR/check-jobs.sh" --update

        # Re-check after status update
        completed_jobs=$(jq -c '.jobs[] | select(.status == "completed")' "$JOBS_FILE")
    fi

    local integrated=0
    local failed=0

    if [[ -n "$completed_jobs" ]]; then
        local count=$(echo "$completed_jobs" | wc -l | tr -d ' ')
        echo "Found $count completed jobs to process"
        echo ""

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
    fi

    # Also attempt to recover untracked completed jobs from the server
    echo ""
    recover_server_completed
}

main
