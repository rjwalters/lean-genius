#!/bin/bash
#
# check-jobs.sh - Check status of submitted Aristotle jobs
#
# Usage:
#   ./check-jobs.sh              # Check all submitted jobs
#   ./check-jobs.sh --update     # Update job statuses in jobs.json
#   ./check-jobs.sh --json       # Output as JSON
#
# Environment:
#   ARISTOTLE_API_KEY - Required for API access
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

UPDATE_STATUS=false
JSON_OUTPUT=false

# Record that a job reached a terminal state (completed/failed/expired).
# The marker's mtime feeds wedge-check.sh's "no terminal transition in N
# days" detector (issue #43006). REPO_ROOT resolution matches
# aristotle-agent.sh so worktree and main checkout agree on the path.
mark_terminal_transition() {
    local state_dir="${REPO_ROOT:-$PROJECT_ROOT}/.loom/state"
    mkdir -p "$state_dir"
    touch "$state_dir/aristotle-last-terminal"
}

while [[ $# -gt 0 ]]; do
    case $1 in
        --update) UPDATE_STATUS=true; shift ;;
        --json) JSON_OUTPUT=true; shift ;;
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

# --- Aristotle v2 status model -------------------------------------------
# The v2 CLI (aristotlelib >= 1.0) splits status into two levels:
#   * PROJECT status (`aristotle list --status`) is only RUNNING | IDLE.
#     RUNNING = a task is actively searching; IDLE = no task running (terminal
#     from the project's perspective — the task underneath may have COMPLETEd,
#     FAILED, etc.).
#   * TASK status (`aristotle tasks <project-id>` STATUS column, also shown by
#     `aristotle show <project-id>`) carries the fine-grained terminal states:
#     IN_PROGRESS | COMPLETE | COMPLETE_WITH_ERRORS | FAILED | CANCELED | ...
# The removed v1 project-level enums (NOT_STARTED, QUEUED, COMPLETE,
# COMPLETE_WITH_ERRORS, OUT_OF_BUDGET, FAILED, CANCELED) now error out with
# "invalid choice" if passed to `aristotle list --status`. See issue #38098.

# Parse project entries from 'aristotle list' table output.
# v2 columns: ID CREATED NAME STATUS   (STATUS is RUNNING | IDLE)
# The NAME column can contain spaces / a trailing "..." ellipsis, so we read
# the first field (ID) and the LAST field (project STATUS) and ignore the
# middle. `aristotle list` does not report a numeric progress percentage in v2.
parse_list_output() {
    local output="$1"
    while IFS= read -r line; do
        [[ "$line" =~ ^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12} ]] || continue

        local pid proj_status
        pid=$(echo "$line" | awk '{print $1}')
        proj_status=$(echo "$line" | awk '{print $NF}')
        echo "$pid|$proj_status"
    done <<< "$output"
}

# Resolve a project's terminal TASK status via `aristotle tasks <project-id>`.
# Returns the STATUS of the newest task (last column of the first data row),
# e.g. COMPLETE, COMPLETE_WITH_ERRORS, FAILED, IN_PROGRESS. Empty if none.
task_status_for_project() {
    local pid="$1"
    local tasks_output
    tasks_output=$(uvx --from aristotlelib aristotle tasks "$pid" --limit 1 2>/dev/null) || return 0
    echo "$tasks_output" | awk '
        /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}/ { print $NF; exit }
    '
}

# Query the Aristotle server for all projects across all statuses.
# Builds a combined JSON result compatible with the rest of the script.
# Output format: {"submitted": N, "results": [...], "server_projects": [...]}
# Look up a project ID in the server data string.
# Args: project_id, all_server_projects (pipe-delimited lines: pid|status)
# Outputs: status (the resolved task-level status) or empty string if not found
lookup_server_project() {
    local target_pid="$1"
    local server_data="$2"
    awk -F'|' -v target_pid="$target_pid" '$1 == target_pid { print $2; exit }' <<< "$server_data"
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

run_check() {
    local all_server_projects=""

    # v2: enumerate projects at the two valid project-level statuses
    # (RUNNING | IDLE), then resolve each project's fine-grained TASK status.
    # RUNNING projects are in flight; IDLE projects have a terminal task whose
    # exact outcome (COMPLETE / COMPLETE_WITH_ERRORS / FAILED / ...) we read
    # from `aristotle tasks`.
    local raw_projects=""
    for proj_status in RUNNING IDLE; do
        local output
        output=$(uvx --from aristotlelib aristotle list --status "$proj_status" --limit 100 2>&1) || continue

        local parsed
        parsed=$(parse_list_output "$output")
        if [[ -n "$parsed" ]]; then
            if [[ -n "$raw_projects" ]]; then
                raw_projects="$raw_projects
$parsed"
            else
                raw_projects="$parsed"
            fi
        fi
    done

    # Resolve project-level status to task-level status for downstream logic.
    # RUNNING -> keep as IN_PROGRESS (a task is actively searching).
    # IDLE    -> query the task's terminal status; fall back to COMPLETE if the
    #            task lookup yields nothing (idle with an unreadable task).
    while IFS='|' read -r pid proj_status; do
        [[ -z "$pid" ]] && continue
        local resolved
        if [[ "$proj_status" == "RUNNING" ]]; then
            resolved="IN_PROGRESS"
        else
            resolved=$(task_status_for_project "$pid")
            # An IDLE project with no readable task never ran a solve job — the
            # v2 analogue of the old NOT_STARTED "zombie". Flag it with a
            # sentinel so reconciliation can detect it.
            [[ -z "$resolved" ]] && resolved="NO_TASK"
        fi
        if [[ -n "$all_server_projects" ]]; then
            all_server_projects="$all_server_projects
$pid|$resolved"
        else
            all_server_projects="$pid|$resolved"
        fi
    done <<< "$raw_projects"

    # Get submitted jobs from local tracking
    local submitted_jobs
    submitted_jobs=$(jq -c '.jobs[] | select(.status == "submitted")' "$JOBS_FILE" 2>/dev/null)
    local submitted_count=0
    [[ -n "$submitted_jobs" ]] && submitted_count=$(echo "$submitted_jobs" | wc -l | tr -d ' ')

    # Build results JSON for submitted jobs
    local results_json="[]"
    if [[ -n "$submitted_jobs" ]]; then
        while IFS= read -r job; do
            [[ -z "$job" ]] && continue
            local pid prob
            pid=$(echo "$job" | jq -r '.project_id')
            prob=$(echo "$job" | jq -r '.problem_id // "unknown"')

            local server_status="NOT_FOUND"
            # v2 has no numeric progress; retain the field (default 0) so
            # downstream JSON consumers keep working.
            local server_progress="0"
            local server_entry
            server_entry=$(lookup_server_project "$pid" "$all_server_projects")
            if [[ -n "$server_entry" ]]; then
                server_status="$server_entry"
            fi

            results_json=$(echo "$results_json" | jq \
                --arg pid "$pid" --arg prob "$prob" \
                --arg status "$server_status" --argjson percent "${server_progress:-0}" \
                '. += [{"project_id": $pid, "problem_id": $prob, "status": $status, "percent": $percent}]')
        done <<< "$submitted_jobs"
    fi

    # Build server_projects JSON array for reconciliation
    local server_json="[]"
    if [[ -n "$all_server_projects" ]]; then
        while IFS='|' read -r pid status; do
            [[ -z "$pid" ]] && continue
            # CLI list does not provide file_name or numeric progress; use null/0.
            server_json=$(echo "$server_json" | jq \
                --arg pid "$pid" --arg status "$status" \
                '. += [{"project_id": $pid, "status": $status, "percent": 0, "file_name": null}]')
        done <<< "$all_server_projects"
    fi

    # Output combined JSON
    jq -n --argjson submitted "$submitted_count" \
          --argjson results "$results_json" \
          --argjson server "$server_json" \
          '{"submitted": $submitted, "results": $results, "server_projects": $server}'
}

# Categorize failure based on job outcome text and file content
categorize_failure() {
    local pid="$1"

    # Get outcome text from jobs file
    local outcome
    outcome=$(jq -r --arg pid "$pid" '.jobs[] | select(.project_id == $pid) | .outcome // ""' "$JOBS_FILE" 2>/dev/null)
    local file
    file=$(jq -r --arg pid "$pid" '.jobs[] | select(.project_id == $pid) | .file // ""' "$JOBS_FILE" 2>/dev/null)

    # Pattern match on outcome text
    case "$outcome" in
        *"parse"*|*"unexpected token"*|*"syntax"*)
            echo "parse_error" ;;
        *"failed to load"*|*"import"*|*"not found"*)
            echo "load_error" ;;
        *"def.*sorry"*|*"definition sorry"*)
            echo "def_sorry" ;;
        *"placeholder"*|*"True"*)
            echo "placeholder" ;;
        *"axiom"*|*"nothing to prove"*)
            echo "axiom_only" ;;
        *"OPEN"*|*"conjecture"*|*"open problem"*)
            echo "open_problem" ;;
        *"no improvement"*|*"0 theorems"*|*"no progress"*)
            echo "no_improvement" ;;
        *)
            echo "unknown" ;;
    esac
}

# Count how many times a file has been submitted
count_file_submissions() {
    local pid="$1"
    local file
    file=$(jq -r --arg pid "$pid" '.jobs[] | select(.project_id == $pid) | .file // ""' "$JOBS_FILE" 2>/dev/null)

    if [[ -n "$file" ]]; then
        jq --arg file "$file" '[.jobs[] | select(.file == $file)] | length' "$JOBS_FILE" 2>/dev/null
    else
        echo 1
    fi
}

# Update jobs.json with new statuses
update_jobs_file() {
    local results="$1"

    # Parse results and update
    echo "$results" | jq -r '.results[] | "\(.project_id)|\(.status)"' | while IFS='|' read -r pid status; do
        [[ -z "$pid" ]] && continue

        # $status here is the resolved v2 TASK status (from `aristotle tasks`),
        # not a project-level enum. Terminal task states map to local lifecycle
        # states; non-terminal (IN_PROGRESS) and untracked (NO_TASK/NOT_FOUND
        # handled elsewhere) are left alone.
        local new_status
        case "$status" in
            COMPLETE|COMPLETE_WITH_ERRORS) new_status="completed" ;;
            FAILED|OUT_OF_BUDGET) new_status="failed" ;;
            NOT_FOUND|CANCELED) new_status="expired" ;;
            *) continue ;;  # Don't update non-terminal jobs (IN_PROGRESS, NO_TASK)
        esac

        # For failed/expired jobs, categorize the failure and count submissions
        local extra_fields=""
        if [[ "$new_status" == "failed" || "$new_status" == "expired" ]]; then
            local category
            category=$(categorize_failure "$pid")
            local sub_count
            sub_count=$(count_file_submissions "$pid")

            # Update with failure metadata
            local tmp_file=$(mktemp)
            jq --arg pid "$pid" --arg status "$new_status" \
               --arg category "$category" --argjson count "$sub_count" '
                .jobs |= map(if .project_id == $pid then
                    .status = $status |
                    .failure_category = $category |
                    .submission_count = $count
                else . end)
            ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"

            mark_terminal_transition
            echo -e "  Updated $pid -> $new_status (category: $category, submissions: $sub_count)"
        else
            # Update status only
            local tmp_file=$(mktemp)
            jq --arg pid "$pid" --arg status "$new_status" '
                .jobs |= map(if .project_id == $pid then .status = $status else . end)
            ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"

            mark_terminal_transition
            echo -e "  Updated $pid -> $new_status"
        fi
    done
}

# Reconcile server projects: find zombies not tracked locally
reconcile_server_projects() {
    local results="$1"

    # Get all tracked project IDs from jobs.json
    local tracked_ids
    tracked_ids=$(jq -r '.jobs[].project_id // empty' "$JOBS_FILE" | sort -u)

    # Check each server project
    echo "$results" | jq -r '.server_projects[] | "\(.project_id)|\(.status)|\(.file_name)"' | while IFS='|' read -r pid status fname; do
        [[ -z "$pid" ]] && continue

        # Skip if already tracked
        if echo "$tracked_ids" | grep -q "^${pid}$"; then
            continue
        fi

        # Extract problem_id from filename (e.g., Erdos123Problem.lean -> erdos-123)
        local problem_id="recovered-${pid%%-*}"
        if [[ -n "${fname:-}" && "$fname" != "null" ]]; then
            problem_id=$(lean_file_to_problem_id "$fname")
        fi

        if [[ "$status" == "NO_TASK" ]]; then
            # v2 zombie: an IDLE project with no readable solve task — the
            # analogue of the old v1 NOT_STARTED zombie (accepted but never ran).
            echo -e "  ${YELLOW}ZOMBIE:${NC} $pid (IDLE, no task, file: ${fname:-unknown})"

            if [[ "$UPDATE_STATUS" == true ]]; then
                local now
                now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
                local tmp_file
                tmp_file=$(mktemp)
                jq --arg pid "$pid" --arg fname "${fname:-unknown}" --arg now "$now" '
                    .jobs += [{
                        project_id: $pid,
                        file: $fname,
                        problem_id: ("zombie-" + ($pid | split("-") | .[0])),
                        submitted: "unknown",
                        status: "zombie",
                        notes: ("Zombie project discovered by reconciliation at " + $now + ". IDLE with no solve task on server, not tracked locally.")
                    }]
                ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"
                echo -e "    ${GREEN}Added to tracking${NC}"
            fi
        elif [[ "$status" == "IN_PROGRESS" ]]; then
            # Only re-adopt if we can map the filename to a real local proof file
            local can_map_active=false
            if [[ -n "${fname:-}" && "$fname" != "null" ]]; then
                if [[ -f "$PROJECT_ROOT/proofs/Proofs/$fname" ]]; then
                    can_map_active=true
                fi
            fi

            if [[ "$can_map_active" == false ]]; then
                echo -e "  ${YELLOW}SKIP:${NC} $pid ($status, file: ${fname:-unknown}) — cannot map to local proof file, skipping"
                continue
            fi

            # Re-adopt active projects as submitted so the agent monitors them
            echo -e "  ${CYAN}RE-ADOPT:${NC} $pid ($status, file: ${fname:-unknown}) → submitted"

            if [[ "$UPDATE_STATUS" == true ]]; then
                local now
                now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
                local tmp_file
                tmp_file=$(mktemp)
                jq --arg pid "$pid" --arg fname "proofs/Proofs/${fname}" \
                   --arg prob "$problem_id" --arg now "$now" --arg sstat "$status" '
                    .jobs += [{
                        project_id: $pid,
                        file: $fname,
                        problem_id: $prob,
                        submitted: "unknown",
                        status: "submitted",
                        notes: ("Re-adopted " + $sstat + " project during reconciliation at " + $now)
                    }]
                ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"
                echo -e "    ${GREEN}Re-adopted as submitted${NC}"
            fi
        elif [[ "$status" == "COMPLETE" ]]; then
            # Only re-adopt if we can map the filename to a real local proof file
            local can_map=false
            if [[ -n "${fname:-}" && "$fname" != "null" ]]; then
                local proof_basename="${fname%.lean}"
                if [[ -f "$PROJECT_ROOT/proofs/Proofs/$fname" ]]; then
                    can_map=true
                fi
            fi

            if [[ "$can_map" == false ]]; then
                echo -e "  ${YELLOW}SKIP:${NC} $pid (COMPLETE, file: ${fname:-unknown}) — cannot map to local proof file, skipping"
                continue
            fi

            # Re-adopt completed projects for integration
            echo -e "  ${GREEN}RE-ADOPT:${NC} $pid (COMPLETE, file: ${fname:-unknown}) → completed"

            if [[ "$UPDATE_STATUS" == true ]]; then
                local now
                now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
                local tmp_file
                tmp_file=$(mktemp)
                jq --arg pid "$pid" --arg fname "proofs/Proofs/${fname}" \
                   --arg prob "$problem_id" --arg now "$now" '
                    .jobs += [{
                        project_id: $pid,
                        file: $fname,
                        problem_id: $prob,
                        submitted: "unknown",
                        status: "completed",
                        notes: ("Re-adopted COMPLETE project during reconciliation at " + $now)
                    }]
                ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"
                echo -e "    ${GREEN}Re-adopted as completed${NC}"
            fi
        fi
    done
}

# Main logic
main() {
    if [[ ! -f "$JOBS_FILE" ]]; then
        echo "No jobs file found"
        exit 0
    fi

    local output
    output=$(run_check)

    # Check for errors
    if echo "$output" | jq -e '.error' >/dev/null 2>&1; then
        local error=$(echo "$output" | jq -r '.error')
        echo -e "${RED}API Error: $error${NC}" >&2
        exit 1
    fi

    if [[ "$JSON_OUTPUT" == true ]]; then
        echo "$output"
        exit 0
    fi

    local submitted=$(echo "$output" | jq -r '.submitted')

    echo -e "${BLUE}=== Aristotle Job Status ===${NC}"
    echo ""

    if [[ "$submitted" == "0" ]]; then
        echo -e "${GREEN}No pending jobs${NC}"

        # Show summary
        local completed=$(jq '[.jobs[] | select(.status == "completed")] | length' "$JOBS_FILE")
        local integrated=$(jq '[.jobs[] | select(.status == "integrated")] | length' "$JOBS_FILE")
        local failed=$(jq '[.jobs[] | select(.status == "failed")] | length' "$JOBS_FILE")
        local expired=$(jq '[.jobs[] | select(.status == "expired")] | length' "$JOBS_FILE")
        local zombies=$(jq '[.jobs[] | select(.status == "zombie")] | length' "$JOBS_FILE")

        echo ""
        echo "Summary:"
        echo "  Completed: $completed"
        echo "  Integrated: $integrated"
        echo "  Failed: $failed"
        echo "  Expired: $expired"
        if [[ "$zombies" -gt 0 ]]; then
            echo -e "  ${YELLOW}Zombies: $zombies${NC}"
        fi
    else
        echo "Submitted jobs: $submitted"
        echo ""

        # Display results
        echo "$output" | jq -r '.results[] | "\(.problem_id)|\(.status)|\(.percent)"' | while IFS='|' read -r prob status percent; do
            case "$status" in
                COMPLETE)
                    echo -e "  ${GREEN}$prob${NC}: COMPLETE"
                    ;;
                IN_PROGRESS)
                    echo -e "  ${YELLOW}$prob${NC}: IN_PROGRESS"
                    ;;
                NO_TASK)
                    echo -e "  ${CYAN}$prob${NC}: IDLE (no solve task — possible zombie)"
                    ;;
                COMPLETE_WITH_ERRORS)
                    echo -e "  ${YELLOW}$prob${NC}: COMPLETE_WITH_ERRORS (results may be partial)"
                    ;;
                FAILED|OUT_OF_BUDGET)
                    echo -e "  ${RED}$prob${NC}: $status"
                    ;;
                NOT_FOUND|CANCELED)
                    echo -e "  ${RED}$prob${NC}: $status (expired?)"
                    ;;
                *)
                    echo -e "  $prob: $status ($percent%)"
                    ;;
            esac
        done

        # Update if requested
        if [[ "$UPDATE_STATUS" == true ]]; then
            echo ""
            echo "Updating job statuses..."
            update_jobs_file "$output"
        fi
    fi

    # Reconcile server projects (find zombies) - always runs
    local server_count
    server_count=$(echo "$output" | jq '.server_projects | length')
    if [[ "$server_count" -gt 0 ]]; then
        echo ""
        echo -e "${BLUE}Server reconciliation:${NC} $server_count projects on server"
        reconcile_server_projects "$output"
    fi
}

main
