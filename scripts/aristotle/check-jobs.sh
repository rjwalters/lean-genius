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

# Python script to check job status
PYTHON_CHECK='
import asyncio
import json
import sys
from aristotlelib import Project

async def check_jobs():
    jobs_file = sys.argv[1]

    with open(jobs_file) as f:
        data = json.load(f)

    submitted = [j for j in data.get("jobs", []) if j.get("status") == "submitted"]

    if not submitted:
        print(json.dumps({"submitted": 0, "results": []}))
        return

    try:
        projects, _ = await Project.list_projects()
        project_map = {p.project_id: p for p in projects}
    except Exception as e:
        print(json.dumps({"error": str(e)}))
        return

    results = []
    for job in submitted:
        pid = job.get("project_id")
        problem_id = job.get("problem_id", "unknown")

        if pid in project_map:
            p = project_map[pid]
            results.append({
                "problem_id": problem_id,
                "project_id": pid,
                "status": p.status.name,
                "percent": p.percent_complete or 0
            })
        else:
            results.append({
                "problem_id": problem_id,
                "project_id": pid,
                "status": "NOT_FOUND",
                "percent": 0
            })

    print(json.dumps({"submitted": len(submitted), "results": results}))

asyncio.run(check_jobs())
'

# Run status check
run_check() {
    uvx --from aristotlelib python3 -c "$PYTHON_CHECK" "$JOBS_FILE" 2>&1
}

# Update jobs.json with new statuses
update_jobs_file() {
    local results="$1"

    # Parse results and update
    echo "$results" | jq -r '.results[] | "\(.project_id)|\(.status)"' | while IFS='|' read -r pid status; do
        [[ -z "$pid" ]] && continue

        local new_status
        case "$status" in
            COMPLETE) new_status="completed" ;;
            FAILED) new_status="failed" ;;
            *) continue ;;  # Don't update in-progress jobs
        esac

        # Update in jobs file
        local tmp_file=$(mktemp)
        jq --arg pid "$pid" --arg status "$new_status" '
            .jobs |= map(if .project_id == $pid then .status = $status else . end)
        ' "$JOBS_FILE" > "$tmp_file" && mv "$tmp_file" "$JOBS_FILE"

        echo -e "  Updated $pid -> $new_status"
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

        echo ""
        echo "Summary:"
        echo "  Completed: $completed"
        echo "  Integrated: $integrated"
        echo "  Failed: $failed"
        exit 0
    fi

    echo "Submitted jobs: $submitted"
    echo ""

    # Display results
    local complete_count=0
    local in_progress_count=0
    local failed_count=0

    echo "$output" | jq -r '.results[] | "\(.problem_id)|\(.status)|\(.percent)"' | while IFS='|' read -r prob status percent; do
        case "$status" in
            COMPLETE)
                echo -e "  ${GREEN}$prob${NC}: COMPLETE"
                ;;
            IN_PROGRESS)
                echo -e "  ${YELLOW}$prob${NC}: IN_PROGRESS ($percent%)"
                ;;
            QUEUED|NOT_STARTED)
                echo -e "  ${CYAN}$prob${NC}: QUEUED"
                ;;
            FAILED)
                echo -e "  ${RED}$prob${NC}: FAILED"
                ;;
            NOT_FOUND)
                echo -e "  ${RED}$prob${NC}: NOT_FOUND (expired?)"
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
}

main
