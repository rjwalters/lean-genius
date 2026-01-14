#!/bin/bash
#
# aristotle-status.sh - Check status of all Aristotle jobs
#
# Usage:
#   ./aristotle-status.sh              # Check all pending jobs
#   ./aristotle-status.sh --retrieve   # Also retrieve completed solutions
#   ./aristotle-status.sh --json       # Output as JSON (for scripts)
#
# Requires: ARISTOTLE_API_KEY environment variable
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"
RESULTS_DIR="$PROJECT_ROOT/aristotle-results/new"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

RETRIEVE=false
JSON_OUTPUT=false

for arg in "$@"; do
    case $arg in
        --retrieve) RETRIEVE=true ;;
        --json) JSON_OUTPUT=true ;;
    esac
done

# Check ARISTOTLE_API_KEY
if [ -z "$ARISTOTLE_API_KEY" ]; then
    # Try to load from common locations
    if [ -f "$HOME/.aristotle_key" ]; then
        export ARISTOTLE_API_KEY=$(cat "$HOME/.aristotle_key")
    elif grep -q "ARISTOTLE_API_KEY" "$HOME/.zshrc" 2>/dev/null; then
        export ARISTOTLE_API_KEY=$(grep ARISTOTLE_API_KEY "$HOME/.zshrc" | cut -d'=' -f2 | tr -d '"')
    fi
fi

if [ -z "$ARISTOTLE_API_KEY" ]; then
    echo -e "${RED}ERROR: ARISTOTLE_API_KEY not set${NC}" >&2
    exit 1
fi

# Create results directory if needed
mkdir -p "$RESULTS_DIR"

# Python script to check all jobs
PYTHON_SCRIPT='
import asyncio
import json
import sys
import os
from aristotlelib import Project

async def check_all():
    jobs_file = sys.argv[1]
    retrieve = sys.argv[2] == "true"
    results_dir = sys.argv[3]

    with open(jobs_file) as f:
        data = json.load(f)

    # Get submitted jobs
    submitted = [j for j in data.get("jobs", []) if j.get("status") == "submitted"]

    if not submitted:
        print(json.dumps({"submitted": [], "results": []}))
        return

    # Check status via API
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
            status = p.status.name
            percent = p.percent_complete or 0

            result = {
                "problem_id": problem_id,
                "project_id": pid[:8],
                "status": status,
                "percent": percent,
                "file_name": p.file_name
            }

            # Retrieve if complete and requested
            if status == "COMPLETE" and retrieve:
                try:
                    base = os.path.basename(p.file_name or f"{problem_id}.lean")
                    output = os.path.join(results_dir, base.replace(".lean", "-solved.lean"))
                    await p.get_solution(output)
                    result["retrieved"] = output
                except Exception as e:
                    result["retrieve_error"] = str(e)

            results.append(result)
        else:
            results.append({
                "problem_id": problem_id,
                "project_id": pid[:8] if pid else "unknown",
                "status": "NOT_FOUND",
                "percent": 0
            })

    print(json.dumps({"submitted": len(submitted), "results": results}))

asyncio.run(check_all())
'

# Run the Python script
OUTPUT=$(uvx --from aristotlelib python3 -c "$PYTHON_SCRIPT" "$JOBS_FILE" "$RETRIEVE" "$RESULTS_DIR" 2>&1)

# Check for errors
if echo "$OUTPUT" | grep -q '"error"'; then
    ERROR=$(echo "$OUTPUT" | jq -r '.error')
    echo -e "${RED}API Error: $ERROR${NC}" >&2
    exit 1
fi

# JSON output mode
if [ "$JSON_OUTPUT" = true ]; then
    echo "$OUTPUT"
    exit 0
fi

# Pretty print results
echo ""
echo "============================================"
echo -e "${CYAN}Aristotle Job Status${NC}"
echo "============================================"
echo ""

SUBMITTED=$(echo "$OUTPUT" | jq -r '.submitted')
if [ "$SUBMITTED" = "0" ] || [ "$SUBMITTED" = "[]" ]; then
    echo -e "${GREEN}No pending jobs.${NC}"
    echo ""
    # Show completed count
    COMPLETED=$(jq '.jobs | map(select(.status == "completed")) | length' "$JOBS_FILE")
    echo "Completed jobs: $COMPLETED"
    exit 0
fi

echo "$OUTPUT" | jq -r '.results[] | "\(.problem_id)|\(.project_id)|\(.status)|\(.percent)|\(.retrieved // "")"' | while IFS='|' read -r problem_id project_id status percent retrieved; do
    echo -e "${BLUE}$problem_id${NC} ($project_id...)"

    case "$status" in
        COMPLETE)
            if [ -n "$retrieved" ]; then
                echo -e "  Status: ${GREEN}COMPLETE${NC} - Retrieved to $retrieved"
            else
                echo -e "  Status: ${GREEN}COMPLETE${NC} - Ready to retrieve (use --retrieve)"
            fi
            ;;
        IN_PROGRESS)
            echo -e "  Status: ${YELLOW}IN_PROGRESS${NC} ($percent%)"
            ;;
        QUEUED|NOT_STARTED)
            echo -e "  Status: ${CYAN}QUEUED${NC}"
            ;;
        FAILED)
            echo -e "  Status: ${RED}FAILED${NC}"
            ;;
        NOT_FOUND)
            echo -e "  Status: ${RED}NOT_FOUND${NC} (job may have expired)"
            ;;
        *)
            echo -e "  Status: $status ($percent%)"
            ;;
    esac
    echo ""
done

echo "============================================"
echo "Run with --retrieve to download completed solutions"
echo "============================================"
