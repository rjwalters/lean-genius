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

# Parse project entries from 'aristotle list' table output.
parse_list_entries() {
    local output="$1"
    echo "$output" | grep -E '^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' | while read -r line; do
        local pid status progress
        pid=$(echo "$line" | awk '{print $1}')
        status=$(echo "$line" | awk '{print $2}')
        progress=$(echo "$line" | awk '{print $NF}' | sed 's/%//')
        [[ "$progress" == "-" ]] && progress="0"
        echo "$pid|$status|$progress"
    done
}

# Build a server project map from all statuses via CLI
build_server_map() {
    local all_statuses="NOT_STARTED QUEUED IN_PROGRESS COMPLETE COMPLETE_WITH_ERRORS OUT_OF_BUDGET FAILED CANCELED"
    for status in $all_statuses; do
        local output
        output=$(uvx --from aristotlelib aristotle list --status "$status" --limit 100 2>&1) || continue
        parse_list_entries "$output"
    done
}

# Look up a project ID in server data (pipe-delimited: pid|status|progress)
lookup_server_entry() {
    local target_pid="$1"
    local server_data="$2"
    echo "$server_data" | grep "^${target_pid}|" | head -1 | cut -d'|' -f2-
}

# Run the status check using CLI
check_and_build_output() {
    # Build server data (pipe-delimited lines: pid|status|progress)
    local server_data
    server_data=$(build_server_map)

    # Get submitted jobs from local tracking
    local submitted_jobs
    submitted_jobs=$(jq -c '.jobs[] | select(.status == "submitted")' "$JOBS_FILE" 2>/dev/null)

    if [[ -z "$submitted_jobs" ]]; then
        echo '{"submitted": 0, "results": []}'
        return
    fi

    local submitted_count
    submitted_count=$(echo "$submitted_jobs" | wc -l | tr -d ' ')

    # Build results
    local results_json="[]"
    while IFS= read -r job; do
        [[ -z "$job" ]] && continue
        local pid prob
        pid=$(echo "$job" | jq -r '.project_id')
        prob=$(echo "$job" | jq -r '.problem_id // "unknown"')

        local server_status="NOT_FOUND"
        local server_progress="0"
        local retrieved=""

        local server_entry
        server_entry=$(lookup_server_entry "$pid" "$server_data")
        if [[ -n "$server_entry" ]]; then
            server_status=$(echo "$server_entry" | cut -d'|' -f1)
            server_progress=$(echo "$server_entry" | cut -d'|' -f2)
        fi

        # Retrieve if complete and requested
        if [[ "$server_status" == "COMPLETE" && "$RETRIEVE" == true ]]; then
            local base="${prob}.lean"
            local output_file="$RESULTS_DIR/${base%.lean}-solved.lean"

            local retrieve_result
            retrieve_result=$(retrieve_solution_cli "$pid" "$output_file" 2>&1)
            if echo "$retrieve_result" | grep -q "SUCCESS"; then
                retrieved="$output_file"
            fi
        fi

        results_json=$(echo "$results_json" | jq \
            --arg pid "${pid:0:8}" --arg prob "$prob" \
            --arg status "$server_status" --argjson percent "${server_progress:-0}" \
            --arg retrieved "$retrieved" \
            '. += [{"project_id": $pid, "problem_id": $prob, "status": $status, "percent": $percent, "retrieved": (if $retrieved != "" then $retrieved else null end)}]')
    done <<< "$submitted_jobs"

    jq -n --argjson submitted "$submitted_count" --argjson results "$results_json" \
        '{"submitted": $submitted, "results": $results}'
}

# Retrieve a solution using the CLI (for --retrieve mode)
retrieve_solution_cli() {
    local project_id="$1"
    local output_path="$2"

    local tmp_dir
    tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/aristotle-retrieve-XXXXXX")
    local archive_path="$tmp_dir/result.tar.gz"

    local cli_output
    cli_output=$(uvx --from aristotlelib aristotle result "$project_id" --destination "$archive_path" 2>&1) || {
        rm -rf "$tmp_dir"
        echo "ERROR: Failed to retrieve $project_id"
        return 1
    }

    # Extract lean file from archive
    local extract_dir="$tmp_dir/extracted"
    mkdir -p "$extract_dir"

    if file "$archive_path" | grep -q "gzip"; then
        gunzip -f "$archive_path" 2>/dev/null
        local tar_path="${archive_path%.gz}"
        [[ ! -f "$tar_path" ]] && tar_path="$archive_path"
        tar xf "$tar_path" -C "$extract_dir" 2>/dev/null
    elif file "$archive_path" | grep -q "tar"; then
        tar xf "$archive_path" -C "$extract_dir" 2>/dev/null
    else
        cp "$archive_path" "$extract_dir/output.lean" 2>/dev/null
    fi

    local lean_file
    lean_file=$(find "$extract_dir" -name "*.lean" -type f | head -1)

    if [[ -n "$lean_file" && -f "$lean_file" ]]; then
        cp "$lean_file" "$output_path"
        rm -rf "$tmp_dir"
        echo "SUCCESS: Retrieved to $output_path"
        return 0
    else
        rm -rf "$tmp_dir"
        echo "ERROR: No lean file in result archive"
        return 1
    fi
}

OUTPUT=$(check_and_build_output)

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
