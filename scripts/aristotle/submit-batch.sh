#!/bin/bash
#
# submit-batch.sh - Submit a batch of files to Aristotle
#
# Usage:
#   ./submit-batch.sh                    # Submit up to TARGET (default 20) total active
#   ./submit-batch.sh --count N          # Submit exactly N files
#   ./submit-batch.sh --dry-run          # Show what would be submitted
#   ./submit-batch.sh --target N         # Maintain N active jobs (default 20)
#
# Environment:
#   ARISTOTLE_API_KEY - Required for submission
#   ARISTOTLE_TARGET  - Target number of active jobs (default 20)
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"
FIND_CANDIDATES="$SCRIPT_DIR/find-candidates.sh"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Defaults
TARGET_ACTIVE="${ARISTOTLE_TARGET:-20}"
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
            echo "  --target N   Maintain N active jobs (default: 20)"
            echo "  --dry-run    Show what would be submitted"
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

# Count currently active (submitted) jobs
count_active_jobs() {
    if [[ ! -f "$JOBS_FILE" ]]; then
        echo 0
        return
    fi
    jq '[.jobs[] | select(.status == "submitted")] | length' "$JOBS_FILE"
}

# Submit a single file to Aristotle
submit_file() {
    local file="$1"
    local problem_id=$(basename "$file" .lean | sed 's/Problem$//' | tr '[:upper:]' '[:lower:]' | sed 's/erdos/erdos-/')

    echo -e "${BLUE}Submitting:${NC} $file"

    if [[ "$DRY_RUN" == true ]]; then
        echo -e "  ${YELLOW}[DRY RUN]${NC} Would submit $problem_id"
        return 0
    fi

    # Use aristotlelib to submit (prove-from-file is the new command)
    local output
    output=$(uvx --from aristotlelib aristotle prove-from-file "$file" --no-wait 2>&1) || {
        echo -e "  ${RED}Failed:${NC} $output"
        return 1
    }

    # Extract project ID from output
    local project_id=$(echo "$output" | grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' | head -1)

    if [[ -z "$project_id" ]]; then
        echo -e "  ${RED}Failed to get project ID${NC}"
        echo "  Output: $output"
        return 1
    fi

    echo -e "  ${GREEN}Submitted:${NC} $project_id"

    # Log to jobs file
    local now=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    local tmp_file=$(mktemp)

    jq --arg pid "$project_id" \
       --arg file "$file" \
       --arg prob "$problem_id" \
       --arg now "$now" \
       '.jobs += [{
         project_id: $pid,
         file: $file,
         problem_id: $prob,
         submitted: $now,
         status: "submitted",
         notes: "Batch submission"
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
    echo "Currently active jobs: $active"
    echo "Target active jobs: $TARGET_ACTIVE"

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

    if [[ "$to_submit" -eq 0 ]]; then
        echo -e "${GREEN}Already at target. No submissions needed.${NC}"
        return 0
    fi

    echo "Will submit: $to_submit files"
    echo ""

    # Get best candidates
    local candidates
    candidates=$("$FIND_CANDIDATES" --json --best "$to_submit" 2>/dev/null)

    if [[ -z "$candidates" || "$candidates" == "[]" ]]; then
        echo -e "${YELLOW}No candidates found${NC}"
        return 0
    fi

    # Submit each candidate
    local submitted=0
    local failed=0

    while IFS= read -r file; do
        [[ -z "$file" ]] && continue

        if submit_file "$file"; then
            ((submitted++))
        else
            ((failed++))
        fi

        # Small delay between submissions
        sleep 1
    done < <(echo "$candidates" | jq -r '.[].file')

    echo ""
    echo -e "${GREEN}Submitted: $submitted${NC}"
    if [[ "$failed" -gt 0 ]]; then
        echo -e "${RED}Failed: $failed${NC}"
    fi

    local new_active=$(count_active_jobs)
    echo "Active jobs now: $new_active"
}

main
