#!/bin/bash
#
# aristotle-status.sh - Check status of all Aristotle jobs
#
# Usage:
#   ./aristotle-status.sh           # Check all pending jobs
#   ./aristotle-status.sh --retrieve # Also retrieve completed solutions
#
# This script:
#   1. Reads jobs from research/aristotle-jobs.json
#   2. Checks status of each pending job via Aristotle API
#   3. Updates the jobs file with current status
#   4. Optionally retrieves completed solutions
#

set -e

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

RETRIEVE=false
if [ "$1" = "--retrieve" ]; then
    RETRIEVE=true
fi

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check jobs file exists
if [ ! -f "$JOBS_FILE" ]; then
    log_error "No jobs file found at $JOBS_FILE"
    echo "Submit a job first with: ./aristotle-submit.sh <file>"
    exit 1
fi

# Check ARISTOTLE_API_KEY
if [ -z "$ARISTOTLE_API_KEY" ]; then
    log_error "ARISTOTLE_API_KEY not set"
    exit 1
fi

echo ""
echo "============================================"
echo -e "${CYAN}Aristotle Job Status Report${NC}"
echo "============================================"
echo ""

# Get pending jobs
PENDING_JOBS=$(jq -r '.jobs[] | select(.status == "submitted" or .status == "in_progress") | .project_id' "$JOBS_FILE")

if [ -z "$PENDING_JOBS" ]; then
    log_info "No pending jobs found."

    # Show summary of completed/failed
    COMPLETED=$(jq -r '.completed | length' "$JOBS_FILE")
    FAILED=$(jq -r '.failed | length' "$JOBS_FILE")

    echo ""
    echo "Summary:"
    echo "  Completed: $COMPLETED"
    echo "  Failed:    $FAILED"
    exit 0
fi

TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

echo "$PENDING_JOBS" | while read -r PROJECT_ID; do
    if [ -z "$PROJECT_ID" ]; then
        continue
    fi

    # Get job info
    JOB_INFO=$(jq -r ".jobs[] | select(.project_id == \"$PROJECT_ID\")" "$JOBS_FILE")
    PROBLEM_ID=$(echo "$JOB_INFO" | jq -r '.problem_id')
    FILE=$(echo "$JOB_INFO" | jq -r '.file')
    SUBMITTED=$(echo "$JOB_INFO" | jq -r '.submitted')

    echo -e "${BLUE}Job: $PROJECT_ID${NC}"
    echo "  Problem:   $PROBLEM_ID"
    echo "  File:      $FILE"
    echo "  Submitted: $SUBMITTED"

    # Check status via Aristotle
    STATUS_OUTPUT=$(cd "$PROJECT_ROOT/proofs" && uvx --from aristotlelib aristotle status "$PROJECT_ID" 2>&1 || true)

    # Parse status
    STATUS=$(echo "$STATUS_OUTPUT" | grep -i "status:" | head -1 | sed 's/.*status: *//i' | tr '[:lower:]' '[:upper:]' | tr -d '[:space:]')
    PERCENT=$(echo "$STATUS_OUTPUT" | grep -i "percent" | grep -oE "[0-9]+" | head -1 || echo "0")

    if [ -z "$STATUS" ]; then
        STATUS="UNKNOWN"
    fi

    # Color code status
    case "$STATUS" in
        COMPLETE|COMPLETED)
            echo -e "  Status:    ${GREEN}COMPLETE${NC}"
            STATUS="COMPLETE"
            ;;
        FAILED)
            echo -e "  Status:    ${RED}FAILED${NC}"
            ;;
        IN_PROGRESS|INPROGRESS)
            echo -e "  Status:    ${YELLOW}IN_PROGRESS${NC} (${PERCENT}%)"
            STATUS="in_progress"
            ;;
        QUEUED)
            echo -e "  Status:    ${CYAN}QUEUED${NC}"
            STATUS="submitted"
            ;;
        *)
            echo -e "  Status:    ${YELLOW}$STATUS${NC}"
            ;;
    esac

    # Update jobs file with current status
    jq --arg pid "$PROJECT_ID" \
       --arg status "$STATUS" \
       --arg ts "$TIMESTAMP" \
       --arg percent "$PERCENT" \
       '(.jobs[] | select(.project_id == $pid)) |= . + {
         "status": ($status | ascii_downcase),
         "last_check": {
           "timestamp": $ts,
           "percent": ($percent | tonumber)
         }
       }' "$JOBS_FILE" > "${JOBS_FILE}.tmp" && mv "${JOBS_FILE}.tmp" "$JOBS_FILE"

    # Handle completed jobs
    if [ "$STATUS" = "COMPLETE" ]; then
        if [ "$RETRIEVE" = true ]; then
            OUTPUT_FILE="${PROJECT_ROOT}/${FILE%.lean}-solved.lean"
            log_info "Retrieving solution to $OUTPUT_FILE..."

            if cd "$PROJECT_ROOT/proofs" && uvx --from aristotlelib aristotle retrieve "$PROJECT_ID" --output-file "$OUTPUT_FILE" 2>/dev/null; then
                log_success "Solution saved!"

                # Move to completed
                jq --arg pid "$PROJECT_ID" \
                   '(.completed += [(.jobs[] | select(.project_id == $pid))]) |
                    (.jobs |= map(select(.project_id != $pid)))' "$JOBS_FILE" > "${JOBS_FILE}.tmp" && mv "${JOBS_FILE}.tmp" "$JOBS_FILE"
            else
                log_warn "Failed to retrieve solution"
            fi
        else
            echo -e "  ${GREEN}Ready to retrieve!${NC} Run with --retrieve"
        fi
    fi

    # Handle failed jobs
    if [ "$STATUS" = "FAILED" ]; then
        # Move to failed
        jq --arg pid "$PROJECT_ID" \
           '(.failed += [(.jobs[] | select(.project_id == $pid))]) |
            (.jobs |= map(select(.project_id != $pid)))' "$JOBS_FILE" > "${JOBS_FILE}.tmp" && mv "${JOBS_FILE}.tmp" "$JOBS_FILE"

        log_warn "Job failed. Consider breaking into smaller lemmas."
    fi

    echo ""
done

echo "============================================"
echo "Updated: $TIMESTAMP"
echo "============================================"
