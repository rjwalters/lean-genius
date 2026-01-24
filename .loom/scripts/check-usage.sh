#!/bin/bash

# check-usage.sh - Query claude-monitor database for usage status
#
# Usage:
#   check-usage.sh              - Get current usage status as JSON
#   check-usage.sh --throttle   - Get throttle level (0-4) for scripting
#   check-usage.sh --human      - Human-readable output
#   check-usage.sh --help       - Show help
#
# Returns JSON with usage percentages and reset times from claude-monitor.
# Integrates with Loom for intelligent throttling of autonomous operations.
#
# Throttle Levels:
#   0 (< 70%)  - Normal operation
#   1 (70-80%) - Warning logged, continue
#   2 (80-90%) - Reduce autonomous operation frequency
#   3 (90-97%) - Pause non-critical operations
#   4 (> 97%)  - Pause all operations until reset

set -euo pipefail

# Database path
DB_PATH="${CLAUDE_MONITOR_DB:-$HOME/.claude-monitor/usage.db}"

# Stale data threshold in seconds (5 minutes)
STALE_THRESHOLD=300

# Colors for human output
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

# Show help
show_help() {
    cat <<EOF
check-usage.sh - Query claude-monitor database for usage status

USAGE:
    check-usage.sh              Get current usage as JSON
    check-usage.sh --throttle   Get throttle level (0-4) for scripting
    check-usage.sh --human      Human-readable output with colors
    check-usage.sh --help       Show this help

OUTPUT (JSON mode):
    {
      "session_percent": 45.2,
      "session_reset": "2h 15m",
      "weekly_all_percent": 23.1,
      "weekly_reset": "5d 3h",
      "timestamp": "2026-01-24T10:30:00",
      "data_age_seconds": 45,
      "throttle_level": 0,
      "throttle_action": "normal"
    }

THROTTLE LEVELS:
    0 (< 70%)   Normal operation
    1 (70-80%)  Warning logged, continue
    2 (80-90%)  Reduce autonomous frequency
    3 (90-97%)  Pause non-critical operations
    4 (> 97%)   Pause all operations until reset

ENVIRONMENT:
    CLAUDE_MONITOR_DB   Override database path (default: ~/.claude-monitor/usage.db)

EXAMPLES:
    # Check if we should throttle
    if [ \$(check-usage.sh --throttle) -ge 3 ]; then
        echo "High usage - pausing autonomous operations"
        exit 0
    fi

    # Get full status for logging
    check-usage.sh | jq .

    # Human-readable status
    check-usage.sh --human
EOF
}

# Calculate throttle level from session percentage
get_throttle_level() {
    local percent="$1"

    if (( $(echo "$percent < 70" | bc -l) )); then
        echo 0
    elif (( $(echo "$percent < 80" | bc -l) )); then
        echo 1
    elif (( $(echo "$percent < 90" | bc -l) )); then
        echo 2
    elif (( $(echo "$percent < 97" | bc -l) )); then
        echo 3
    else
        echo 4
    fi
}

# Get throttle action description
get_throttle_action() {
    local level="$1"

    case "$level" in
        0) echo "normal" ;;
        1) echo "warning" ;;
        2) echo "reduce_frequency" ;;
        3) echo "pause_non_critical" ;;
        4) echo "pause_all" ;;
        *) echo "unknown" ;;
    esac
}

# Output error JSON and exit
error_json() {
    local message="$1"
    local details="${2:-}"

    if [ -n "$details" ]; then
        echo "{\"error\": \"$message\", \"details\": \"$details\", \"db_path\": \"$DB_PATH\"}"
    else
        echo "{\"error\": \"$message\", \"db_path\": \"$DB_PATH\"}"
    fi
    exit 1
}

# Query database and output JSON
query_usage() {
    # Check if database exists
    if [ ! -f "$DB_PATH" ]; then
        error_json "claude-monitor database not found" "Install claude-monitor or check CLAUDE_MONITOR_DB path"
    fi

    # Check if sqlite3 is available
    if ! command -v sqlite3 &> /dev/null; then
        error_json "sqlite3 not found" "Install sqlite3 to query usage database"
    fi

    # Query the database for the most recent non-synthetic entry
    local result
    result=$(sqlite3 "$DB_PATH" "
        SELECT json_object(
            'session_percent', COALESCE(session_percent, 0),
            'session_reset', COALESCE(session_reset, 'unknown'),
            'weekly_all_percent', COALESCE(weekly_all_percent, 0),
            'weekly_reset', COALESCE(weekly_reset, 'unknown'),
            'timestamp', timestamp,
            'data_age_seconds', CAST((julianday('now') - julianday(timestamp)) * 86400 AS INTEGER)
        )
        FROM usage_history
        WHERE is_synthetic = 0
        ORDER BY timestamp DESC
        LIMIT 1
    " 2>/dev/null) || error_json "Failed to query database" "Database may be corrupted or schema mismatch"

    # Check if we got a result
    if [ -z "$result" ]; then
        error_json "No usage data found" "claude-monitor may not have collected data yet"
    fi

    # Parse the result to add throttle information
    local session_percent
    local data_age
    session_percent=$(echo "$result" | jq -r '.session_percent')
    data_age=$(echo "$result" | jq -r '.data_age_seconds')

    # Calculate throttle level
    local throttle_level
    throttle_level=$(get_throttle_level "$session_percent")
    local throttle_action
    throttle_action=$(get_throttle_action "$throttle_level")

    # Check for stale data
    local is_stale="false"
    if [ "$data_age" -gt "$STALE_THRESHOLD" ]; then
        is_stale="true"
    fi

    # Output enhanced JSON
    echo "$result" | jq --argjson level "$throttle_level" \
                        --arg action "$throttle_action" \
                        --argjson stale "$is_stale" \
                        --argjson threshold "$STALE_THRESHOLD" \
                        '. + {
                            throttle_level: $level,
                            throttle_action: $action,
                            is_stale: $stale,
                            stale_threshold_seconds: $threshold
                        }'
}

# Output just the throttle level
output_throttle() {
    # Check if database exists
    if [ ! -f "$DB_PATH" ]; then
        # Default to highest throttle level if we can't read usage
        echo 4
        exit 0
    fi

    if ! command -v sqlite3 &> /dev/null; then
        echo 4
        exit 0
    fi

    local session_percent
    session_percent=$(sqlite3 "$DB_PATH" "
        SELECT COALESCE(session_percent, 100)
        FROM usage_history
        WHERE is_synthetic = 0
        ORDER BY timestamp DESC
        LIMIT 1
    " 2>/dev/null) || { echo 4; exit 0; }

    if [ -z "$session_percent" ]; then
        echo 4
        exit 0
    fi

    get_throttle_level "$session_percent"
}

# Human-readable output
output_human() {
    local json
    json=$(query_usage 2>/dev/null) || {
        echo -e "${RED}Error:${NC} $(echo "$json" | jq -r '.error // "Unknown error"')"
        exit 1
    }

    local session_percent weekly_percent throttle_level throttle_action is_stale data_age
    session_percent=$(echo "$json" | jq -r '.session_percent')
    weekly_percent=$(echo "$json" | jq -r '.weekly_all_percent')
    throttle_level=$(echo "$json" | jq -r '.throttle_level')
    throttle_action=$(echo "$json" | jq -r '.throttle_action')
    is_stale=$(echo "$json" | jq -r '.is_stale')
    data_age=$(echo "$json" | jq -r '.data_age_seconds')
    session_reset=$(echo "$json" | jq -r '.session_reset')
    weekly_reset=$(echo "$json" | jq -r '.weekly_reset')

    echo -e "${BLUE}Claude Usage Status${NC}"
    echo "==================="

    # Session usage with color coding
    local session_color="$GREEN"
    if [ "$throttle_level" -ge 3 ]; then
        session_color="$RED"
    elif [ "$throttle_level" -ge 1 ]; then
        session_color="$YELLOW"
    fi
    echo -e "Session:  ${session_color}${session_percent}%${NC} (resets in ${session_reset})"
    echo -e "Weekly:   ${weekly_percent}% (resets in ${weekly_reset})"

    echo ""

    # Throttle status
    local throttle_color="$GREEN"
    local throttle_desc="Normal operation"
    case "$throttle_level" in
        1)
            throttle_color="$YELLOW"
            throttle_desc="Warning - monitor usage"
            ;;
        2)
            throttle_color="$YELLOW"
            throttle_desc="Reduce autonomous frequency"
            ;;
        3)
            throttle_color="$RED"
            throttle_desc="Pause non-critical operations"
            ;;
        4)
            throttle_color="$RED"
            throttle_desc="PAUSE ALL - wait for reset"
            ;;
    esac
    echo -e "Throttle: ${throttle_color}Level $throttle_level${NC} - $throttle_desc"

    # Stale warning
    if [ "$is_stale" = "true" ]; then
        echo ""
        echo -e "${YELLOW}Warning:${NC} Data is stale (${data_age}s old, threshold: ${STALE_THRESHOLD}s)"
        echo "         Run claude-monitor to refresh usage data"
    fi
}

# Main
case "${1:-}" in
    --help|-h)
        show_help
        ;;
    --throttle)
        output_throttle
        ;;
    --human)
        output_human
        ;;
    "")
        query_usage
        ;;
    *)
        echo "Unknown option: $1" >&2
        echo "Run 'check-usage.sh --help' for usage" >&2
        exit 1
        ;;
esac
