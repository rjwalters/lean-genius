#!/bin/bash
# check-usage.sh - Query claude-monitor database for session usage
#
# Usage:
#   ./.loom/scripts/check-usage.sh             # Returns JSON with usage data
#   ./.loom/scripts/check-usage.sh --status    # Human-readable status
#   ./.loom/scripts/check-usage.sh --throttle  # Numeric throttle level (0-4)
#
# Throttle levels (--throttle):
#   0 - Normal (session < 70%)
#   1 - Low (session >= 70%) - informational
#   2 - Moderate (session >= 80%) - warning
#   3 - High (session >= 90%) - spawn delays recommended
#   4 - Critical (session >= 97%) - pause all operations
#
# Exit codes:
#   0 - Data returned successfully (--throttle always exits 0)
#   1 - Database not found or query failed
#
# This script queries the claude-monitor SQLite database to get current
# session usage. Used by the Loom daemon to detect approaching rate limits.
#
# Requires: claude-monitor browser extension
# See: https://github.com/rjwalters/claude-monitor

set -e

DB_PATH="$HOME/.claude-monitor/usage.db"

# Check if database exists
if [ ! -f "$DB_PATH" ]; then
    if [ "$1" = "--throttle" ]; then
        echo "0"
        exit 0
    elif [ "$1" = "--status" ]; then
        echo "NO_DATABASE: claude-monitor not installed"
        echo ""
        echo "For multi-day autonomous operation, install claude-monitor:"
        echo "  https://github.com/rjwalters/claude-monitor"
    else
        echo '{"error": "NO_DATABASE", "message": "claude-monitor not installed"}'
    fi
    exit 1
fi

# Check if sqlite3 is available
if ! command -v sqlite3 &> /dev/null; then
    if [ "$1" = "--throttle" ]; then
        echo "0"
        exit 0
    elif [ "$1" = "--status" ]; then
        echo "ERROR: sqlite3 not found"
    else
        echo '{"error": "NO_SQLITE3", "message": "sqlite3 command not found"}'
    fi
    exit 1
fi

# Helper: compute throttle level from session percentage
compute_throttle_level() {
    local session_pct="$1"
    local pct="${session_pct%.*}"  # Remove decimal part

    if [ -z "$pct" ] || [ "$pct" -le 0 ] 2>/dev/null; then
        echo "0"
    elif [ "$pct" -ge 97 ]; then
        echo "4"
    elif [ "$pct" -ge 90 ]; then
        echo "3"
    elif [ "$pct" -ge 80 ]; then
        echo "2"
    elif [ "$pct" -ge 70 ]; then
        echo "1"
    else
        echo "0"
    fi
}

if [ "$1" = "--throttle" ]; then
    # Return numeric throttle level (0-4) for programmatic use
    result=$(sqlite3 "$DB_PATH" "
        SELECT session_percent
        FROM usage_history
        WHERE is_synthetic = 0
        ORDER BY timestamp DESC
        LIMIT 1
    " 2>/dev/null)

    if [ -z "$result" ]; then
        echo "0"
        exit 0
    fi

    compute_throttle_level "$result"
    exit 0

elif [ "$1" = "--status" ]; then
    # Human-readable format
    result=$(sqlite3 "$DB_PATH" "
        SELECT
            session_percent,
            session_reset,
            weekly_all_percent,
            weekly_reset,
            datetime(timestamp, 'localtime') as local_time
        FROM usage_history
        WHERE is_synthetic = 0
        ORDER BY timestamp DESC
        LIMIT 1
    " -separator '|' 2>/dev/null)

    if [ -z "$result" ]; then
        echo "NO_DATA: No usage data in database"
        echo "Make sure claude.ai/settings/usage is open in your browser"
        exit 1
    fi

    IFS='|' read -r session_pct session_reset weekly_pct weekly_reset timestamp <<< "$result"

    echo "Claude Usage Status (as of $timestamp)"
    echo "========================================"
    echo ""
    echo "Session:     ${session_pct}% used"
    echo "  Resets:    $session_reset"
    echo ""
    echo "Weekly:      ${weekly_pct}% used"
    echo "  Resets:    $weekly_reset"
    echo ""

    # Compute and display throttle level
    throttle_level=$(compute_throttle_level "$session_pct")

    echo "Throttle:    Level $throttle_level/4"
    echo ""

    # Provide recommendation based on throttle level
    case "$throttle_level" in
        4) echo "RECOMMENDATION: Pause all operations until session resets" ;;
        3) echo "WARNING: High usage - spawn delays recommended" ;;
        2) echo "WARNING: Approaching session limit" ;;
        1) echo "NOTE: Usage rising, monitoring recommended" ;;
        *) echo "Session usage is healthy" ;;
    esac
else
    # JSON format for programmatic use
    sqlite3 "$DB_PATH" "
        SELECT json_object(
            'session_percent', session_percent,
            'session_reset', session_reset,
            'weekly_all_percent', weekly_all_percent,
            'weekly_reset', weekly_reset,
            'timestamp', timestamp,
            'data_age_seconds', CAST((julianday('now') - julianday(timestamp)) * 86400 AS INTEGER)
        )
        FROM usage_history
        WHERE is_synthetic = 0
        ORDER BY timestamp DESC
        LIMIT 1
    " 2>/dev/null || {
        echo '{"error": "QUERY_FAILED", "message": "Failed to query database"}'
        exit 1
    }
fi
