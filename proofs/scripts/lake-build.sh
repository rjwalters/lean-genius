#!/bin/bash
#
# lake-build.sh - Run lake build with single-instance protection
#
# This script ensures only one Lean build runs at a time to prevent
# out-of-memory crashes. Uses a PID-based lock file mechanism.
#
# Usage:
#   ./lake-build.sh [lake-args...]
#
# Examples:
#   ./lake-build.sh              # Run 'lake build'
#   ./lake-build.sh Proofs       # Run 'lake build Proofs'
#   ./lake-build.sh --help       # Show this help
#
# Environment variables:
#   LAKE_BUILD_LOCK_DIR    - Directory for lock file (default: /tmp)
#   LAKE_BUILD_TIMEOUT     - Max seconds to wait for lock (default: 0 = no wait)
#   LAKE_BUILD_NO_LOCK     - Set to 1 to skip locking (not recommended)
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Configuration
LOCK_DIR="${LAKE_BUILD_LOCK_DIR:-/tmp}"
LOCK_FILE="${LOCK_DIR}/lean-genius-lake-build.lock"
TIMEOUT="${LAKE_BUILD_TIMEOUT:-0}"
NO_LOCK="${LAKE_BUILD_NO_LOCK:-0}"

# Show help
if [[ "$1" == "--help" || "$1" == "-h" ]]; then
    head -24 "$0" | tail -20
    exit 0
fi

# Function to check if a PID is still running
is_pid_running() {
    local pid=$1
    if [[ -z "$pid" ]]; then
        return 1
    fi
    kill -0 "$pid" 2>/dev/null
}

# Function to get lock holder info
get_lock_info() {
    if [[ -f "$LOCK_FILE" ]]; then
        cat "$LOCK_FILE"
    fi
}

# Function to acquire lock
acquire_lock() {
    local start_time=$(date +%s)

    while true; do
        # Try to create lock file atomically
        if (set -o noclobber; echo "$$:$(date +%s):$(whoami)" > "$LOCK_FILE") 2>/dev/null; then
            # Successfully acquired lock
            return 0
        fi

        # Lock file exists - check if holder is still alive
        local lock_info=$(get_lock_info)
        local holder_pid=$(echo "$lock_info" | cut -d: -f1)
        local lock_time=$(echo "$lock_info" | cut -d: -f2)
        local lock_user=$(echo "$lock_info" | cut -d: -f3)

        if ! is_pid_running "$holder_pid"; then
            # Stale lock - holder is dead
            echo -e "${YELLOW}Removing stale lock from dead process $holder_pid${NC}"
            rm -f "$LOCK_FILE"
            continue
        fi

        # Lock is held by running process
        local current_time=$(date +%s)
        local elapsed=$((current_time - start_time))
        local lock_duration=$((current_time - lock_time))

        if [[ "$TIMEOUT" -gt 0 && "$elapsed" -ge "$TIMEOUT" ]]; then
            echo -e "${RED}ERROR: Timed out waiting for lock after ${TIMEOUT}s${NC}" >&2
            echo -e "${RED}Lock held by PID $holder_pid (user: $lock_user) for ${lock_duration}s${NC}" >&2
            return 1
        fi

        if [[ "$TIMEOUT" -eq 0 ]]; then
            echo -e "${RED}ERROR: Another Lean build is already running${NC}" >&2
            echo -e "${RED}Lock held by PID $holder_pid (user: $lock_user) for ${lock_duration}s${NC}" >&2
            echo -e "${YELLOW}Hint: Set LAKE_BUILD_TIMEOUT=300 to wait up to 5 minutes${NC}" >&2
            return 1
        fi

        # Wait and retry
        if [[ "$elapsed" -eq 0 || $((elapsed % 10)) -eq 0 ]]; then
            echo -e "${YELLOW}Waiting for lock... (PID $holder_pid, ${lock_duration}s elapsed)${NC}"
        fi
        sleep 2
    done
}

# Function to release lock
release_lock() {
    local lock_info=$(get_lock_info)
    local holder_pid=$(echo "$lock_info" | cut -d: -f1)

    # Only remove if we're the holder
    if [[ "$holder_pid" == "$$" ]]; then
        rm -f "$LOCK_FILE"
    fi
}

# Cleanup on exit
cleanup() {
    local exit_code=$?
    release_lock
    exit $exit_code
}

# Main execution
main() {
    cd "$PROJECT_DIR"

    # Skip locking if requested
    if [[ "$NO_LOCK" == "1" ]]; then
        echo -e "${YELLOW}Warning: Running without lock protection${NC}"
        exec lake build "$@"
    fi

    # Acquire lock
    if ! acquire_lock; then
        exit 1
    fi

    # Set up cleanup trap
    trap cleanup EXIT INT TERM

    echo -e "${BLUE}Lock acquired (PID $$)${NC}"
    echo -e "${BLUE}Running: lake build $*${NC}"
    echo ""

    # Run lake build
    lake build "$@"
    local result=$?

    if [[ $result -eq 0 ]]; then
        echo ""
        echo -e "${GREEN}Build completed successfully${NC}"
    else
        echo ""
        echo -e "${RED}Build failed with exit code $result${NC}"
    fi

    return $result
}

main "$@"
