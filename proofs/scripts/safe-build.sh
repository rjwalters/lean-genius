#!/bin/bash
#
# Safe Lean build with memory limits
#
# Prevents Lean from consuming all system memory and crashing the machine.
# Actually monitors memory usage and kills the build if it exceeds the limit.
#
# Usage:
#   ./proofs/scripts/safe-build.sh          # Build all
#   ./proofs/scripts/safe-build.sh Proofs   # Build specific target
#   LEAN_MEMORY_LIMIT=16384 ./proofs/scripts/safe-build.sh  # Custom limit (MB)
#
# Environment variables:
#   LEAN_MEMORY_LIMIT  - Max memory in MB (default: 16384 = 16GB)
#   LEAN_BUILD_TIMEOUT - Build timeout (default: 60m)
#   LEAN_CHECK_INTERVAL - Memory check interval in seconds (default: 2)
#

set -e

# Memory limit in MB (default 16GB - conservative to leave room for system)
MEMORY_LIMIT_MB=${LEAN_MEMORY_LIMIT:-16384}

# Timeout for entire build (default 60 minutes)
TIMEOUT=${LEAN_BUILD_TIMEOUT:-60m}

# How often to check memory (seconds)
CHECK_INTERVAL=${LEAN_CHECK_INTERVAL:-2}

cd "$(dirname "$0")/.."

echo "=== Safe Lean Build ==="
echo "Memory limit: ${MEMORY_LIMIT_MB}MB"
echo "Timeout: ${TIMEOUT}"
echo "Check interval: ${CHECK_INTERVAL}s"
echo ""

# Function to get total memory usage of a process tree (in MB)
get_process_tree_memory() {
    local pid=$1
    local total=0

    # Get all descendant PIDs
    local pids=$(pgrep -P "$pid" 2>/dev/null)
    pids="$pid $pids"

    for p in $pids; do
        # Get RSS in KB, convert to MB
        local mem=$(ps -o rss= -p "$p" 2>/dev/null | tr -d ' ')
        if [[ -n "$mem" && "$mem" -gt 0 ]]; then
            total=$((total + mem / 1024))
        fi
    done

    echo "$total"
}

# Function to kill process tree
kill_tree() {
    local pid=$1
    local pids=$(pgrep -P "$pid" 2>/dev/null)
    for p in $pids; do
        kill_tree "$p"
    done
    kill -9 "$pid" 2>/dev/null || true
}

# Cleanup function
cleanup() {
    if [[ -n "$BUILD_PID" ]] && kill -0 "$BUILD_PID" 2>/dev/null; then
        echo ""
        echo "Cleaning up build process..."
        kill_tree "$BUILD_PID"
    fi
    if [[ -n "$MONITOR_PID" ]] && kill -0 "$MONITOR_PID" 2>/dev/null; then
        kill "$MONITOR_PID" 2>/dev/null || true
    fi
}

trap cleanup EXIT INT TERM

# Start the build in background
echo "Starting build..."
nice -n 10 lake build "$@" &
BUILD_PID=$!

# Monitor memory usage
EXCEEDED=false
START_TIME=$(date +%s)

# Convert timeout to seconds
TIMEOUT_SECS=$(echo "$TIMEOUT" | sed 's/m/*60/;s/h/*3600/;s/s//' | bc)

while kill -0 "$BUILD_PID" 2>/dev/null; do
    CURRENT_MEM=$(get_process_tree_memory "$BUILD_PID")
    ELAPSED=$(($(date +%s) - START_TIME))

    # Show progress every 10 checks
    if [[ $((ELAPSED % (CHECK_INTERVAL * 10))) -lt $CHECK_INTERVAL ]]; then
        echo "[${ELAPSED}s] Memory: ${CURRENT_MEM}MB / ${MEMORY_LIMIT_MB}MB"
    fi

    # Check memory limit
    if [[ "$CURRENT_MEM" -gt "$MEMORY_LIMIT_MB" ]]; then
        echo ""
        echo "!!! MEMORY LIMIT EXCEEDED !!!"
        echo "Current: ${CURRENT_MEM}MB > Limit: ${MEMORY_LIMIT_MB}MB"
        echo "Killing build to prevent system crash..."
        EXCEEDED=true
        kill_tree "$BUILD_PID"
        break
    fi

    # Check timeout
    if [[ "$ELAPSED" -gt "$TIMEOUT_SECS" ]]; then
        echo ""
        echo "!!! TIMEOUT EXCEEDED !!!"
        echo "Build exceeded ${TIMEOUT} timeout"
        echo "Killing build..."
        kill_tree "$BUILD_PID"
        exit 124
    fi

    sleep "$CHECK_INTERVAL"
done

# Wait for build to finish and get exit code
wait "$BUILD_PID" 2>/dev/null
EXIT_CODE=$?

if $EXCEEDED; then
    echo ""
    echo "=== Build KILLED (memory limit) ==="
    echo "The build was consuming too much memory."
    echo "Consider:"
    echo "  - Building specific targets instead of all"
    echo "  - Increasing LEAN_MEMORY_LIMIT if you have more RAM"
    echo "  - Excluding memory-intensive files from the build"
    exit 137
fi

if [[ $EXIT_CODE -eq 0 ]]; then
    echo ""
    echo "=== Build complete ==="
else
    echo ""
    echo "=== Build failed (exit code: $EXIT_CODE) ==="
    exit $EXIT_CODE
fi
