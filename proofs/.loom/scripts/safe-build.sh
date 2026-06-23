#!/bin/bash
# Safe build wrapper that prevents concurrent lake builds and OOM issues
# Usage: ./.loom/scripts/safe-build.sh [lake build args...]

set -e

LOCKFILE="/tmp/lean-genius-build.lock"
MAX_WAIT=5  # seconds to wait for existing build

# Check for existing build
if [ -f "$LOCKFILE" ]; then
    PID=$(cat "$LOCKFILE" 2>/dev/null)
    if [ -n "$PID" ] && kill -0 "$PID" 2>/dev/null; then
        echo "Build already in progress (PID: $PID)"
        echo "Lock file: $LOCKFILE"
        echo "To force: rm $LOCKFILE"
        exit 1
    else
        echo "Stale lock file found, removing..."
        rm -f "$LOCKFILE"
    fi
fi

# Create lock file with our PID
cleanup() {
    rm -f "$LOCKFILE"
}
trap cleanup EXIT INT TERM

echo $$ > "$LOCKFILE"
echo "Build lock acquired (PID: $$)"

# Run lake build with memory-conscious settings
# Limit to single job to reduce memory pressure
echo "Running: lake build $*"
lake build -j1 "$@"

echo "Build completed successfully"
