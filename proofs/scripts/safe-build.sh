#!/bin/bash
#
# Safe Lean build with memory limits
#
# Prevents Lean from consuming all system memory and crashing the machine.
# Uses LEAN_MEMORY_LIMIT to cap memory at 64GB (configurable).
#
# Usage:
#   ./proofs/scripts/safe-build.sh          # Build all
#   ./proofs/scripts/safe-build.sh Proofs   # Build specific target
#   LEAN_MEMORY_LIMIT=32768 ./proofs/scripts/safe-build.sh  # Custom limit
#

set -e

# Memory limit in MB (default 64GB = 65536MB)
export LEAN_MEMORY_LIMIT=${LEAN_MEMORY_LIMIT:-65536}

# Timeout for entire build (default 60 minutes)
TIMEOUT=${LEAN_BUILD_TIMEOUT:-60m}

# Number of parallel jobs (default: half of CPU cores to reduce memory pressure)
JOBS=${LEAN_JOBS:-$(( $(nproc 2>/dev/null || sysctl -n hw.ncpu) / 2 ))}

cd "$(dirname "$0")/.."

echo "=== Safe Lean Build ==="
echo "Memory limit: ${LEAN_MEMORY_LIMIT}MB"
echo "Timeout: ${TIMEOUT}"
echo "Parallel jobs: ${JOBS}"
echo ""

# Run with timeout and nice (lower priority)
if command -v timeout &> /dev/null; then
    nice -n 10 timeout "$TIMEOUT" lake build -j"$JOBS" "$@"
elif command -v gtimeout &> /dev/null; then
    # macOS with coreutils installed
    nice -n 10 gtimeout "$TIMEOUT" lake build -j"$JOBS" "$@"
else
    # No timeout available, just run with nice
    echo "Warning: timeout command not found, running without timeout"
    nice -n 10 lake build -j"$JOBS" "$@"
fi

echo ""
echo "=== Build complete ==="
