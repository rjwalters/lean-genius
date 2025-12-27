#!/bin/bash
# generate-proofs-imports.sh - Auto-generate proofs/Proofs.lean from directory contents
# Ensures consistent sorting across all platforms using LC_ALL=C
#
# Usage: ./.loom/scripts/generate-proofs-imports.sh [--check]
#
# Options:
#   --check    Verify Proofs.lean is up to date (exit 1 if out of sync)
#
# This script eliminates merge conflicts by auto-generating the import file.

set -euo pipefail

# Navigate to repository root (handle being called from anywhere)
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

PROOFS_DIR="$REPO_ROOT/proofs/Proofs"
OUTPUT_FILE="$REPO_ROOT/proofs/Proofs.lean"

# Check mode flag
CHECK_MODE=false
if [[ "${1:-}" == "--check" ]]; then
    CHECK_MODE=true
fi

# Verify the proofs directory exists
if [[ ! -d "$PROOFS_DIR" ]]; then
    echo "Error: Proofs directory not found at $PROOFS_DIR" >&2
    exit 1
fi

# Generate the imports file content
generate_imports() {
    echo "-- Auto-generated file - do not edit manually"
    echo "-- Run: ./.loom/scripts/generate-proofs-imports.sh"
    echo ""

    # Find all .lean files, extract module names, and sort them
    # Use LC_ALL=C for consistent sorting across macOS and Linux
    find "$PROOFS_DIR" -maxdepth 1 -name "*.lean" -type f | \
        xargs -I{} basename {} .lean | \
        LC_ALL=C sort | \
        while read -r module; do
            echo "import Proofs.$module"
        done
}

# Generate the new content
NEW_CONTENT=$(generate_imports)

if [[ "$CHECK_MODE" == true ]]; then
    # Check mode: compare with existing file
    if [[ ! -f "$OUTPUT_FILE" ]]; then
        echo "Error: $OUTPUT_FILE does not exist" >&2
        exit 1
    fi

    EXISTING_CONTENT=$(cat "$OUTPUT_FILE")

    if [[ "$NEW_CONTENT" != "$EXISTING_CONTENT" ]]; then
        echo "Error: proofs/Proofs.lean is out of sync with proofs/Proofs/ directory" >&2
        echo "" >&2
        echo "Run: ./.loom/scripts/generate-proofs-imports.sh" >&2
        echo "" >&2
        echo "Diff:" >&2
        diff <(echo "$EXISTING_CONTENT") <(echo "$NEW_CONTENT") || true
        exit 1
    fi

    echo "proofs/Proofs.lean is up to date"
    exit 0
fi

# Write mode: generate the file
echo "$NEW_CONTENT" > "$OUTPUT_FILE"

# Count modules
MODULE_COUNT=$(find "$PROOFS_DIR" -maxdepth 1 -name "*.lean" -type f | wc -l | tr -d ' ')

echo "Generated proofs/Proofs.lean with $MODULE_COUNT imports"
