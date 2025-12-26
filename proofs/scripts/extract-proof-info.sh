#!/bin/bash
#
# extract-proof-info.sh - Extract goal states and type info from Lean proofs
#
# Usage: ./scripts/extract-proof-info.sh [proof-file.lean]
#        ./scripts/extract-proof-info.sh --all
#
# Requirements:
#   - LeanInk built at ~/Projects/LeanInk
#   - This project uses Lean 4.10.0 with pinned Mathlib
#
# Output:
#   Creates .leanInk JSON files alongside each .lean file
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
LEANINK_BIN="$HOME/Projects/LeanInk/.lake/build/bin/leanInk"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Check LeanInk exists
if [ ! -f "$LEANINK_BIN" ]; then
    echo -e "${RED}Error: LeanInk not found at $LEANINK_BIN${NC}"
    echo "Please build LeanInk first:"
    echo "  cd ~/Projects/LeanInk && MACOSX_DEPLOYMENT_TARGET=15.0 lake build"
    exit 1
fi

cd "$PROJECT_DIR"

# Function to process a single file
process_file() {
    local file="$1"
    echo -e "${YELLOW}Processing: $file${NC}"

    if "$LEANINK_BIN" analyze "$file" --lake lakefile.toml --x-enable-type-info 2>&1; then
        local output="${file}.leanInk"
        if [ -f "$output" ]; then
            local size=$(wc -c < "$output" | tr -d ' ')
            echo -e "${GREEN}  ✓ Generated $output ($size bytes)${NC}"
        fi
    else
        echo -e "${RED}  ✗ Failed to process $file${NC}"
        return 1
    fi
}

# Main logic
if [ "$1" == "--all" ]; then
    echo "Processing all proof files..."
    echo ""

    # Find all .lean files in Proofs directory
    find Proofs -name "*.lean" | while read -r file; do
        process_file "$file"
        echo ""
    done

    echo -e "${GREEN}Done!${NC}"

elif [ -n "$1" ]; then
    # Process single file
    if [ ! -f "$1" ]; then
        echo -e "${RED}Error: File not found: $1${NC}"
        exit 1
    fi
    process_file "$1"

else
    echo "Usage: $0 [proof-file.lean]"
    echo "       $0 --all"
    echo ""
    echo "Examples:"
    echo "  $0 Proofs/Sqrt2Irrational.lean"
    echo "  $0 --all"
fi
