#!/bin/bash
# Sync research meta.json files to src/data/research/problems/
# This script copies meta.json from research/problems/<slug>/ to src/data/research/problems/<slug>.json
# Problems with status "skipped" are NOT synced (and removed from target if present)

set -e

# Get script directory and project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

SOURCE_DIR="$PROJECT_ROOT/research/problems"
TARGET_DIR="$PROJECT_ROOT/src/data/research/problems"

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo "Syncing research meta.json files..."
echo "Source: $SOURCE_DIR"
echo "Target: $TARGET_DIR"
echo ""

# Ensure target directory exists
mkdir -p "$TARGET_DIR"

# Counters
synced=0
up_to_date=0
filtered=0
removed=0
errors=0

# Find all meta.json files in research/problems/*/
for meta_file in "$SOURCE_DIR"/*/meta.json; do
    if [ -f "$meta_file" ]; then
        # Extract the problem slug from the path
        slug=$(basename "$(dirname "$meta_file")")
        target_file="$TARGET_DIR/${slug}.json"

        # Check if status is "skipped" - these should not be on the website
        status=$(jq -r '.status // "unknown"' "$meta_file" 2>/dev/null || echo "unknown")

        if [ "$status" = "skipped" ]; then
            # Remove from target if it exists
            if [ -f "$target_file" ]; then
                rm "$target_file"
                echo -e "${BLUE}✕${NC} Removed (status=skipped): $slug"
                ((removed++))
            else
                echo -e "${BLUE}○${NC} Filtered (status=skipped): $slug"
            fi
            ((filtered++))
            continue
        fi

        # Check if source is newer than target (or target doesn't exist)
        if [ ! -f "$target_file" ] || [ "$meta_file" -nt "$target_file" ]; then
            if cp "$meta_file" "$target_file"; then
                echo -e "${GREEN}✓${NC} Synced: $slug"
                ((synced++))
            else
                echo -e "${RED}✗${NC} Error syncing: $slug"
                ((errors++))
            fi
        else
            echo -e "${YELLOW}○${NC} Up to date: $slug"
            ((up_to_date++))
        fi
    fi
done

echo ""
echo "Summary:"
echo -e "  ${GREEN}Synced:${NC}     $synced"
echo -e "  ${YELLOW}Up to date:${NC} $up_to_date"
echo -e "  ${BLUE}Filtered:${NC}   $filtered (status=skipped, not shown on website)"
if [ $removed -gt 0 ]; then
    echo -e "  ${BLUE}Removed:${NC}    $removed (were in target, now filtered)"
fi
if [ $errors -gt 0 ]; then
    echo -e "  ${RED}Errors:${NC}     $errors"
fi

# List any JSON files in target that don't have a meta.json source
echo ""
echo "Checking for orphaned files in target..."
orphaned=0
for target_file in "$TARGET_DIR"/*.json; do
    if [ -f "$target_file" ]; then
        slug=$(basename "$target_file" .json)
        source_meta="$SOURCE_DIR/$slug/meta.json"
        if [ ! -f "$source_meta" ]; then
            echo -e "${YELLOW}⚠${NC}  Orphaned (no meta.json source): $slug.json"
            ((orphaned++))
        fi
    fi
done

if [ $orphaned -eq 0 ]; then
    echo "  No orphaned files found."
fi

echo ""
echo "Done!"
