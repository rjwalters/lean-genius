#!/bin/bash
#
# setup.sh - Set up the lean-genius-proofs environment
#
# This script:
#   1. Builds the Mathlib cache tool (needed for macOS 26+)
#   2. Downloads Mathlib cache
#   3. Builds all proofs
#   4. Optionally extracts LeanInk info
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

cd "$PROJECT_DIR"

echo -e "${BLUE}=== LeanGenius Proofs Setup ===${NC}"
echo ""

# Step 1: Update dependencies
echo -e "${YELLOW}Step 1: Updating lake dependencies...${NC}"
lake update

# Step 2: Build cache tool from source (macOS 26 compatibility)
echo -e "${YELLOW}Step 2: Building Mathlib cache tool...${NC}"
cd .lake/packages/mathlib
MACOSX_DEPLOYMENT_TARGET=15.0 lake build cache
cd "$PROJECT_DIR"

# Step 3: Download Mathlib cache
echo -e "${YELLOW}Step 3: Downloading Mathlib cache...${NC}"
lake exe cache get

# Step 4: Build all proofs (using lock to prevent concurrent builds)
echo -e "${YELLOW}Step 4: Building proofs...${NC}"
MACOSX_DEPLOYMENT_TARGET=15.0 "$SCRIPT_DIR/lake-build.sh"

echo ""
echo -e "${GREEN}✓ Setup complete!${NC}"
echo ""
echo "Next steps:"
echo "  - Add new proofs to Proofs/ directory"
echo "  - Run ./scripts/extract-proof-info.sh --all to generate LeanInk output"
