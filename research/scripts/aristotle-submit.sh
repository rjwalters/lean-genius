#!/bin/bash
#
# aristotle-submit.sh - Submit Lean files to Aristotle for overnight processing
#
# Usage:
#   ./aristotle-submit.sh <lean-file> [problem-id] [notes]
#
# Example:
#   ./aristotle-submit.sh proofs/Proofs/Erdos340GreedySidon-provable.lean erdos-340 "Excluding open conjecture"
#
# This script:
#   1. Validates the file exists and has sorries
#   2. Checks for OPEN sorries (warns but doesn't block)
#   3. Submits to Aristotle with --no-wait
#   4. Logs the job to research/aristotle-jobs.json
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
JOBS_FILE="$PROJECT_ROOT/research/aristotle-jobs.json"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

usage() {
    echo "Usage: $0 <lean-file> [problem-id] [notes]"
    echo ""
    echo "Arguments:"
    echo "  lean-file   Path to Lean file with sorries (required)"
    echo "  problem-id  Problem identifier for tracking (optional, derived from filename)"
    echo "  notes       Notes about this submission (optional)"
    echo ""
    echo "Example:"
    echo "  $0 proofs/Proofs/Erdos340GreedySidon.lean erdos-340 'First attempt'"
    exit 1
}

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check arguments
if [ $# -lt 1 ]; then
    usage
fi

LEAN_FILE="$1"
PROBLEM_ID="${2:-$(basename "$LEAN_FILE" .lean | tr '[:upper:]' '[:lower:]')}"
NOTES="${3:-Overnight submission}"

# Validate file exists
if [ ! -f "$LEAN_FILE" ]; then
    # Try relative to project root
    if [ -f "$PROJECT_ROOT/$LEAN_FILE" ]; then
        LEAN_FILE="$PROJECT_ROOT/$LEAN_FILE"
    else
        log_error "File not found: $LEAN_FILE"
        exit 1
    fi
fi

# Get absolute path
LEAN_FILE="$(cd "$(dirname "$LEAN_FILE")" && pwd)/$(basename "$LEAN_FILE")"

log_info "Analyzing $LEAN_FILE..."

# Count sorries
SORRY_COUNT=$(grep -c "sorry" "$LEAN_FILE" 2>/dev/null || echo "0")
if [ "$SORRY_COUNT" -eq 0 ]; then
    log_error "No sorries found in file - nothing to prove!"
    exit 1
fi

log_info "Found $SORRY_COUNT sorries"

# Extract sorry names (look for theorem/lemma declarations before sorry)
SORRIES=$(grep -B5 "sorry" "$LEAN_FILE" | grep -E "^(theorem|lemma|def)" | sed 's/.*\(theorem\|lemma\|def\) \([a-zA-Z0-9_]*\).*/\2/' | sort -u)
echo -e "${BLUE}Sorries to prove:${NC}"
echo "$SORRIES" | while read -r name; do
    if [ -n "$name" ]; then
        echo "  - $name"
    fi
done

# Check for definition sorries (Aristotle skips these entirely)
DEF_SORRIES=$(grep -E "^(noncomputable )?def.*:=.*sorry|^(noncomputable )?def.*:= by.*sorry" "$LEAN_FILE" 2>/dev/null || true)
if [ -n "$DEF_SORRIES" ]; then
    log_warn "Definition sorries detected (Aristotle will SKIP these):"
    echo "$DEF_SORRIES" | while read -r line; do
        name=$(echo "$line" | sed 's/.*def \([a-zA-Z0-9_]*\).*/\1/')
        echo -e "  ${YELLOW}def $name${NC} - Aristotle cannot define data, only prove theorems"
    done
    echo ""
    echo -e "${RED}WARNING:${NC} Aristotle skips definition sorries entirely."
    echo "         Theorems depending on these definitions cannot be proved."
    echo ""
    echo "Options:"
    echo "  1. Provide actual definitions (best)"
    echo "  2. Convert to axioms with proof sketches"
    echo "  3. Submit anyway (dependent theorems will fail)"
    echo ""
    read -p "Send to Aristotle anyway? (y/N) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        log_info "Tip: Complete definitions before submission for best results."
        exit 0
    fi
    log_warn "Proceeding - definition sorries will be skipped."
fi

# Check for placeholder True theorems
PLACEHOLDER_THEOREMS=$(grep -E "theorem.*: True :=" "$LEAN_FILE" 2>/dev/null || true)
if [ -n "$PLACEHOLDER_THEOREMS" ]; then
    log_warn "Placeholder 'True' theorems detected (no value to Aristotle):"
    echo "$PLACEHOLDER_THEOREMS" | while read -r line; do
        name=$(echo "$line" | sed 's/.*theorem \([a-zA-Z0-9_]*\).*/\1/')
        echo -e "  ${YELLOW}$name : True${NC} - trivial, provides no formalization value"
    done
    echo ""
fi

# Check for potential OPEN conjectures (heuristic: names containing 'erdos_' followed by number only)
OPEN_CONJECTURES=$(echo "$SORRIES" | grep -E "^erdos_[0-9]+$" || true)
if [ -n "$OPEN_CONJECTURES" ]; then
    log_warn "Potential OPEN conjectures detected:"
    echo "$OPEN_CONJECTURES" | while read -r name; do
        echo -e "  ${YELLOW}$name${NC} - Aristotle may spin on this (no known proof)"
    done
    echo ""
    echo -e "${BLUE}Note:${NC} OPEN problems are our mission! But Aristotle does proof search,"
    echo "      not creative math. Consider working on these with Claude instead."
    echo ""
    read -p "Send to Aristotle anyway? (y/N) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        log_info "Tip: Create a version with only HARD sorries for overnight runs."
        log_info "Work on OPEN problems directly with Claude for creative approaches."
        exit 0
    fi
    log_info "Proceeding - Aristotle will attempt all sorries including OPEN ones."
fi

# Check ARISTOTLE_API_KEY
if [ -z "$ARISTOTLE_API_KEY" ]; then
    log_error "ARISTOTLE_API_KEY not set"
    echo "Set it with: export ARISTOTLE_API_KEY=your_key"
    exit 1
fi

# Submit to Aristotle
log_info "Submitting to Aristotle (async)..."

OUTPUT_FILE="${LEAN_FILE%.lean}-solved.lean"

# Run aristotle with --no-wait
SUBMIT_OUTPUT=$(cd "$PROJECT_ROOT/proofs" && uvx --from aristotlelib aristotle prove-from-file "$LEAN_FILE" --output-file "$OUTPUT_FILE" --no-wait 2>&1)

# Extract project ID from output
PROJECT_ID=$(echo "$SUBMIT_OUTPUT" | grep -oE "[a-f0-9]{8}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{4}-[a-f0-9]{12}" | head -1)

if [ -z "$PROJECT_ID" ]; then
    log_error "Failed to get project ID from Aristotle"
    echo "Output: $SUBMIT_OUTPUT"
    exit 1
fi

log_success "Submitted! Project ID: $PROJECT_ID"

# Get current timestamp
TIMESTAMP=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

# Update jobs file
log_info "Logging to $JOBS_FILE..."

# Create jobs file if it doesn't exist
if [ ! -f "$JOBS_FILE" ]; then
    echo '{"version":"1.0","jobs":[],"completed":[],"failed":[],"lessons_learned":[]}' > "$JOBS_FILE"
fi

# Add new job using jq
SORRIES_JSON=$(echo "$SORRIES" | jq -R . | jq -s .)
RELATIVE_FILE="${LEAN_FILE#$PROJECT_ROOT/}"

jq --arg pid "$PROJECT_ID" \
   --arg file "$RELATIVE_FILE" \
   --arg problem "$PROBLEM_ID" \
   --arg ts "$TIMESTAMP" \
   --argjson sorries "$SORRIES_JSON" \
   --arg notes "$NOTES" \
   '.jobs += [{
     "project_id": $pid,
     "file": $file,
     "problem_id": $problem,
     "submitted": $ts,
     "sorries": $sorries,
     "notes": $notes,
     "status": "submitted",
     "last_check": null
   }]' "$JOBS_FILE" > "${JOBS_FILE}.tmp" && mv "${JOBS_FILE}.tmp" "$JOBS_FILE"

log_success "Job logged successfully!"

echo ""
echo "============================================"
echo -e "${GREEN}Aristotle Job Submitted${NC}"
echo "============================================"
echo "Project ID:  $PROJECT_ID"
echo "Problem:     $PROBLEM_ID"
echo "File:        $RELATIVE_FILE"
echo "Sorries:     $SORRY_COUNT"
echo "Submitted:   $TIMESTAMP"
echo ""
echo "Check status with:"
echo "  ./research/scripts/aristotle-status.sh"
echo ""
echo "Or manually:"
echo "  uvx --from aristotlelib aristotle status $PROJECT_ID"
echo "============================================"
