#!/bin/bash
#
# synthesize-knowledge.sh - Aggregate cross-problem knowledge and patterns
#
# Scans all research problem files and knowledge bases to:
# - Build a technique index (which techniques, which problems, what results)
# - Identify common Mathlib gaps across problems
# - Surface cross-problem insights
# - Update the patterns.md synthesis report
#
# Usage:
#   ./synthesize-knowledge.sh                Run full synthesis
#   ./synthesize-knowledge.sh --report       Generate report only (no file updates)
#   ./synthesize-knowledge.sh --techniques   Update technique index only
#   ./synthesize-knowledge.sh --gaps         Report Mathlib gaps only
#
# Output:
#   research/knowledge/technique-index.json  Updated technique index
#   research/knowledge/synthesis-report.md   Full synthesis report
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
PROBLEMS_DIR="$REPO_ROOT/src/data/research/problems"
KNOWLEDGE_DIR="$REPO_ROOT/research/knowledge"
TECHNIQUE_INDEX="$KNOWLEDGE_DIR/technique-index.json"
SYNTHESIS_REPORT="$KNOWLEDGE_DIR/synthesis-report.md"
CANDIDATE_POOL="$REPO_ROOT/research/candidate-pool.json"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

print_info() { echo -e "${BLUE}i $1${NC}"; }
print_success() { echo -e "${GREEN}+ $1${NC}"; }
print_warning() { echo -e "${YELLOW}! $1${NC}"; }

# Parse arguments
MODE="full"
case "${1:-}" in
    --report)   MODE="report" ;;
    --techniques) MODE="techniques" ;;
    --gaps)     MODE="gaps" ;;
    --help|-h)
        echo "Usage: $0 [--report|--techniques|--gaps]"
        echo ""
        echo "Modes:"
        echo "  (none)        Full synthesis (techniques + gaps + report)"
        echo "  --report      Generate synthesis report only"
        echo "  --techniques  Update technique index only"
        echo "  --gaps        Report Mathlib gaps only"
        exit 0
        ;;
esac

# Ensure directories exist
mkdir -p "$KNOWLEDGE_DIR"

# Count total problems
count_problems() {
    if [[ -d "$PROBLEMS_DIR" ]]; then
        ls "$PROBLEMS_DIR"/*.json 2>/dev/null | wc -l | tr -d ' '
    else
        echo "0"
    fi
}

# Extract all insights across problems
extract_insights() {
    print_info "Extracting insights from $(count_problems) problem files..."

    local total_insights=0
    local total_gaps=0
    local total_built=0
    local total_steps=0

    for file in "$PROBLEMS_DIR"/*.json; do
        [[ -f "$file" ]] || continue
        local id
        id=$(basename "$file" .json)

        local insights gaps built steps
        insights=$(jq -r '.knowledge.insights | length' "$file" 2>/dev/null || echo "0")
        gaps=$(jq -r '.knowledge.mathlibGaps | length' "$file" 2>/dev/null || echo "0")
        built=$(jq -r '.knowledge.builtItems | length' "$file" 2>/dev/null || echo "0")
        steps=$(jq -r '.knowledge.nextSteps | length' "$file" 2>/dev/null || echo "0")

        total_insights=$((total_insights + insights))
        total_gaps=$((total_gaps + gaps))
        total_built=$((total_built + built))
        total_steps=$((total_steps + steps))
    done

    echo "  Insights: $total_insights"
    echo "  Mathlib gaps: $total_gaps"
    echo "  Built items: $total_built"
    echo "  Next steps: $total_steps"
}

# Extract and deduplicate Mathlib gaps
extract_gaps() {
    print_info "Extracting Mathlib gaps..."

    local gaps_file
    gaps_file=$(mktemp)

    for file in "$PROBLEMS_DIR"/*.json; do
        [[ -f "$file" ]] || continue
        local id
        id=$(basename "$file" .json)
        jq -r --arg id "$id" '.knowledge.mathlibGaps[]? | "\(.) [from: \($id)]"' "$file" 2>/dev/null >> "$gaps_file"
    done

    if [[ -s "$gaps_file" ]]; then
        echo ""
        echo "=== Mathlib Gaps (across all problems) ==="
        sort "$gaps_file" | uniq -c | sort -rn | head -20
        echo ""
        local gap_count
        gap_count=$(wc -l < "$gaps_file" | tr -d ' ')
        local unique_count
        unique_count=$(sort "$gaps_file" | uniq | wc -l | tr -d ' ')
        echo "Total: $gap_count gap mentions, $unique_count unique gaps"
    else
        echo "  No Mathlib gaps found across problems"
    fi

    rm -f "$gaps_file"
}

# Generate synthesis report
generate_report() {
    print_info "Generating synthesis report..."

    local date
    date=$(date +"%Y-%m-%d %H:%M")
    local problem_count
    problem_count=$(count_problems)

    cat > "$SYNTHESIS_REPORT" << HEADER
# Knowledge Synthesis Report

**Generated**: $date
**Problems analyzed**: $problem_count

---

## Summary Statistics

HEADER

    # Knowledge distribution
    echo "### Knowledge Distribution" >> "$SYNTHESIS_REPORT"
    echo "" >> "$SYNTHESIS_REPORT"
    echo "| Tier | Count | Description |" >> "$SYNTHESIS_REPORT"
    echo "|------|-------|-------------|" >> "$SYNTHESIS_REPORT"

    local empty=0 weak=0 moderate=0 rich=0
    for file in "$PROBLEMS_DIR"/*.json; do
        [[ -f "$file" ]] || continue
        local score
        score=$(jq '[.knowledge.insights, .knowledge.builtItems, .knowledge.mathlibGaps, .knowledge.nextSteps] | map(length) | add' "$file" 2>/dev/null || echo "0")

        if [[ "$score" -eq 0 ]]; then
            empty=$((empty + 1))
        elif [[ "$score" -le 5 ]]; then
            weak=$((weak + 1))
        elif [[ "$score" -le 15 ]]; then
            moderate=$((moderate + 1))
        else
            rich=$((rich + 1))
        fi
    done

    echo "| EMPTY (0) | $empty | No research yet |" >> "$SYNTHESIS_REPORT"
    echo "| WEAK (1-5) | $weak | Minimal research |" >> "$SYNTHESIS_REPORT"
    echo "| MODERATE (6-15) | $moderate | Active research |" >> "$SYNTHESIS_REPORT"
    echo "| RICH (16+) | $rich | Well-researched |" >> "$SYNTHESIS_REPORT"
    echo "" >> "$SYNTHESIS_REPORT"

    # Pool status
    if [[ -f "$CANDIDATE_POOL" ]]; then
        echo "### Candidate Pool Status" >> "$SYNTHESIS_REPORT"
        echo "" >> "$SYNTHESIS_REPORT"
        echo "| Status | Count |" >> "$SYNTHESIS_REPORT"
        echo "|--------|-------|" >> "$SYNTHESIS_REPORT"
        jq -r '.candidates | group_by(.status) | map("| \(.[0].status) | \(length) |") | .[]' "$CANDIDATE_POOL" >> "$SYNTHESIS_REPORT" 2>/dev/null
        echo "" >> "$SYNTHESIS_REPORT"
    fi

    # Top Mathlib gaps
    echo "### Most Common Mathlib Gaps" >> "$SYNTHESIS_REPORT"
    echo "" >> "$SYNTHESIS_REPORT"

    local has_gaps=false
    for file in "$PROBLEMS_DIR"/*.json; do
        [[ -f "$file" ]] || continue
        local gap_count
        gap_count=$(jq -r '.knowledge.mathlibGaps | length' "$file" 2>/dev/null || echo "0")
        if [[ "$gap_count" -gt 0 ]]; then
            has_gaps=true
            break
        fi
    done

    if [[ "$has_gaps" == "true" ]]; then
        local gaps_tmp
        gaps_tmp=$(mktemp)
        for file in "$PROBLEMS_DIR"/*.json; do
            [[ -f "$file" ]] || continue
            jq -r '.knowledge.mathlibGaps[]?' "$file" 2>/dev/null >> "$gaps_tmp"
        done
        echo "| Gap | Occurrences |" >> "$SYNTHESIS_REPORT"
        echo "|-----|-------------|" >> "$SYNTHESIS_REPORT"
        sort "$gaps_tmp" | uniq -c | sort -rn | head -10 | while read -r count gap; do
            echo "| $gap | $count |" >> "$SYNTHESIS_REPORT"
        done
        rm -f "$gaps_tmp"
    else
        echo "No Mathlib gaps recorded yet." >> "$SYNTHESIS_REPORT"
    fi

    echo "" >> "$SYNTHESIS_REPORT"

    # Cross-problem patterns
    echo "### Cross-Problem Patterns" >> "$SYNTHESIS_REPORT"
    echo "" >> "$SYNTHESIS_REPORT"
    echo "Patterns are extracted from insights across all problems." >> "$SYNTHESIS_REPORT"
    echo "Run this script periodically to keep patterns current." >> "$SYNTHESIS_REPORT"
    echo "" >> "$SYNTHESIS_REPORT"

    # Technique index summary
    if [[ -f "$TECHNIQUE_INDEX" ]]; then
        local tech_count
        tech_count=$(jq '.techniques | length' "$TECHNIQUE_INDEX" 2>/dev/null || echo "0")
        echo "### Technique Index" >> "$SYNTHESIS_REPORT"
        echo "" >> "$SYNTHESIS_REPORT"
        echo "Tracked techniques: $tech_count" >> "$SYNTHESIS_REPORT"
        echo "" >> "$SYNTHESIS_REPORT"
        if [[ "$tech_count" -gt 0 ]]; then
            echo "| Technique | Problems Used | Success Rate |" >> "$SYNTHESIS_REPORT"
            echo "|-----------|---------------|--------------|" >> "$SYNTHESIS_REPORT"
            jq -r '.techniques[] | "| \(.name) | \(.used_in_problems | length) | \(.success_rate // "N/A") |"' "$TECHNIQUE_INDEX" >> "$SYNTHESIS_REPORT" 2>/dev/null
        fi
    fi

    echo "" >> "$SYNTHESIS_REPORT"
    echo "---" >> "$SYNTHESIS_REPORT"
    echo "" >> "$SYNTHESIS_REPORT"
    echo "*Report generated by synthesize-knowledge.sh*" >> "$SYNTHESIS_REPORT"

    print_success "Report written to $SYNTHESIS_REPORT"
}

# Main
print_info "Knowledge Synthesis (mode: $MODE)"
echo ""

case "$MODE" in
    full)
        extract_insights
        echo ""
        extract_gaps
        echo ""
        generate_report
        ;;
    report)
        generate_report
        ;;
    techniques)
        print_info "Technique index is updated by the Chronicler during LEARN phase"
        print_info "Current index: $TECHNIQUE_INDEX"
        if [[ -f "$TECHNIQUE_INDEX" ]]; then
            jq '.techniques | length' "$TECHNIQUE_INDEX"
            echo "techniques tracked"
        fi
        ;;
    gaps)
        extract_gaps
        ;;
esac

echo ""
print_success "Synthesis complete"
