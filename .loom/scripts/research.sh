#!/bin/bash
#
# Research Workflow Helper Script
#
# Usage:
#   ./research.sh init <problem-slug>     Initialize a new research problem
#   ./research.sh status                   Show status of all active problems
#   ./research.sh state <problem-slug>     Show current state of a problem
#   ./research.sh approach <problem> <N>   Create a new approach for a problem
#   ./research.sh list                     List all problems
#   ./research.sh help                     Show this help
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
RESEARCH_DIR="$REPO_ROOT/.loom/research"
TEMPLATES_DIR="$RESEARCH_DIR/templates"
PROBLEMS_DIR="$RESEARCH_DIR/problems"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Ensure directories exist
mkdir -p "$PROBLEMS_DIR"

show_help() {
    cat << 'EOF'
Research Workflow Helper Script

Commands:
  init <slug>           Initialize a new research problem
  status                Show status of all active problems
  state <slug>          Show current state of a specific problem
  approach <slug> <N>   Create approach N for a problem
  list                  List all problems
  help                  Show this help

Examples:
  ./research.sh init twin-prime-gaps
  ./research.sh status
  ./research.sh state twin-prime-gaps
  ./research.sh approach twin-prime-gaps 1

Problem slugs should be lowercase with hyphens (e.g., "goldbach-weak").
EOF
}

init_problem() {
    local slug="$1"

    if [ -z "$slug" ]; then
        echo -e "${RED}Error: Problem slug required${NC}"
        echo "Usage: ./research.sh init <problem-slug>"
        exit 1
    fi

    local problem_dir="$PROBLEMS_DIR/$slug"

    if [ -d "$problem_dir" ]; then
        echo -e "${YELLOW}Warning: Problem '$slug' already exists${NC}"
        echo "Directory: $problem_dir"
        exit 1
    fi

    echo -e "${BLUE}Initializing research problem: $slug${NC}"

    # Create directory structure
    mkdir -p "$problem_dir"/{approaches,literature,lean}

    # Create problem.md from template
    local date=$(date -Iseconds)
    sed -e "s/{{SLUG}}/$slug/g" \
        -e "s/{{DATE}}/$date/g" \
        -e "s/{{TITLE}}/[Problem Title]/g" \
        -e "s/{{SOURCE}}/user-request/g" \
        "$TEMPLATES_DIR/problem.md" > "$problem_dir/problem.md"

    # Create state.md
    cat > "$problem_dir/state.md" << EOF
# Research State: $slug

## Current State
**Phase**: OBSERVE
**Since**: $date
**Iteration**: 1

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.
EOF

    # Create knowledge.md
    cat > "$problem_dir/knowledge.md" << EOF
# Knowledge Base: $slug

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
EOF

    # Create literature directory with placeholder
    cat > "$problem_dir/literature/README.md" << EOF
# Literature for $slug

This directory contains:
- Related papers and their summaries
- Links to relevant Mathlib documentation
- References to similar problems and their solutions

## Related Gallery Proofs

[List proofs from src/data/proofs/ that relate to this problem]

## External References

[Papers, books, online resources]
EOF

    echo -e "${GREEN}✓ Created research workspace at: $problem_dir${NC}"
    echo ""
    echo "Next steps:"
    echo "  1. Edit $problem_dir/problem.md with the actual problem statement"
    echo "  2. Use /researcher role to begin the OODA loop"
    echo "  3. Or manually update state.md as you work"
}

show_status() {
    echo -e "${BLUE}Research Status${NC}"
    echo "==============="
    echo ""

    if [ ! -d "$PROBLEMS_DIR" ] || [ -z "$(ls -A "$PROBLEMS_DIR" 2>/dev/null)" ]; then
        echo "No active research problems."
        echo "Use './research.sh init <slug>' to start one."
        return
    fi

    for problem_dir in "$PROBLEMS_DIR"/*/; do
        if [ -d "$problem_dir" ]; then
            local slug=$(basename "$problem_dir")
            local state_file="$problem_dir/state.md"

            if [ -f "$state_file" ]; then
                local phase=$(grep "^\*\*Phase\*\*:" "$state_file" | sed 's/.*: //')
                local since=$(grep "^\*\*Since\*\*:" "$state_file" | sed 's/.*: //')
                local iteration=$(grep "^\*\*Iteration\*\*:" "$state_file" | sed 's/.*: //')

                # Color code by phase
                case "$phase" in
                    OBSERVE) color=$BLUE ;;
                    ORIENT) color=$BLUE ;;
                    DECIDE) color=$YELLOW ;;
                    ACT) color=$GREEN ;;
                    VERIFY) color=$GREEN ;;
                    LEARN) color=$YELLOW ;;
                    BREAKTHROUGH) color=$GREEN ;;
                    PIVOT) color=$RED ;;
                    *) color=$NC ;;
                esac

                printf "%-30s ${color}%-12s${NC} (iter %s)\n" "$slug" "$phase" "$iteration"
            else
                printf "%-30s ${RED}[no state file]${NC}\n" "$slug"
            fi
        fi
    done
}

show_state() {
    local slug="$1"

    if [ -z "$slug" ]; then
        echo -e "${RED}Error: Problem slug required${NC}"
        echo "Usage: ./research.sh state <problem-slug>"
        exit 1
    fi

    local problem_dir="$PROBLEMS_DIR/$slug"
    local state_file="$problem_dir/state.md"

    if [ ! -d "$problem_dir" ]; then
        echo -e "${RED}Error: Problem '$slug' not found${NC}"
        exit 1
    fi

    if [ ! -f "$state_file" ]; then
        echo -e "${RED}Error: No state.md found for '$slug'${NC}"
        exit 1
    fi

    cat "$state_file"
}

create_approach() {
    local slug="$1"
    local num="$2"

    if [ -z "$slug" ] || [ -z "$num" ]; then
        echo -e "${RED}Error: Problem slug and approach number required${NC}"
        echo "Usage: ./research.sh approach <problem-slug> <N>"
        exit 1
    fi

    local problem_dir="$PROBLEMS_DIR/$slug"
    local approach_dir="$problem_dir/approaches/approach-$num"

    if [ ! -d "$problem_dir" ]; then
        echo -e "${RED}Error: Problem '$slug' not found${NC}"
        exit 1
    fi

    if [ -d "$approach_dir" ]; then
        echo -e "${YELLOW}Warning: Approach $num already exists${NC}"
        exit 1
    fi

    echo -e "${BLUE}Creating approach $num for $slug${NC}"

    mkdir -p "$approach_dir"/{attempts,attacks}

    local date=$(date -Iseconds)
    sed -e "s/{{N}}/$num/g" \
        -e "s/{{DATE}}/$date/g" \
        -e "s/{{PROBLEM_SLUG}}/$slug/g" \
        -e "s/{{APPROACH_NAME}}/[Approach Name]/g" \
        "$TEMPLATES_DIR/hypothesis.md" > "$approach_dir/hypothesis.md"

    echo -e "${GREEN}✓ Created approach at: $approach_dir${NC}"
    echo "Edit $approach_dir/hypothesis.md to define the approach."
}

list_problems() {
    echo -e "${BLUE}Research Problems${NC}"
    echo "================="
    echo ""

    if [ ! -d "$PROBLEMS_DIR" ] || [ -z "$(ls -A "$PROBLEMS_DIR" 2>/dev/null)" ]; then
        echo "No research problems found."
        return
    fi

    for problem_dir in "$PROBLEMS_DIR"/*/; do
        if [ -d "$problem_dir" ]; then
            local slug=$(basename "$problem_dir")
            local approaches=$(ls -d "$problem_dir/approaches"/approach-* 2>/dev/null | wc -l | tr -d ' ')
            echo "  $slug ($approaches approaches)"
        fi
    done
}

# Main command dispatch
case "${1:-help}" in
    init)
        init_problem "$2"
        ;;
    status)
        show_status
        ;;
    state)
        show_state "$2"
        ;;
    approach)
        create_approach "$2" "$3"
        ;;
    list)
        list_problems
        ;;
    help|--help|-h)
        show_help
        ;;
    *)
        echo -e "${RED}Unknown command: $1${NC}"
        show_help
        exit 1
        ;;
esac
