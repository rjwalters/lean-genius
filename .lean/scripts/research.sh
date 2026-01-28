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
RESEARCH_DIR="$REPO_ROOT/research"
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
mkdir -p "$RESEARCH_DIR/knowledge"

REGISTRY_FILE="$RESEARCH_DIR/registry.json"

# Initialize registry if it doesn't exist or is malformed
init_registry() {
    if [ ! -f "$REGISTRY_FILE" ] || ! jq empty "$REGISTRY_FILE" 2>/dev/null; then
        cat > "$REGISTRY_FILE" << 'EOF'
{
  "version": "1.0.0",
  "problems": [],
  "config": {
    "maxActiveProblemsPerAgent": 1,
    "oodaTimeoutMinutes": 60,
    "attemptsBeforePivot": 5
  }
}
EOF
    fi
}

# Register a problem in the registry
register_problem() {
    local slug="$1"
    local phase="${2:-OBSERVE}"
    local path_type="${3:-full}"
    local date=$(date -Iseconds)

    init_registry

    # Check if already registered
    if jq -e --arg slug "$slug" '.problems[] | select(.slug == $slug)' "$REGISTRY_FILE" > /dev/null 2>&1; then
        echo -e "${YELLOW}Problem '$slug' already in registry, updating phase${NC}"
        update_phase "$slug" "$phase"
        return
    fi

    # Add to registry
    local tmp=$(mktemp)
    jq --arg slug "$slug" --arg phase "$phase" --arg date "$date" --arg path "$path_type" \
        '.problems += [{"slug": $slug, "phase": $phase, "path": $path, "started": $date, "status": "active"}]' \
        "$REGISTRY_FILE" > "$tmp" && mv "$tmp" "$REGISTRY_FILE"

    echo -e "${GREEN}✓ Registered '$slug' in registry (phase: $phase, path: $path_type)${NC}"
}

# Update phase for a problem
update_phase() {
    local slug="$1"
    local phase="$2"
    local date=$(date -Iseconds)

    init_registry

    local tmp=$(mktemp)
    jq --arg slug "$slug" --arg phase "$phase" --arg date "$date" \
        '(.problems[] | select(.slug == $slug)) |= . + {"phase": $phase, "lastUpdate": $date}' \
        "$REGISTRY_FILE" > "$tmp" && mv "$tmp" "$REGISTRY_FILE"

    # Also update state.md
    local state_file="$PROBLEMS_DIR/$slug/state.md"
    if [ -f "$state_file" ]; then
        sed -i '' "s/^\*\*Phase\*\*: .*/\*\*Phase\*\*: $phase/" "$state_file"
        sed -i '' "s/^\*\*Since\*\*: .*/\*\*Since\*\*: $date/" "$state_file"
    fi

    echo -e "${GREEN}✓ Updated '$slug' to phase: $phase${NC}"
}

# Convert number to word for theorem names
number_to_word() {
    case "$1" in
        2) echo "two" ;;
        3) echo "three" ;;
        4) echo "four" ;;
        5) echo "five" ;;
        6) echo "six" ;;
        7) echo "seven" ;;
        8) echo "eight" ;;
        9) echo "nine" ;;
        10) echo "ten" ;;
        11) echo "eleven" ;;
        12) echo "twelve" ;;
        13) echo "thirteen" ;;
        14) echo "fourteen" ;;
        15) echo "fifteen" ;;
        16) echo "sixteen" ;;
        17) echo "seventeen" ;;
        18) echo "eighteen" ;;
        19) echo "nineteen" ;;
        20) echo "twenty" ;;
        *) echo "$1" ;;  # Fallback to number
    esac
}

# Generate power expansion (n * n * n for cube, n * n * n * n for 4th power, etc.)
generate_power_expansion() {
    local n="$1"
    local result="n"
    for ((i=1; i<n; i++)); do
        result="$result * n"
    done
    echo "$result"
}

# Generate candidate elimination code for template (single line for sed compatibility)
generate_candidate_elimination() {
    local upper_bound="$1"
    local m="$2"
    local n="$3"

    # Just use omega - it handles all cases efficiently
    echo "omega  -- n ∈ {1..$((upper_bound-1))}, none satisfy n^$n = $m"
}

# Generate proof from template
generate_from_template() {
    local template="$1"
    local target_value="$2"
    local root_degree="$3"
    local output="$4"

    local template_file="$RESEARCH_DIR/knowledge/templates/${template}.lean.tmpl"

    if [ ! -f "$template_file" ]; then
        echo -e "${RED}Error: Template '$template' not found at $template_file${NC}"
        return 1
    fi

    # Compute parameters
    # Upper bound = floor(M^(1/n)) + 1, which is the smallest k where k^n > M
    local upper_bound
    upper_bound=$(python3 -c "import math; print(int(math.floor($target_value ** (1/$root_degree))) + 1)" 2>/dev/null || echo "3")

    local upper_power=$((upper_bound ** root_degree))
    local m_word=$(number_to_word "$target_value")
    local n_word=$(number_to_word "$root_degree")
    local power_expansion=$(generate_power_expansion "$root_degree")

    # Determine root symbol and name based on degree
    local root_symbol root_name namespace
    case "$root_degree" in
        2) root_symbol="√"; root_name="sqrt${target_value}"; namespace="SquareRoot${target_value}Irrational" ;;
        3) root_symbol="∛"; root_name="cbrt${target_value}"; namespace="CubeRoot${target_value}Irrational" ;;
        4) root_symbol="∜"; root_name="fourthrt${target_value}"; namespace="FourthRoot${target_value}Irrational" ;;
        *) root_symbol="$root_degree√"; root_name="nrt${root_degree}_${target_value}"; namespace="Root${root_degree}Of${target_value}Irrational" ;;
    esac

    # Calculate bounds comment
    local lower_val=$((upper_bound - 1))
    local lower_power=$((lower_val ** root_degree))
    local bounds_comment="${lower_val}^${root_degree}=${lower_power} < ${target_value} < ${upper_power}=${upper_bound}^${root_degree}"

    # Apply substitutions in stages to avoid issues with special characters
    local tmpout=$(mktemp)

    sed -e "s/{{M}}/${target_value}/g" \
        -e "s/{{N}}/${root_degree}/g" \
        -e "s/{{M_WORD}}/${m_word}/g" \
        -e "s/{{N_WORD}}/${n_word}/g" \
        -e "s/{{UPPER_BOUND}}/${upper_bound}/g" \
        -e "s/{{UPPER_POWER}}/${upper_power}/g" \
        -e "s/{{POWER_EXPANSION}}/${power_expansion}/g" \
        -e "s/{{ROOT_SYMBOL}}/${root_symbol}/g" \
        -e "s/{{ROOT_NAME}}/${root_name}/g" \
        -e "s/{{NAMESPACE}}/${namespace}/g" \
        -e "s/{{BOUNDS_COMMENT}}/${bounds_comment}/g" \
        -e "s/{{DATE}}/$(date +%Y-%m-%d)/g" \
        "$template_file" > "$output"

    rm -f "$tmpout" 2>/dev/null

    echo -e "${GREEN}✓ Generated proof from template${NC}"
    echo "  Template: $template"
    echo "  Value: $target_value (${root_symbol}${target_value})"
    echo "  Bounds: n < $upper_bound (${upper_bound}^${root_degree} = $upper_power > $target_value)"
    echo "  Output: $output"
}

# Mark problem as completed
complete_problem() {
    local slug="$1"
    local status="${2:-success}"
    local date=$(date -Iseconds)

    init_registry

    local tmp=$(mktemp)
    jq --arg slug "$slug" --arg status "$status" --arg date "$date" \
        '(.problems[] | select(.slug == $slug)) |= . + {"status": $status, "completed": $date}' \
        "$REGISTRY_FILE" > "$tmp" && mv "$tmp" "$REGISTRY_FILE"

    echo -e "${GREEN}✓ Marked '$slug' as $status${NC}"
}

# Graduate a proof to the gallery
graduate_problem() {
    local slug="$1"

    if [ -z "$slug" ]; then
        echo -e "${RED}Error: Problem slug required${NC}"
        exit 1
    fi

    local problem_dir="$PROBLEMS_DIR/$slug"

    if [ ! -d "$problem_dir" ]; then
        echo -e "${RED}Error: Problem '$slug' not found${NC}"
        exit 1
    fi

    # Convert slug to CamelCase for Lean file
    # e.g., cube-root-5-irrational -> CubeRoot5Irrational
    local proof_name=$(echo "$slug" | awk -F'-' '{for(i=1;i<=NF;i++) printf toupper(substr($i,1,1)) substr($i,2)}')

    # Find successful Lean attempt
    local attempt=$(find "$problem_dir/approaches" -name "*.lean" 2>/dev/null | head -1)

    if [ -z "$attempt" ]; then
        echo -e "${RED}Error: No Lean proof found for '$slug'${NC}"
        exit 1
    fi

    local dest="$REPO_ROOT/proofs/Proofs/${proof_name}.lean"

    if [ -f "$dest" ]; then
        echo -e "${YELLOW}Warning: $dest already exists${NC}"
        read -p "Overwrite? (y/N) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            exit 1
        fi
    fi

    # Pre-copy validation: compile in place first
    echo -e "${BLUE}Validating proof before copy...${NC}"
    # Convert to path relative to proofs directory if it's absolute
    local relative_attempt
    if [[ "$attempt" = /* ]]; then
        relative_attempt="$attempt"
    else
        relative_attempt="../$attempt"
    fi
    if ! (cd "$REPO_ROOT/proofs" && lake env lean "$relative_attempt" 2>&1); then
        echo -e "${RED}Proof does not compile. Fix errors before graduating.${NC}"
        echo ""
        echo -e "${YELLOW}Hint: Check the proof at:${NC}"
        echo "  $attempt"
        exit 1
    fi
    echo -e "${GREEN}✓ Proof validates${NC}"

    # Now safe to copy
    echo -e "${BLUE}Graduating proof to gallery...${NC}"
    cp "$attempt" "$dest"

    # Build in gallery
    echo -e "${BLUE}Building proof in gallery...${NC}"
    if (cd "$REPO_ROOT/proofs" && lake build "Proofs.${proof_name}" 2>&1); then
        echo -e "${GREEN}✓ Build successful${NC}"
        complete_problem "$slug" "graduated"
        echo -e "${GREEN}✓ Graduated '$slug' to proofs/Proofs/${proof_name}.lean${NC}"
    else
        echo -e "${RED}Build failed after copy. Removing from gallery.${NC}"
        rm -f "$dest"
        exit 1
    fi
}

# Extract learnings to global knowledge base
extract_learnings() {
    local slug="$1"

    if [ -z "$slug" ]; then
        echo -e "${RED}Error: Problem slug required${NC}"
        exit 1
    fi

    local problem_dir="$PROBLEMS_DIR/$slug"
    local knowledge_dir="$RESEARCH_DIR/knowledge"

    # Check for success-recap or knowledge.md
    local recap="$problem_dir/success-recap.md"
    local knowledge="$problem_dir/knowledge.md"

    if [ ! -f "$recap" ] && [ ! -f "$knowledge" ]; then
        echo -e "${YELLOW}No success-recap.md or knowledge.md found for '$slug'${NC}"
        exit 1
    fi

    echo -e "${BLUE}Extracting learnings from '$slug'...${NC}"

    # Initialize global knowledge files if needed
    if [ ! -f "$knowledge_dir/tactics.md" ]; then
        cat > "$knowledge_dir/tactics.md" << 'EOF'
# Tactic Patterns

Reusable tactic patterns discovered during research.

---

EOF
    fi

    if [ ! -f "$knowledge_dir/theorems.md" ]; then
        cat > "$knowledge_dir/theorems.md" << 'EOF'
# Mathlib Theorems

Useful theorems organized by topic.

---

EOF
    fi

    # Append a reference to the problem's learnings
    local date=$(date +%Y-%m-%d)
    echo "" >> "$knowledge_dir/tactics.md"
    echo "## From: $slug ($date)" >> "$knowledge_dir/tactics.md"
    echo "See: research/problems/$slug/knowledge.md" >> "$knowledge_dir/tactics.md"
    echo "" >> "$knowledge_dir/tactics.md"

    echo -e "${GREEN}✓ Added reference in knowledge/tactics.md${NC}"
    echo -e "${YELLOW}Please manually extract specific patterns to the appropriate knowledge files${NC}"
}

# Derive a new problem from an existing one
derive_problem() {
    local slug="$1"
    local source="$2"
    local date=$(date -Iseconds)

    if [ -z "$slug" ] || [ -z "$source" ]; then
        echo -e "${RED}Error: Both target slug and source slug required${NC}"
        exit 1
    fi

    local source_dir="$PROBLEMS_DIR/$source"
    local problem_dir="$PROBLEMS_DIR/$slug"

    if [ ! -d "$source_dir" ]; then
        echo -e "${RED}Error: Source problem '$source' not found${NC}"
        exit 1
    fi

    if [ -d "$problem_dir" ]; then
        echo -e "${YELLOW}Warning: Problem '$slug' already exists${NC}"
        exit 1
    fi

    echo -e "${BLUE}📋 Deriving '$slug' from '$source'...${NC}"

    # Extract numeric values from slugs for substitution
    local source_val=$(echo "$source" | grep -oE '[0-9]+' | head -1)
    local target_val=$(echo "$slug" | grep -oE '[0-9]+' | head -1)

    if [ -z "$source_val" ] || [ -z "$target_val" ]; then
        echo -e "${YELLOW}Warning: Could not extract numeric values for substitution${NC}"
        echo "Source: $source → value: $source_val"
        echo "Target: $slug → value: $target_val"
    fi

    # Find source proof
    local source_proof=$(find "$source_dir/approaches" -name "*.lean" 2>/dev/null | head -1)

    if [ -z "$source_proof" ]; then
        echo -e "${RED}Error: No Lean proof found in source problem${NC}"
        exit 1
    fi

    echo -e "  Source proof: $source_proof"
    echo -e "  Substitution: $source_val → $target_val"

    # Create directory structure
    mkdir -p "$problem_dir/approaches/approach-01/attempts"

    # Generate derived proof with substitutions
    local target_proof="$problem_dir/approaches/approach-01/attempts/attempt-01.lean"

    # Perform substitutions
    sed -e "s/\b${source_val}\b/${target_val}/g" \
        -e "s/cbrt${source_val}/cbrt${target_val}/g" \
        -e "s/Cbrt${source_val}/Cbrt${target_val}/g" \
        -e "s/CubeRoot${source_val}/CubeRoot${target_val}/g" \
        -e "s/${source}_/${target_val}_/g" \
        -e "s/cube-root-${source_val}/cube-root-${target_val}/g" \
        -e "s/Date: .*/Date: $(date +%Y-%m-%d)/" \
        -e "s/Status: .*/Status: DERIVED (needs verification)/" \
        "$source_proof" > "$target_proof"

    echo -e "${GREEN}  ✓ Generated: $target_proof${NC}"

    # Create state.md
    cat > "$problem_dir/state.md" << EOF
# Research State: $slug

## Current State
**Phase**: ACT
**Path**: fast (derived)
**Since**: $date
**Iteration**: 1
**Derived From**: $source

## Current Focus
Verify derived proof compiles and adjust bounds if needed.

## Active Approach
approach-01 (derived from $source)

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None.

## Next Action
1. Review generated proof for correctness
2. Adjust bounds if needed (check UPPER_BOUND)
3. Build: cd proofs && lake env lean <path-to-proof>
4. If successful, graduate
EOF

    # Create minimal knowledge.md
    cat > "$problem_dir/knowledge.md" << EOF
# Knowledge Base: $slug

## Derivation

**Derived from**: $source
**Substitutions**: $source_val → $target_val
**Pattern used**: n-th Root Irrationality (see knowledge/patterns.md)

## Verification Notes

[Add notes about any adjustments made to the derived proof]
EOF

    # Record derivation link
    echo "$source" > "$problem_dir/derived_from"

    # Register in registry
    register_problem "$slug" "ACT" "fast"

    # Update registry with derivation info
    local tmp=$(mktemp)
    jq --arg slug "$slug" --arg source "$source" \
        '(.problems[] | select(.slug == $slug)) |= . + {"derived_from": $source}' \
        "$REGISTRY_FILE" > "$tmp" && mv "$tmp" "$REGISTRY_FILE"

    # Create completion signal for daemon stats tracking (problem selected for research)
    local completions_dir="$REPO_ROOT/.loom/signals/completions"
    mkdir -p "$completions_dir"
    touch "$completions_dir/problem-selected-$slug-$(date +%s)"

    echo ""
    echo -e "${GREEN}✓ Derived problem created!${NC}"
    echo ""
    echo -e "${YELLOW}Review the generated proof:${NC}"
    echo "  $target_proof"
    echo ""
    echo -e "${YELLOW}Key things to check:${NC}"
    echo "  1. Numeric substitutions are correct"
    echo "  2. Bounds are still valid (e.g., 1³ < $target_val < 2³?)"
    echo "  3. Namespace/theorem names are correct"
    echo ""
    echo -e "${BLUE}To verify and build:${NC}"
    echo "  cd proofs && lake env lean ../$target_proof"
    echo ""
    echo -e "${BLUE}If successful, graduate:${NC}"
    echo "  ./research.sh graduate $slug"
}

show_help() {
    cat << 'EOF'
Research Workflow Helper Script

Commands:
  init <slug> [--fast|--full]  Initialize a new research problem
  init <slug> --derive-from=<source>  Derive from existing problem (sed-based)
  init <slug> --template=<name> [--value=N] [--degree=N]  Generate from template
  status                       Show status of all active problems
  state <slug>                 Show current state of a specific problem
  approach <slug> <N>          Create approach N for a problem
  phase <slug> <PHASE>         Update phase for a problem
  complete <slug> [status]     Mark problem as completed (success/failure/abandoned)
  graduate <slug>              Graduate successful proof to gallery (validates first!)
  learn <slug>                 Extract learnings to global knowledge base
  list                         List all problems
  help                         Show this help

Phases: OBSERVE, ORIENT, DECIDE, ACT, VERIFY, LEARN, PIVOT, BREAKTHROUGH

Template Options:
  --template=<name>   Use template (e.g., nrt-irrational)
  --value=N           Target value (e.g., 9 for ∛9). Auto-detected from slug if omitted.
  --degree=N          Root degree (default: 3 for cube root)

Examples:
  ./research.sh init twin-prime-gaps --fast
  ./research.sh init cube-root-9-irrational --template=nrt-irrational
  ./research.sh init cube-root-10-irrational --template=nrt-irrational --value=10
  ./research.sh phase twin-prime-gaps ACT
  ./research.sh complete twin-prime-gaps success
  ./research.sh graduate twin-prime-gaps

Problem slugs should be lowercase with hyphens (e.g., "goldbach-weak").
EOF
}

init_problem() {
    local slug="$1"
    local path_type="full"
    local derive_from=""
    local template=""
    local template_value=""
    local template_degree="3"  # Default to cube root

    # Parse flags
    shift
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --fast) path_type="fast"; shift ;;
            --full) path_type="full"; shift ;;
            --derive-from)
                derive_from="$2"
                path_type="fast"  # Derived problems use fast path
                shift 2
                ;;
            --derive-from=*)
                derive_from="${1#*=}"
                path_type="fast"
                shift
                ;;
            --template)
                template="$2"
                path_type="fast"
                shift 2
                ;;
            --template=*)
                template="${1#*=}"
                path_type="fast"
                shift
                ;;
            --value)
                template_value="$2"
                shift 2
                ;;
            --value=*)
                template_value="${1#*=}"
                shift
                ;;
            --degree)
                template_degree="$2"
                shift 2
                ;;
            --degree=*)
                template_degree="${1#*=}"
                shift
                ;;
            *) shift ;;
        esac
    done

    if [ -z "$slug" ]; then
        echo -e "${RED}Error: Problem slug required${NC}"
        echo "Usage: ./research.sh init <problem-slug> [--fast|--full] [--derive-from=<source-slug>]"
        exit 1
    fi

    # If deriving, delegate to derive_problem
    if [ -n "$derive_from" ]; then
        derive_problem "$slug" "$derive_from"
        return
    fi

    # If using template, generate from template
    if [ -n "$template" ]; then
        # Extract value from slug if not provided
        if [ -z "$template_value" ]; then
            template_value=$(echo "$slug" | grep -oE '[0-9]+' | head -1)
        fi

        if [ -z "$template_value" ]; then
            echo -e "${RED}Error: Could not determine value from slug. Use --value=N${NC}"
            exit 1
        fi

        local problem_dir="$PROBLEMS_DIR/$slug"

        if [ -d "$problem_dir" ]; then
            echo -e "${YELLOW}Warning: Problem '$slug' already exists${NC}"
            exit 1
        fi

        echo -e "${BLUE}📋 Generating '$slug' from template '$template'...${NC}"

        # Create directory structure
        mkdir -p "$problem_dir/approaches/approach-01/attempts"

        # Generate proof from template
        local target_proof="$problem_dir/approaches/approach-01/attempts/attempt-01.lean"
        if ! generate_from_template "$template" "$template_value" "$template_degree" "$target_proof"; then
            echo -e "${RED}Template generation failed${NC}"
            rm -rf "$problem_dir"
            exit 1
        fi

        # Create state.md
        local date=$(date -Iseconds)
        cat > "$problem_dir/state.md" << EOF
# Research State: $slug

## Current State
**Phase**: ACT
**Path**: fast (template-generated)
**Since**: $date
**Iteration**: 1
**Template**: $template
**Value**: $template_value
**Degree**: $template_degree

## Current Focus
Verify generated proof compiles.

## Active Approach
approach-01 (generated from template $template)

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
None.

## Next Action
1. Build: cd proofs && lake env lean <path-to-proof>
2. If successful, graduate
EOF

        # Create knowledge.md
        cat > "$problem_dir/knowledge.md" << EOF
# Knowledge Base: $slug

## Generation

**Template**: $template
**Value**: $template_value
**Degree**: $template_degree
**Pattern used**: n-th Root Irrationality (see knowledge/patterns.md)

## Verification Notes

[Add notes about any adjustments made to the generated proof]
EOF

        # Register in registry
        register_problem "$slug" "ACT" "fast"

        # Update registry with template info
        local tmp=$(mktemp)
        jq --arg slug "$slug" --arg template "$template" --arg value "$template_value" \
            '(.problems[] | select(.slug == $slug)) |= . + {"template": $template, "template_value": $value}' \
            "$REGISTRY_FILE" > "$tmp" && mv "$tmp" "$REGISTRY_FILE"

        # Create completion signal for daemon stats tracking (problem selected for research)
        local completions_dir="$REPO_ROOT/.loom/signals/completions"
        mkdir -p "$completions_dir"
        touch "$completions_dir/problem-selected-$slug-$(date +%s)"

        echo ""
        echo -e "${GREEN}✓ Template-generated problem created!${NC}"
        echo ""
        echo -e "${BLUE}To verify and build:${NC}"
        echo "  cd proofs && lake env lean ../$target_proof"
        echo ""
        echo -e "${BLUE}If successful, graduate:${NC}"
        echo "  ./research.sh graduate $slug"
        return
    fi

    local problem_dir="$PROBLEMS_DIR/$slug"

    if [ -d "$problem_dir" ]; then
        echo -e "${YELLOW}Warning: Problem '$slug' already exists${NC}"
        echo "Directory: $problem_dir"
        exit 1
    fi

    echo -e "${BLUE}Initializing research problem: $slug (path: $path_type)${NC}"

    # Create directory structure (simplified for fast path)
    if [ "$path_type" = "fast" ]; then
        mkdir -p "$problem_dir"/{approaches,lean}
    else
        mkdir -p "$problem_dir"/{approaches,literature,lean}
    fi

    # Create problem.md from template
    local date=$(date -Iseconds)
    sed -e "s/{{SLUG}}/$slug/g" \
        -e "s/{{DATE}}/$date/g" \
        -e "s/{{TITLE}}/[Problem Title]/g" \
        -e "s/{{SOURCE}}/user-request/g" \
        "$TEMPLATES_DIR/problem.md" > "$problem_dir/problem.md"

    # Create state.md with path type
    cat > "$problem_dir/state.md" << EOF
# Research State: $slug

## Current State
**Phase**: OBSERVE
**Path**: $path_type
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
$(if [ "$path_type" = "fast" ]; then
    echo "Fast path: Quick Mathlib search, then directly to ACT if obvious approach found."
    echo "See FAST_PATH.md for protocol."
else
    echo "Read problem.md thoroughly and acquire full context."
    echo "Then move to ORIENT phase to explore literature and related proofs."
fi)
EOF

    # Register in registry
    register_problem "$slug" "OBSERVE" "$path_type"

    # Create completion signal for daemon stats tracking (problem selected for research)
    local completions_dir="$REPO_ROOT/.loom/signals/completions"
    mkdir -p "$completions_dir"
    touch "$completions_dir/problem-selected-$slug-$(date +%s)"

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

    # Create literature directory with placeholder (full path only)
    if [ "$path_type" = "full" ]; then
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
    fi

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
        shift
        init_problem "$@"
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
    phase)
        if [ -z "$2" ] || [ -z "$3" ]; then
            echo -e "${RED}Error: Problem slug and phase required${NC}"
            echo "Usage: ./research.sh phase <slug> <PHASE>"
            exit 1
        fi
        update_phase "$2" "$3"
        ;;
    complete)
        if [ -z "$2" ]; then
            echo -e "${RED}Error: Problem slug required${NC}"
            echo "Usage: ./research.sh complete <slug> [status]"
            exit 1
        fi
        complete_problem "$2" "${3:-success}"
        ;;
    graduate)
        graduate_problem "$2"
        ;;
    learn)
        extract_learnings "$2"
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
