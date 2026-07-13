#!/bin/bash
#
# validate-for-aristotle.sh - Pre-submission validation for Aristotle compatibility
#
# Usage:
#   ./validate-for-aristotle.sh <lean-file>
#   ./validate-for-aristotle.sh <lean-file> --fix  # Show suggested fixes
#
# Exit codes:
#   0 - File is compatible with Aristotle
#   1 - Compatibility issues found (submission may fail)
#   2 - File not found or other error
#
# Known Aristotle Incompatibilities:
#   - /-! docstrings (use /- instead)
#   - Complex nested namespaces
#   - Definition sorries (Aristotle skips these)
#   - Missing type annotations in some contexts
#
# See also: CLAUDE.md "Aristotle: Syntax Compatibility" section

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

usage() {
    echo "Usage: $0 <lean-file> [--fix]"
    echo ""
    echo "Validates Lean file for Aristotle proof search compatibility."
    echo ""
    echo "Options:"
    echo "  --fix    Show suggested fixes for issues found"
    echo ""
    echo "Exit codes:"
    echo "  0 - Compatible"
    echo "  1 - Issues found"
    echo "  2 - Error"
    exit 2
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_ok() {
    echo -e "${GREEN}[OK]${NC} $1"
}

# Parse arguments
LEAN_FILE=""
SHOW_FIX=false

for arg in "$@"; do
    case $arg in
        --fix)
            SHOW_FIX=true
            ;;
        -h|--help)
            usage
            ;;
        *)
            if [ -z "$LEAN_FILE" ]; then
                LEAN_FILE="$arg"
            fi
            ;;
    esac
done

if [ -z "$LEAN_FILE" ]; then
    usage
fi

# Resolve file path
if [ ! -f "$LEAN_FILE" ]; then
    if [ -f "$PROJECT_ROOT/$LEAN_FILE" ]; then
        LEAN_FILE="$PROJECT_ROOT/$LEAN_FILE"
    else
        log_error "File not found: $LEAN_FILE"
        exit 2
    fi
fi

LEAN_FILE="$(cd "$(dirname "$LEAN_FILE")" && pwd)/$(basename "$LEAN_FILE")"
FILENAME=$(basename "$LEAN_FILE")

echo ""
echo "========================================"
echo "Aristotle Compatibility Validation"
echo "========================================"
echo "File: $FILENAME"
echo ""

ISSUES=0
WARNINGS=0

# ---------------------------------------------------------------------------
# Check 1: /-! docstrings (CRITICAL - causes parse errors)
# ---------------------------------------------------------------------------
DOCSTRINGS=$(grep -n "/-!" "$LEAN_FILE" 2>/dev/null || true)
if [ -n "$DOCSTRINGS" ]; then
    ((++ISSUES))
    log_error "Found /-! docstrings (Aristotle parser fails on these)"
    echo "$DOCSTRINGS" | head -5 | while read -r line; do
        echo "    $line"
    done
    if [ "$SHOW_FIX" = true ]; then
        echo ""
        echo -e "  ${BLUE}Fix:${NC} Replace /-! with /- or use regular comments"
        echo "       sed 's|/-!|/-|g' $FILENAME > $FILENAME.tmp && mv $FILENAME.tmp $FILENAME"
    fi
    echo ""
fi

# ---------------------------------------------------------------------------
# Check 2: Definition sorries (CRITICAL - blocks dependent theorems)
# ---------------------------------------------------------------------------
DEF_SORRIES=$(grep -nE "^(noncomputable )?(abbrev |def |instance )[a-zA-Z0-9_]+.*:=.*sorry|^(noncomputable )?(abbrev |def |instance )[a-zA-Z0-9_]+.*:= by sorry" "$LEAN_FILE" 2>/dev/null || true)
if [ -n "$DEF_SORRIES" ]; then
    ((++ISSUES))
    log_error "Found definition sorries (Aristotle skips these entirely)"
    echo "$DEF_SORRIES" | head -5 | while read -r line; do
        echo "    $line"
    done
    if [ "$SHOW_FIX" = true ]; then
        echo ""
        echo -e "  ${BLUE}Fix:${NC} Provide actual implementations for definitions."
        echo "       Aristotle can only prove theorem/lemma sorries, not define data."
        echo "       All theorems depending on these definitions will fail."
    fi
    echo ""
fi

# ---------------------------------------------------------------------------
# Check 3: Complex namespace nesting (WARNING - may cause issues)
# ---------------------------------------------------------------------------
NAMESPACE_DEPTH=$(grep -c "^namespace " "$LEAN_FILE" 2>/dev/null | head -1 || echo "0")
END_COUNT=$(grep -c "^end " "$LEAN_FILE" 2>/dev/null | head -1 || echo "0")
if [ "$NAMESPACE_DEPTH" -gt 3 ]; then
    ((++WARNINGS))
    log_warn "Deep namespace nesting ($NAMESPACE_DEPTH levels) may cause issues"
    if [ "$SHOW_FIX" = true ]; then
        echo -e "  ${BLUE}Fix:${NC} Consider flattening namespace structure"
    fi
    echo ""
fi

# Check for mismatched namespace/end
if [ "$NAMESPACE_DEPTH" -ne "$END_COUNT" ]; then
    ((++WARNINGS))
    log_warn "Namespace/end count mismatch ($NAMESPACE_DEPTH namespaces, $END_COUNT ends)"
    echo ""
fi

# ---------------------------------------------------------------------------
# Check 4: Axioms without theorem conversion note (INFO)
# ---------------------------------------------------------------------------
AXIOM_COUNT=$(grep -c "^axiom " "$LEAN_FILE" 2>/dev/null | head -1 || echo "0")
if [ "$AXIOM_COUNT" -gt 0 ]; then
    ((++WARNINGS))
    log_warn "Found $AXIOM_COUNT axiom declarations"
    echo "    Aristotle treats axioms as 'given' and will NOT attempt to prove them."
    echo "    If you want Aristotle to prove these, convert to theorem sorries."
    if [ "$SHOW_FIX" = true ]; then
        echo ""
        echo -e "  ${BLUE}Fix:${NC} Convert axioms to theorem sorries:"
        echo "       sed -i.bak 's/^axiom \\([^:]*\\):/theorem \\1 :=/; s/theorem \\([^:]*\\) :=\$/theorem \\1 := by sorry/' $FILENAME"
    fi
    echo ""
fi

# ---------------------------------------------------------------------------
# Check 5: Placeholder True theorems (WARNING)
# ---------------------------------------------------------------------------
TRUE_THEOREMS=$(grep -n "theorem.*: True" "$LEAN_FILE" 2>/dev/null || true)
if [ -n "$TRUE_THEOREMS" ]; then
    ((++WARNINGS))
    log_warn "Found placeholder 'True' theorems (trivial, no value)"
    echo "$TRUE_THEOREMS" | head -3 | while read -r line; do
        echo "    $line"
    done
    echo ""
fi

# ---------------------------------------------------------------------------
# Check 6: Unicode issues (rare but possible)
# ---------------------------------------------------------------------------
# Check for unusual Unicode that might cause parsing issues
UNUSUAL_UNICODE=$(grep -nP '[^\x00-\x7F\xCE\xCF\xE2\xC2]' "$LEAN_FILE" 2>/dev/null | head -3 || true)
if [ -n "$UNUSUAL_UNICODE" ]; then
    ((++WARNINGS))
    log_warn "Unusual Unicode characters detected (may cause issues)"
    echo "$UNUSUAL_UNICODE" | while read -r line; do
        echo "    $line"
    done
    echo ""
fi

# ---------------------------------------------------------------------------
# Check 7: Import compatibility
# ---------------------------------------------------------------------------
# Check for imports that Aristotle might not have
UNUSUAL_IMPORTS=$(grep "^import " "$LEAN_FILE" 2>/dev/null | grep -vE "(Mathlib|Lean|Init|Proofs)" || true)
if [ -n "$UNUSUAL_IMPORTS" ]; then
    ((++WARNINGS))
    log_warn "Non-standard imports detected (verify Aristotle has these)"
    echo "$UNUSUAL_IMPORTS" | while read -r line; do
        echo "    $line"
    done
    echo ""
fi

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------
echo "========================================"
echo "Summary"
echo "========================================"

SORRY_COUNT=$(grep -c "sorry" "$LEAN_FILE" 2>/dev/null | head -1 || echo "0")
THEOREM_COUNT=$(grep -cE "^theorem |^lemma " "$LEAN_FILE" 2>/dev/null | head -1 || echo "0")

echo "Theorems/Lemmas: $THEOREM_COUNT"
echo "Sorries:         $SORRY_COUNT"
echo "Axioms:          $AXIOM_COUNT"
echo ""

if [ "$ISSUES" -gt 0 ]; then
    log_error "$ISSUES critical issues found - submission will likely fail"
    echo ""
    echo "Run with --fix for suggested solutions."
    exit 1
elif [ "$WARNINGS" -gt 0 ]; then
    log_warn "$WARNINGS warnings - submission may succeed but with limited results"
    echo ""
    log_ok "File can be submitted (with caveats)"
    exit 0
else
    log_ok "File appears compatible with Aristotle"
    exit 0
fi
