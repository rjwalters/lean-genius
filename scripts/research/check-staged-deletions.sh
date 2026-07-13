#!/bin/bash
#
# check-staged-deletions.sh - commit-time mass-deletion tripwire
#
# Guards against a repeat of the dc9fdffa30 incident (2026-07-11): a researcher
# worktree had been "slimmed" by deleting tracked files from disk WITHOUT git
# sparse-checkout, so git saw ~9,927 tracked files as locally deleted. A
# stage-everything commit (`git add -A`) for a single new Lean file silently
# staged all 9,927 deletions, the commit message mentioned only the Lean file,
# and the merge wiped the research corpus, the engine scripts, and every root
# config file from main. See issue #38398.
#
# Usage:
#   - As a `pre-commit` hook (parallel-research.sh installs it into every
#     researcher worktree it creates or reuses).
#   - Standalone, from anywhere inside a repo/worktree:
#       scripts/research/check-staged-deletions.sh [--max N]
#
# Behavior:
#   Exits 1 (blocking the commit when run as a hook) if the number of STAGED
#   deletions exceeds the threshold (default: 20).
#
# Overrides:
#   --max N                  Set the threshold for this invocation
#   MAX_STAGED_DELETIONS=N   Set the threshold via environment
#   ALLOW_MASS_DELETION=1    Bypass the tripwire entirely (for a genuinely
#                            intended, operator-acknowledged mass deletion)

set -euo pipefail

MAX="${MAX_STAGED_DELETIONS:-20}"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --max)
            if [[ -z "${2:-}" ]]; then
                echo "check-staged-deletions: --max requires a value" >&2
                exit 2
            fi
            MAX="$2"
            shift 2
            ;;
        --help|-h)
            sed -n '2,27p' "$0" | sed 's/^# \{0,1\}//'
            exit 0
            ;;
        *)
            echo "check-staged-deletions: unknown argument: $1 (see --help)" >&2
            exit 2
            ;;
    esac
done

if ! [[ "$MAX" =~ ^[0-9]+$ ]]; then
    echo "check-staged-deletions: threshold must be a non-negative integer (got: $MAX)" >&2
    exit 2
fi

if [[ "${ALLOW_MASS_DELETION:-}" == "1" ]]; then
    echo "check-staged-deletions: ALLOW_MASS_DELETION=1 — bypassing mass-deletion tripwire." >&2
    exit 0
fi

deleted_count=$(git diff --cached --diff-filter=D --name-only | wc -l | tr -d ' ')

if (( deleted_count > MAX )); then
    {
        echo ""
        echo "=============================================================================="
        echo "  COMMIT BLOCKED: $deleted_count staged deletions (threshold: $MAX)"
        echo "=============================================================================="
        echo ""
        echo "  You are about to commit the deletion of $deleted_count tracked files."
        echo ""
        echo "  This is exactly how commit dc9fdffa30 (2026-07-11, issue #38398) wiped"
        echo "  9,927 files from main: a worktree was 'slimmed' by deleting tracked files"
        echo "  from disk without git sparse-checkout, and a 'git add -A' for one new"
        echo "  Lean file silently staged every one of those deletions."
        echo ""
        echo "  First 10 staged deletions:"
        git diff --cached --diff-filter=D --name-only | head -10 | sed 's/^/    - /'
        echo ""
        echo "  If these deletions are UNINTENDED (phantom deletions from a slimmed or"
        echo "  damaged worktree):"
        echo "    1. Unstage them:      git restore --staged \$(git diff --cached --diff-filter=D --name-only)"
        echo "    2. Restore the files: git checkout -- ."
        echo "    3. Need disk space?   Use scripts/research/slim-worktree.sh (sparse-checkout),"
        echo "       NEVER raw 'rm' of tracked files."
        echo ""
        echo "  If this mass deletion is INTENDED (operator-acknowledged cleanup):"
        echo "    ALLOW_MASS_DELETION=1 git commit ..."
        echo "  or raise the threshold: MAX_STAGED_DELETIONS=N (env) / --max N (flag)."
        echo "=============================================================================="
    } >&2
    exit 1
fi

exit 0
