#!/usr/bin/env bash
#
# check-superseded.sh - Detect whether a branch's new proof files already exist on main.
#
# The pipeline runs many research agents concurrently. When two agents work the
# same problem (e.g. a claim expires mid-session and a second agent re-claims it),
# both create a proof file at the SAME path. Whoever merges first wins; the loser
# becomes an unmergeable add/add duplicate that rots as a DIRTY PR. This is the
# "wasted effort" backlog.
#
# A branch is SUPERSEDED when, for every proofs/Proofs/*.lean file it ADDS
# (absent at the branch's merge-base with main), that same path already exists on
# origin/main. That is an add/add collision against an already-formalized result.
#
# Consumers:
#   - Researcher role (fix B): run before `gh pr create`; abort if superseded.
#   - Deployer (fix A):        run over CONFLICTING PRs; close superseded ones
#                              instead of burning cycles on an impossible rebase.
#
# Usage:
#   check-superseded.sh [--ref <ref>] [--base <base-ref>] [--quiet]
#
#   --ref   Commit/branch to inspect      (default: HEAD)
#   --base  Up-to-date main to compare to (default: origin/main)
#   --quiet Suppress the human-readable verdict line
#
# Exit codes:
#   0  NOT_SUPERSEDED — the branch adds at least one genuinely new proof file
#   3  SUPERSEDED     — every added proof file already exists on main
#   1  usage / git error
#
# Note: prints the verdict word (NOT_SUPERSEDED / SUPERSEDED / NO_PROOF_FILES) to
# stdout so callers can branch on text as well as exit code.

set -euo pipefail

REF="HEAD"
BASE="origin/main"
QUIET=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --ref)   REF="$2"; shift 2 ;;
        --base)  BASE="$2"; shift 2 ;;
        --quiet) QUIET=true; shift ;;
        -h|--help) grep '^#' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
        *) echo "Unknown argument: $1" >&2; exit 1 ;;
    esac
done

say() { $QUIET || echo "$@"; }

# Resolve the merge-base so we can tell "added on this branch" from "modified".
base_commit=$(git merge-base "$BASE" "$REF" 2>/dev/null) || {
    echo "check-superseded: cannot find merge-base of $BASE and $REF" >&2
    exit 1
}

# Proof files this branch touched relative to the merge-base.
# (read loop rather than mapfile: macOS ships bash 3.2, which lacks mapfile)
touched=()
while IFS= read -r line; do
    [[ -n "$line" ]] && touched+=("$line")
done < <(git diff --name-only "$base_commit" "$REF" -- 'proofs/Proofs/*.lean' 2>/dev/null || true)

if [[ ${#touched[@]} -eq 0 ]]; then
    say "NO_PROOF_FILES"
    echo "NO_PROOF_FILES"
    exit 0   # nothing to guard; treat as safe to proceed
fi

added_total=0
added_superseded=0
declare -a collisions=()

for f in "${touched[@]}"; do
    [[ -z "$f" ]] && continue
    # "Added on this branch" = absent at merge-base.
    if git cat-file -e "${base_commit}:${f}" 2>/dev/null; then
        continue   # existed at base -> a modification, not an add/add candidate
    fi
    added_total=$((added_total + 1))
    # Does main already carry this exact path (added independently)?
    if git cat-file -e "${BASE}:${f}" 2>/dev/null; then
        added_superseded=$((added_superseded + 1))
        collisions+=("$f")
    fi
done

if [[ $added_total -eq 0 ]]; then
    # Branch only modifies existing files -> a legitimate follow-up, never reap.
    say "NOT_SUPERSEDED (modifies existing files only)"
    echo "NOT_SUPERSEDED"
    exit 0
fi

if [[ $added_superseded -eq $added_total ]]; then
    say "SUPERSEDED — all $added_total added proof file(s) already exist on ${BASE}:"
    for c in "${collisions[@]}"; do say "    $c"; done
    echo "SUPERSEDED"
    exit 3
fi

say "NOT_SUPERSEDED ($added_superseded/$added_total added proof files collide; $((added_total - added_superseded)) genuinely new)"
echo "NOT_SUPERSEDED"
exit 0
