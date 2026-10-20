#!/usr/bin/env bash
#
# Build all Lean proofs EXCEPT memory-intensive or known-broken ones
#
# Some proofs (like Erdos728FactorialDivisibility) have tactics that can
# consume unbounded memory. Others are legacy files that are known not to
# compile and are pending a redesign rather than a repair. This script builds
# everything else.
#
set -euo pipefail

cd "$(dirname "$0")/.."

case "${1:-}" in
    ""|--list) ;;
    *) echo "Usage: $0 [--list]" >&2; exit 2 ;;
esac
(( $# <= 1 )) || { echo "Usage: $0 [--list]" >&2; exit 2; }

# Files to exclude:
#   - known memory hogs (unbounded-memory tactics)
#   - known-broken legacy files awaiting redesign (do NOT repair in place)
EXCLUDE=(
    "Erdos728FactorialDivisibility"   # memory hog
    # Kernel finite searches consumed 81 GiB in one compiler process and
    # triggered OOM in the 110 GiB cloud batch. Preserve the proof source;
    # restore this target after a bounded rebuild. See #43846 / #43756.
    "Erdos30WIP01"
    # Legacy oriented-adjacency file; the false `boundary_doors_odd` block does
    # not compile and is slated for replacement by the #8998 GridSimplex/gridAdj
    # redesign. Canonical foundation: Proofs.SpernerGridBase. See #38578 / #8998.
    "SpernerGrid"
    # Content-free placeholder whose only `import` is the broken SpernerGrid, so
    # it can never build while that file is quarantined. See #38578 / #8998.
    "SpernerGridAristotle"
    # Compute-pathology hang: one of its 34 `decide`/`native_decide` occurrences
    # does not terminate in any reasonable time (pegged one core at 99% CPU for
    # 10h+ during the 2026-09-25 full build, blocking every full build). Quarantine
    # until the hanging tactic is replaced with a bounded computation. See #43756.
    "BirthdayProblemOQ03OQ01OQ01"
    # Accidental import-all artifact, with no declarations: it imports the
    # quarantined Birthday, Erdos728 and SpernerGrid modules, bypassing the
    # exclusions above. Preserve its source but omit this aggregate (#43756).
    "AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle"
)

echo "Excluding: ${EXCLUDE[*]}" >&2

# One Lake invocation shares dependency work and preserves its failure status.
targets=()
for file in Proofs/*.lean; do
    name=${file##*/}
    name=${name%.lean}

    # Check if excluded
    skip=false
    for exc in "${EXCLUDE[@]}"; do
        if [[ "$name" == "$exc" ]]; then
            skip=true
            break
        fi
    done

    if $skip; then
        continue
    fi

    targets+=("Proofs.$name")
done

if [[ "${1:-}" == --list ]]; then
    printf '%s\n' "${targets[@]}"
    exit 0
fi
echo "Building ${#targets[@]} safe-subset targets" >&2
exec lake build "${targets[@]}"
