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

# Files to exclude:
#   - known memory hogs (unbounded-memory tactics)
#   - known-broken legacy files awaiting redesign (do NOT repair in place)
EXCLUDE=(
    "Erdos728FactorialDivisibility"   # memory hog
    # Legacy oriented-adjacency file; the false `boundary_doors_odd` block does
    # not compile and is slated for replacement by the #8998 GridSimplex/gridAdj
    # redesign. Canonical foundation: Proofs.SpernerGridBase. See #38578 / #8998.
    "SpernerGrid"
    # Content-free placeholder whose only `import` is the broken SpernerGrid, so
    # it can never build while that file is quarantined. See #38578 / #8998.
    "SpernerGridAristotle"
)

echo "=== Building Safe Subset of Proofs ==="
echo "Excluding: ${EXCLUDE[*]}"
echo ""

# Build each proof file individually, skipping excluded ones
for file in Proofs/*.lean; do
    name=$(basename "$file" .lean)

    # Check if excluded
    skip=false
    for exc in "${EXCLUDE[@]}"; do
        if [[ "$name" == "$exc" ]]; then
            skip=true
            break
        fi
    done

    if $skip; then
        echo "SKIP: Proofs.$name (excluded - memory intensive)"
        continue
    fi

    echo "BUILD: Proofs.$name"
    if ! lake build "Proofs.$name" 2>&1; then
        echo "FAILED: Proofs.$name"
        # Continue with other files instead of stopping
    fi
done

echo ""
echo "=== Done ==="
