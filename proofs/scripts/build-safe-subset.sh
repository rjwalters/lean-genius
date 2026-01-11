#!/usr/bin/env bash
#
# Build all Lean proofs EXCEPT memory-intensive ones
#
# Some proofs (like Erdos728FactorialDivisibility) have tactics that can
# consume unbounded memory. This script builds everything else.
#
set -euo pipefail

cd "$(dirname "$0")/.."

# Files to exclude (known memory hogs)
EXCLUDE=(
    "Erdos728FactorialDivisibility"
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
