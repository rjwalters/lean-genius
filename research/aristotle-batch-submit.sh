#!/bin/bash
#
# Aristotle Batch Submission - 2026-01-15
#
# Run this script to submit multiple files to Aristotle for overnight processing.
# Requires: ARISTOTLE_API_KEY environment variable
#
# Usage: ./research/aristotle-batch-submit.sh
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

echo "============================================"
echo "Aristotle Batch Submission - 2026-01-15"
echo "============================================"
echo ""

# Check API key
if [ -z "$ARISTOTLE_API_KEY" ]; then
    echo "ERROR: ARISTOTLE_API_KEY not set"
    echo "Set it with: export ARISTOTLE_API_KEY=your_key"
    exit 1
fi

# ============================================
# File 1: Erdos547Problem.lean (Tree Ramsey Numbers)
# ============================================
# Sorries: 3
#   - tree_ramsey_bound: Main theorem R(T) ≤ 2n-2 (HARD - Zhao et al. proved)
#   - chvatal_bound: R(T) ≤ (Δ-1)(n-1)+1 (HARD - Chvátal 1977)
#   - bound_is_tight: Stars achieve bound (HARD - standard result)
# Classification: All HARD - known proofs exist
# Expected success rate: Medium (depends on Ramsey infrastructure)
echo ""
echo "=== Submitting Erdos547Problem.lean ==="
echo "Sorries: tree_ramsey_bound, chvatal_bound, bound_is_tight"
echo "Classification: HARD (known proofs from Chvátal 1977, Zhao et al.)"
"$SCRIPT_DIR/scripts/aristotle-submit.sh" \
    proofs/Proofs/Erdos547Problem.lean \
    erdos-547 \
    "Tree Ramsey bounds - all HARD sorries with known proofs"

# ============================================
# File 2: Erdos21Problem.lean (Divisibility-free sets)
# ============================================
# Sorries: 3
#   - f_one: f(1) = 1 (TRIVIAL - base case)
#   - f_two: f(2) = 3 (HARD - specific computation)
#   - lower_bound_simplified: General lower bound (HARD)
# Classification: Mix of TRIVIAL and HARD
echo ""
echo "=== Submitting Erdos21Problem.lean ==="
echo "Sorries: f_one, f_two, lower_bound_simplified"
echo "Classification: TRIVIAL/HARD mix"
"$SCRIPT_DIR/scripts/aristotle-submit.sh" \
    proofs/Proofs/Erdos21Problem.lean \
    erdos-21 \
    "Divisibility-free sets - base cases and bounds"

# ============================================
# File 3: Erdos135Problem.lean (Distance sets in plane)
# ============================================
# Sorries: 6
#   - parallelogram_few_distances: Geometric lemma (HARD)
#   - trivial_distance_bound: Basic bound (HARD)
#   - Plus 4 more geometric/combinatorial lemmas
# Classification: All HARD - geometric proofs needed
echo ""
echo "=== Submitting Erdos135Problem.lean ==="
echo "Sorries: 6 geometric/combinatorial lemmas"
echo "Classification: HARD (geometric proofs)"
"$SCRIPT_DIR/scripts/aristotle-submit.sh" \
    proofs/Proofs/Erdos135Problem.lean \
    erdos-135 \
    "Distance sets - geometric lemmas"

echo ""
echo "============================================"
echo "Batch submission complete!"
echo ""
echo "Check status with:"
echo "  ./research/scripts/aristotle-status.sh"
echo ""
echo "Or check individual jobs:"
echo "  cat research/aristotle-jobs.json | jq '.jobs[-3:]'"
echo "============================================"
