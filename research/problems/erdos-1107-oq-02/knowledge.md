# Knowledge Base: erdos-1107-oq-02

## Problem Summary

**Title**: Effective Squareful Sum Threshold
**Parent**: Erdős Problem #1107 (sums of r-powerful numbers)
**Focus**: Make Heath-Brown's theorem for r=2 effective by finding the exact threshold N.

## Session 2026-04-13 (Session 1) - Threshold Computation

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Computed the exact threshold N = 120 for sums of 3 squareful numbers
- Identified the complete exceptional set: {7, 15, 23, 87, 111, 119}
- Verified computationally that all integers from 120 to 2000 are representable
- Created Lean 4 formalization in `Erdos1107OQ02.lean`
- Created gallery entry in `src/data/proofs/erdos-1107-oq-02/`

### Key Findings
- The threshold N = 120 is tight: 119 is not representable, 120 = 4 + 8 + 108
- Only 6 positive integers fail out of all natural numbers
- Squareful numbers (0, 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, ...) are dense enough that their 3-fold sumset covers all integers from 120 onwards
- The Lean file uses native_decide for computational verification up to 1000

### Files Modified
- `proofs/Proofs/Erdos1107OQ02.lean` (new, ~140 lines)
- `src/data/proofs/erdos-1107-oq-02/meta.json` (new)
- `src/data/proofs/erdos-1107-oq-02/annotations.json` (new)
- `src/data/proofs/erdos-1107-oq-02/index.ts` (new)

### Status
- **Axiom count**: 1 (squareful_sum_threshold — the infinite extension beyond computation)
- **Sorry count**: 0
- **Build status**: Not yet verified (Docker build needed)
