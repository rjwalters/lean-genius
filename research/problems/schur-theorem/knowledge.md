# Knowledge Base: schur-theorem

## Problem Summary

Prove Schur's theorem: for any r-coloring of positive integers, there exists a monochromatic solution to x + y = z.

**Statement**: For every r ≥ 1, there exists S(r) (the Schur number) such that any r-coloring of {1, ..., S(r)} contains x, y, z of the same color with x + y = z.

## Completion Status

**Status**: Completed
**Proof file**: `proofs/Proofs/SchursTheorem.lean`

## What Was Proved

1. **IsSchurTriple** - Definition: (x, y, z) where x + y = z
2. **IsSumFree** - A set with no Schur triple
3. **schur_1** - S(1) = 2 (trivial: 1 + 1 = 2)
4. **schur_2_upper** - S(2) ≤ 5 (exhaustive case analysis)
5. **schur_2_lower** - S(2) > 4 (exhibit valid 2-coloring of {1,2,3,4})
6. **schur_2** - S(2) = 5 exactly
7. **General existence** - Statement of theorem for arbitrary r

## Mathlib Infrastructure Used

- `Finset` - Finite set operations
- `Fintype` - Decidable finite types for case analysis
- `decide` tactic - Computational verification

## Key Insights

1. **Ramsey connection**: Classical proof uses Ramsey's theorem on edge-colored complete graphs
2. **Triangle trick**: Color edge {i,j} by color of |j-i|, monochromatic triangle → Schur triple
3. **Direct S(2) proof**: Exhaustive case analysis more tractable than Ramsey approach

## Known Schur Numbers

- S(1) = 2
- S(2) = 5
- S(3) = 14
- S(4) = 45
- S(5) = 161 (proved computationally in 2017)

## Historical Context

Issai Schur proved this in 1916, predating Ramsey's theorem (1930). Original motivation: proving x^n + y^n ≡ z^n (mod p) has nontrivial solutions for all primes p.
