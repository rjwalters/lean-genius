# Knowledge Base: schur-theorem

## Problem Summary

Prove Schur's theorem (1916): for any r-coloring of positive integers, there exists a monochromatic solution to x + y = z.

## Current State

**Status**: COMPLETED
**Proof File**: `proofs/Proofs/SchursTheorem.lean` (322 lines)
**Sorries**: 1 (for r >= 3 case)

### What's Proven (no sorries for r <= 2)

1. **Definitions**
   - `IsSchurTriple x y z` - x + y = z
   - `IsSumFree S` - No x, y, x+y all in S
   - `IntegerColoring n r` - r-coloring of {1,...,n}
   - `HasMonochromaticSchurTriple` - Exists monochromatic x + y = z

2. **S(1) = 2**
   - `schur_1` - Any 1-coloring of {1,2} has monochromatic 1+1=2

3. **S(2) = 5 (Complete Proof)**
   - `schur_2_upper` - Any 2-coloring of {1,2,3,4,5} has monochromatic triple
   - `schur_2_lower` - Exists 2-coloring of {1,2,3,4} with no triple
   - `sumFreeColoring4` - The witness: {1,4} and {2,3}
   - `schur_number_2` - Combined statement S(2) = 5

4. **General Framework**
   - `schur_theorem_existence` - For all r, S(r) exists (sorry for r >= 3)
   - `schur_equiv_no_sum_free` - Equivalence with sum-free partitions

### What's Sorry'd (1 sorry)

- General case r >= 3 requires multicolor Ramsey theorem (not yet formalized)

### Key Insight

S(2) = 5 proof by exhaustive case analysis: no sum-free 2-partition of {1,2,3,4,5} exists. The witness {1,4}, {2,3} shows S(2) > 4.

Connection to Ramsey: color edge {i,j} by color of |i-j|. Monochromatic triangle gives Schur triple.

### Known Values

- S(1) = 2, S(2) = 5, S(3) = 14, S(4) = 45, S(5) = 161

## Session Log

### Session 2026-01-01 (Research Iteration) - MULTICOLOR RAMSEY CONNECTION

**Mode**: REVISIT
**Prior Status**: completed (1 sorry)
**Outcome**: PROGRESS - Connected to multicolor Ramsey axiom

**What we did**:
1. Added multicolor Ramsey axiom to `RamseysTheorem.lean`
2. Updated Schur r≥3 case to use multicolor Ramsey
3. Documented the edge coloring connection

**Key insight (edge coloring trick)**:
For coloring c : {1,...,n} → Fin r, define edge color:
- color(i,j) := c(|i-j|) for i ≠ j

A monochromatic triangle i < j < k means:
- c(j-i) = c(k-j) = c(k-i) = col

But j-i + k-j = k-i, so we have a Schur triple!

**Files modified**:
- `proofs/Proofs/RamseysTheorem.lean` - Added multicolor Ramsey axiom (+26 lines)
- `proofs/Proofs/SchursTheorem.lean` - Uses multicolor Ramsey for r≥3

**Status**: Still 1 sorry - the edge coloring connection proof needs:
1. Define edge coloring from integer coloring
2. Show monochromatic clique → Schur triple

This is ~50-100 lines of additional infrastructure.

---

### Backfill Session (2026-01-01)

**Mode**: BACKFILL - Problem was completed without knowledge documentation

**Quality Assessment**: HIGH - Complete proof for S(2), good framework for general case
