# Erdos Problem #1005: Farey Fractions and Similar Ordering

## Problem Summary

Let a1/b1, a2/b2, ... be the Farey fractions of order n >= 4.
Let f(n) be the largest integer such that if 1 <= k < l <= k + f(n)
then a_k/b_k and a_l/b_l are "similarly ordered": (a_k - a_l)(b_k - b_l) >= 0.

**Question**: Estimate f(n). Is there a constant c > 0 such that f(n) = (c + o(1))n?

**Status**: OPEN

**Known bounds**: (1/12 - o(1))n <= f(n) <= n/4 + O(1) (van Doorn 2025)

## Session 2026-01-18 (Session 1) - Infrastructure Fixes and Theorem Proofs

**Mode**: REVISIT (pool empty)
**Outcome**: progress

### What I Did

1. Fixed Mathlib4 compatibility issues:
   - Changed `import Mathlib.Data.Rat.Basic` to `import Mathlib.Data.Rat.Defs` (old import path removed)
   - Added `import Mathlib.Tactic` for `field_simp` and `ring` tactics
   - Changed `List.get?` to bracket notation `[i]?` (Lean 4 syntax)
   - Added explicit type annotations to `farey_adjacent_property` axiom
   - Rewrote `mayerErdosF` definition using `sSup` instead of `Nat.find` (avoiding decidability issues)

2. Fixed proof tactics:
   - `bounds_ratio`: Changed `norm_num` to `field_simp; ring`
   - `gap_significance`: Changed `norm_num` to `field_simp; ring`
   - `similarlyOrdered_iff_monotone`: Fixed intermediate lemma construction for `Int.le_of_sub_nonneg`

3. Verified existing proofs compile:
   - `similarlyOrdered_symm`: Symmetry of similarly ordered relation
   - `similarlyOrdered_refl`: Reflexivity of similarly ordered relation
   - `similarlyOrdered_iff_monotone`: Equivalence with monotone coordinate ordering
   - `bounds_ratio`: The ratio 1/4 / (1/12) = 3
   - `gap_significance`: The gap 1/4 - 1/12 = 1/6
   - `vanDoorn_bounds`: Combines lower and upper bound axioms

### Key Findings

- File had 6+ build errors due to Mathlib4 API changes
- `Mathlib.Data.Rat.Basic` no longer exists - split into `Mathlib.Data.Rat.Defs` etc.
- `List.get?` syntax changed to bracket notation in Lean 4
- `norm_num` cannot handle division of reals directly; need `field_simp` first
- All theorem sorries in this file are actually provable from axioms or by tactics

### Remaining Sorries

Only 2 sorries remain - both are definition sorries (not theorem sorries):
- `fareySequence`: Construction of Farey sequence as a Finset
- `fareyList`: Construction of Farey sequence as an ordered List

These are data construction sorries, not provable theorems. The actual mathematical content (the OPEN question about asymptotic behavior) is correctly marked as axioms.

### Files Modified

- `proofs/Proofs/Erdos1005Problem.lean`

### Next Steps

- The file is now Mathlib4-compatible and builds successfully
- The OPEN question `hasAsymptoticConstant` cannot be proved (it's an unsolved problem)
- Could potentially submit to Aristotle to fill in any remaining trivial sorries, but the two definition sorries require actual Farey sequence construction
