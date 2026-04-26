# angle-trisection-oq-02-oq-01-oq-02-incomplete-01

**Problem**: Complete proof of Wantzel-Galois Constructibility from Mathlib Galois Theory

## Problem Summary

This problem asks to complete the formal proof that angle trisection, cube doubling, and
regular 7-gon construction are impossible using straightedge and compass alone. The key
mathematical content is the Wantzel-Galois theorem: an algebraic number α is constructible
iff the Galois group of its minimal polynomial is a 2-group.

The parent file `AngleTrisectionOQ02OQ01OQ02.lean` had multiple sorries. Previous sessions
improved it to the `Incomplete01` variant with 1 sorry, but that sorry was **FALSE** under
the IsConstructible definition used.

## Critical Issue: Broken IsConstructible Definition

The original `IsConstructible` definition had `sqrt_ext` requiring `IsConstructible β`:

```lean
| sqrt_ext : ∀ (β a b : ℂ),
    IsConstructible β → IsConstructible a → IsConstructible b →
    β * β = a → IsConstructible (b + β)
```

**Problem**: This is circular — β must already be constructible to be added via sqrt_ext.
Result: the only constructible numbers are the rationals (proved by `isConstructible_mem_range`).
Consequence: `wantzel_galois_iff` (α constructible ↔ Gal(minpoly) is 2-group) is **FALSE**
because √2 has a 2-group Galois group but is not rational, hence "not constructible."

## Session 26 Fix: IsConstructible Definition Corrected

Removed `IsConstructible β` precondition from `sqrt_ext`:

```lean
| sqrt_ext : ∀ (β a b : ℂ),
    IsConstructible a → IsConstructible b →
    β * β = a → IsConstructible (b + β)  -- β is any sqrt of constructible a
```

Now:
- √2 IS constructible: take a=2 (rational), b=0, β=√2, β²=2 ✓
- `isConstructible_sqrt2` proved (demo that the definition works)
- `wantzel_galois_iff` is now a TRUE statement

## Remaining Sorries (2, both TRUE)

1. **`isConstructible_algebraic_degree`**: IsConstructible α → IsAlgebraic ℚ α ∧ ∃ n, finrank ℚ ℚ⟮α⟯ = 2^n
   - Proof: induction on IsConstructible
   - rational case: minpoly = X - C q, finrank = 1 = 2^0 ✓
   - sqrt_ext case: β² = a. [ℚ(a,β):ℚ(a)] ≤ 2 (β satisfies X²-a). Tower: [ℚ(b+β):ℚ] ≤ 2^(j+k+1)
   - Needs: `FiniteDimensional.finrank_mul_finrank`, `IntermediateField.adjoin.finrank`
   - Estimated: ~120 lines

2. **`wantzel_galois_iff`**: α constructible ↔ IsTwoGroup Gal(minpoly)
   - Requires full FTGT + 2-group tower characterization
   - Estimated: 500+ lines. Marked as out-of-scope.

## Key Lean Techniques Discovered

- `IntermediateField.adjoin.finrank (halg : IsAlgebraic ℚ α)` gives finrank ℚ ℚ⟮α⟯ = (minpoly ℚ α).natDegree
- `minpoly.dvd ℚ α (h : aeval α p = 0)` gives minpoly ℚ α ∣ p
- `minpoly.ne_zero (halg : IsAlgebraic ℚ α)` gives minpoly ℚ α ≠ 0
- `Polynomial.natDegree_eq_zero_of_isUnit` for unit polynomials

## Session 26 (2026-04-26) — IsConstructible Definition Fix

**Mode**: FRESH (claimed from pool)
**Outcome**: PROGRESS — converted 1 FALSE sorry to 2 TRUE sorries; fixed fundamental definition bug

### What I Did
- Diagnosed the broken `IsConstructible` definition (all constructible = rationals was wrong)
- Removed `IsConstructible β` from `sqrt_ext` constructor (the key fix)
- Proved `isConstructible_sqrt2` (√2 IS constructible under fixed definition)
- Added `isConstructible_algebraic_degree` sorry with detailed proof sketch
- Rewrote `not_constructible_of_bad_degree` to use the new sorry (degree tower approach)
- Updated `wantzel_galois_iff` comment noting it's now TRUE (not false as before)

### Key Insights
- The "trick" in the old proof (constructible → rational → minpoly degree = 1 = 2^0) worked
  correctly but for the WRONG reason — it proved too much (everything non-rational non-constructible)
- The correct proof uses the actual tower argument: constructible → finrank is power of 2
- `IntermediateField.adjoin.finrank` is the key Mathlib lemma connecting finrank to minpoly degree

### Files Modified
- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean` — definition fix + 2 sorries
- `src/data/research/problems/angle-trisection-oq-02-oq-01-oq-02-incomplete-01.json` — knowledge update

### Next Steps
1. Prove `isConstructible_algebraic_degree`: ~120 lines, tower induction
2. For `wantzel_galois_iff`: would need FTGT, keep as sorry
3. Consider Aristotle for helper lemmas in the tower induction
