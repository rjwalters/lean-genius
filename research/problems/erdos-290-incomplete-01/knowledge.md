# Knowledge: erdos-290-incomplete-01

## Research Notes

Problem: Close 2 sorries in `proofs/Proofs/Erdos290Problem.lean`

## Session 2026-04-04 (Session 1) — Closed 2 Sorries

**Mode**: FRESH
**Outcome**: completed (0 sorries)

### What I Did

1. **Sorry 1** (`van_doorn_existence` in `bFunction`): The original `bFunction` used `Nat.find`
   with a `where` clause sorry: `∀ a, ∃ b, HasDenominatorDrop a b := by sorry`.
   - Fix: Moved `ErdosQuestion290` and `axiom van_doorn_main` to BEFORE `bFunction`,
     then replaced `Nat.find (van_doorn_existence a)` with
     `if h : a ≥ 1 then Classical.choose (van_doorn_main a h) else 0`.
   - `Nat.find` was replaced with `Classical.choose` because `harmonicDenom` is noncomputable,
     making `HasDenominatorDrop` not computably decidable (Lean can't synthesize `DecidablePred`).
     `Classical.choose` avoids this requirement.

2. **Sorry 2** (`b_of_3_bound`: harmonicDenom 3 6 < harmonicDenom 3 5): The proof needed
   to show the denominator drops from 60 to 20 at b=5 for the a=3 example.
   - Fix: Proved `partialHarmonic 3 5 = example_sum_3_to_5` and
     `partialHarmonic 3 6 = example_sum_3_to_6` by:
     a. Establishing `Finset.Icc 3 5 = {3,4,5}` via `decide`
     b. Expanding the sum with `Finset.sum_insert` + `Finset.sum_singleton`
     c. Using `norm_num` for the rational arithmetic
   - Then reused `example_denominator_drop` (already proved by `native_decide`).

3. **Import fix**: `Mathlib.Data.Rat.Basic` and `Mathlib.Algebra.BigOperators.Group.Finset`
   are not valid modules in Mathlib 4.26.0. Replaced with:
   - `Mathlib.Data.Rat.Defs` (for `ℚ`)
   - `Mathlib.Algebra.BigOperators.Ring.Finset` (for `∑`)
   - Added `Mathlib.Tactic`
   - Removed `Mathlib.Data.Nat.Basic` (subsumed by Tactic)

4. **Orphaned doc comments**: Lean 4 errors on `/-- ... -/` not followed by a definition.
   Changed orphaned doc comments to block comments `/-  ... -/`.

### Key Findings

- `partialHarmonic` is `noncomputable`, so `native_decide` cannot be used directly on it.
  The workaround is to connect it to computable definitions (`example_sum_3_to_5`) via rewrites.
- The Finset.Icc expansion approach (`decide` + `sum_insert` + `norm_num`) is the right
  pattern for proving equalities involving finite harmonic sums in Lean 4.
- `Classical.choose` (not `Nat.find`) is required when the predicate involves noncomputable types.

### Files Modified

- `proofs/Proofs/Erdos290Problem.lean`: 0 sorries (was 2), fixed imports, fixed doc comments
- `src/data/proofs/erdos-290/meta.json`: sorries: 2 → 0, updated module paths

### Axiom Count

2 axioms remain (unavoidable — van Doorn's 2024 paper result not yet formalized in Mathlib):
- `van_doorn_main`: ∀ a ≥ 1, ∃ b > a, denominatorDrop a b (the main existence theorem)
- `van_doorn_upper_bound`: ∀ a > 1, bFunction a < 4.374 * a (the quantitative bound)

### Next Steps

- Full formalization would require formalizing van Doorn's construction using powers of 3
- van Doorn's key lemma: if a ∈ (3^k, 3^{k+1}], then b = 2·3^{k+1} - 1 gives a denominator drop
- This requires LCM theory and analysis of 3-adic valuations of harmonic sums
