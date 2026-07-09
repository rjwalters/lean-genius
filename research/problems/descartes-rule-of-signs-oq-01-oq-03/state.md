# Current State

**Phase**: SOLVED
**Since**: 2026-06-25T21:00:00.000Z
**Iteration**: 4

## Current Focus

Solved: formalized the implication "Sturm's exact-count theorem ⟹ Descartes' rule of signs" as a verified, axiom-free reduction, with an unconditional axiom-free validation on linear polynomials.

## Active Approach

Reduction skeleton over ℕ (`upper_bound_core`, `parity_core`, both omega-closed) deriving Descartes' upper bound and even-defect parity from a `SturmReduction` bridge structure (Sturm's variation drop on (0, B] plus three coefficient-comparison facts). The analytic content is isolated in the structure; the descent to Descartes is pure combinatorics. The Sturm half is discharged axiom-free on `X − c` (c > 0) by reusing the parent entry's axiom-free `sturm_linear_left`/`sturm_linear_right`.

## Result

`proofs/Proofs/DescartesRuleOfSignsOQ01OQ03.lean` — 14 theorems, 1 definition, 1 structure, 0 sorries, 0 `axiom` declarations. The general direction is conditional on the `SturmReduction` bridge data (counted as the entry's single standing assumption); the linear-polynomial validation is unconditional and axiom-free.

**Iteration 3 increment (2026-07-07):** made the linear branch *fully* unconditional. Previously `linearReduction`/`linear_descartes_bound` took `hV : signChangesInCoeffs (X − C c) = 1` as an unproved hypothesis. That coefficient count is now computed directly by a new axiom-free lemma `linear_signChanges`, built on a new general helper `countSignChanges_two` (a length-2 real sequence with opposite-sign entries has exactly one sign change — the base file had only ever *axiomatised* such concrete counts, e.g. `example_x2_minus_1_sign_changes`). So the `hV` hypothesis is discharged and the linear case carries no assumption beyond `c > 0`. Gallery entry: `descartes-rule-of-signs-oq-01-oq-03`.

A prerequisite Mathlib-rot repair was made to the base file `Proofs/DescartesRuleOfSigns.lean` (renamed `Polynomial.card_roots_le_degree` → `Polynomial.card_roots'`, fixed `Fin.castSucc_lt_succ` application, and supplied the explicit multiset argument to `Multiset.countP_le_card`) so the dependency chain compiles against Mathlib 4.26.0.

**Iteration 4 increment (2026-07-08):** carried out the iteration-3 "next intermediate step" — extended the axiom-free coefficient sign-change computation from `Fin 2` to the `Fin 3` middle-zero pattern. Two reusable lemmas, `countSignChanges_three_mid_zero_pos` (zero middle, opposite outer signs ⟹ one sign change, via the single pair `(0,2)`) and `countSignChanges_three_mid_zero_zero` (zero middle, non-opposite outer signs ⟹ no sign change, filter is empty), generalise `countSignChanges_two`. Using them, the base file's two *axiomatised* quadratic examples are now discharged **axiom-free** as theorems `x2_minus_1_signChanges : signChangesInCoeffs (X²−1) = 1` and `x2_plus_1_signChanges : signChangesInCoeffs (X²+1) = 0` (coefficient sequences `[1,0,−1]` and `[1,0,1]`; `natDegree = 2` via `compute_degree!`, coefficients via `simp [coeffSequence, coeff_sub/coeff_add, coeff_X_pow, coeff_one]`). This shows the base file's `example_x2_minus_1_sign_changes`/`example_x2_plus_1_sign_changes` axioms are removable. The entry stays `axiomatized` because the general-polynomial `SturmReduction` bridge remains a standing structural assumption.

## Blockers

None.

## Next Action

Solved. The remaining open direction is unchanged: prove the three comparison facts (B1)-(B3) for *general* polynomials to make the general Sturm ⟹ Descartes implication unconditional. Follow-up mechanical step now enabled: replace the two `axiom` declarations in the base gallery file `Proofs/DescartesRuleOfSigns.lean` with theorems (the proofs now exist in this entry as `x2_minus_1_signChanges`/`x2_plus_1_signChanges`; a base-file edit would need the `Fin 3` helpers relocated into the base file, since it cannot import this descendant). A further generalisation is a fully general `Fin 3` sign-change count (arbitrary nonzero middle) to handle quadratics `aX²+bX+c` with `b ≠ 0`.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
