# Current State

**Phase**: SOLVED
**Since**: 2026-06-25T21:00:00.000Z
**Iteration**: 3

## Current Focus

Solved: formalized the implication "Sturm's exact-count theorem ⟹ Descartes' rule of signs" as a verified, axiom-free reduction, with an unconditional axiom-free validation on linear polynomials.

## Active Approach

Reduction skeleton over ℕ (`upper_bound_core`, `parity_core`, both omega-closed) deriving Descartes' upper bound and even-defect parity from a `SturmReduction` bridge structure (Sturm's variation drop on (0, B] plus three coefficient-comparison facts). The analytic content is isolated in the structure; the descent to Descartes is pure combinatorics. The Sturm half is discharged axiom-free on `X − c` (c > 0) by reusing the parent entry's axiom-free `sturm_linear_left`/`sturm_linear_right`.

## Result

`proofs/Proofs/DescartesRuleOfSignsOQ01OQ03.lean` — 10 theorems, 1 definition, 1 structure, 0 sorries, 0 `axiom` declarations. The general direction is conditional on the `SturmReduction` bridge data (counted as the entry's single standing assumption); the linear-polynomial validation is unconditional and axiom-free.

**Iteration 3 increment (2026-07-07):** made the linear branch *fully* unconditional. Previously `linearReduction`/`linear_descartes_bound` took `hV : signChangesInCoeffs (X − C c) = 1` as an unproved hypothesis. That coefficient count is now computed directly by a new axiom-free lemma `linear_signChanges`, built on a new general helper `countSignChanges_two` (a length-2 real sequence with opposite-sign entries has exactly one sign change — the base file had only ever *axiomatised* such concrete counts, e.g. `example_x2_minus_1_sign_changes`). So the `hV` hypothesis is discharged and the linear case carries no assumption beyond `c > 0`. Gallery entry: `descartes-rule-of-signs-oq-01-oq-03`.

A prerequisite Mathlib-rot repair was made to the base file `Proofs/DescartesRuleOfSigns.lean` (renamed `Polynomial.card_roots_le_degree` → `Polynomial.card_roots'`, fixed `Fin.castSucc_lt_succ` application, and supplied the explicit multiset argument to `Multiset.countP_le_card`) so the dependency chain compiles against Mathlib 4.26.0.

## Blockers

None.

## Next Action

Solved. Remaining open question: prove the three comparison facts (B1)-(B3) for *general* polynomials to make the general Sturm ⟹ Descartes implication unconditional. (For linear polynomials this is now done — the (B1)-(B3) facts are discharged axiom-free via `linear_signChanges`/`countSignChanges_two`.) A natural next intermediate step is extending the axiom-free coefficient sign-change computation from `Fin 2` to `Fin 3` (quadratics), which would let the base file's axiomatised examples `example_x2_minus_1_sign_changes`/`example_x2_plus_1_sign_changes` be de-axiomatised.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
