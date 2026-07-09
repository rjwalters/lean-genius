# Current State

**Phase**: SOLVED
**Since**: 2026-06-25T21:00:00.000Z
**Iteration**: 5

## Current Focus

Solved: formalized the implication "Sturm's exact-count theorem ⟹ Descartes' rule of signs" as a verified, axiom-free reduction, with an unconditional axiom-free validation on linear polynomials.

## Active Approach

Reduction skeleton over ℕ (`upper_bound_core`, `parity_core`, both omega-closed) deriving Descartes' upper bound and even-defect parity from a `SturmReduction` bridge structure (Sturm's variation drop on (0, B] plus three coefficient-comparison facts). The analytic content is isolated in the structure; the descent to Descartes is pure combinatorics. The Sturm half is discharged axiom-free on `X − c` (c > 0) by reusing the parent entry's axiom-free `sturm_linear_left`/`sturm_linear_right`.

## Result

`proofs/Proofs/DescartesRuleOfSignsOQ01OQ03.lean` — 14 theorems, 1 definition, 1 structure, 0 sorries, 0 `axiom` declarations. The general direction is conditional on the `SturmReduction` bridge data (counted as the entry's single standing assumption); the linear-polynomial validation is unconditional and axiom-free.

**Iteration 3 increment (2026-07-07):** made the linear branch *fully* unconditional. Previously `linearReduction`/`linear_descartes_bound` took `hV : signChangesInCoeffs (X − C c) = 1` as an unproved hypothesis. That coefficient count is now computed directly by a new axiom-free lemma `linear_signChanges`, built on a new general helper `countSignChanges_two` (a length-2 real sequence with opposite-sign entries has exactly one sign change — the base file had only ever *axiomatised* such concrete counts, e.g. `example_x2_minus_1_sign_changes`). So the `hV` hypothesis is discharged and the linear case carries no assumption beyond `c > 0`. Gallery entry: `descartes-rule-of-signs-oq-01-oq-03`.

A prerequisite Mathlib-rot repair was made to the base file `Proofs/DescartesRuleOfSigns.lean` (renamed `Polynomial.card_roots_le_degree` → `Polynomial.card_roots'`, fixed `Fin.castSucc_lt_succ` application, and supplied the explicit multiset argument to `Multiset.countP_le_card`) so the dependency chain compiles against Mathlib 4.26.0.

**Iteration 4 increment (2026-07-08):** carried out the iteration-3 "next intermediate step" — extended the axiom-free coefficient sign-change computation from `Fin 2` to the `Fin 3` middle-zero pattern. Two reusable lemmas, `countSignChanges_three_mid_zero_pos` (zero middle, opposite outer signs ⟹ one sign change, via the single pair `(0,2)`) and `countSignChanges_three_mid_zero_zero` (zero middle, non-opposite outer signs ⟹ no sign change, filter is empty), generalise `countSignChanges_two`. Using them, the base file's two *axiomatised* quadratic examples are now discharged **axiom-free** as theorems `x2_minus_1_signChanges : signChangesInCoeffs (X²−1) = 1` and `x2_plus_1_signChanges : signChangesInCoeffs (X²+1) = 0` (coefficient sequences `[1,0,−1]` and `[1,0,1]`; `natDegree = 2` via `compute_degree!`, coefficients via `simp [coeffSequence, coeff_sub/coeff_add, coeff_X_pow, coeff_one]`). This shows the base file's `example_x2_minus_1_sign_changes`/`example_x2_plus_1_sign_changes` axioms are removable. The entry stays `axiomatized` because the general-polynomial `SturmReduction` bridge remains a standing structural assumption.

**Iteration 5 increment (2026-07-08, researcher-7):** carried out the iteration-4
"further generalisation" — the **fully general `Fin 3` sign-change count with an
arbitrary NON-zero middle**, completing the length-3 (quadratic) theory. Four
axiom-free lemmas classify every sign pattern of a length-3 real sequence with
`f 1 ≠ 0`: `countSignChanges_three_alternating` (both adjacent pairs opposite ⟹
**2** — the maximal count, genuinely new since a zero middle can only give 0 or
1), `countSignChanges_three_mid_ne_left`/`_right` (exactly one adjacent pair
opposite ⟹ 1) and `countSignChanges_three_mid_ne_zero` (neither ⟹ 0). Together
with the `§ 2¾` middle-zero lemmas these give the complete count
`[f0·f1<0] + [f1·f2<0]` for **every** `Fin 3 → ℝ`, so all quadratics `aX²+bX+c`
(`b ≠ 0` included) are covered. Validated on `X²−X+1` (coefficient sequence
`[1,−1,1]`, pattern `+−+`) via the new axiom-free theorem
`x2_minus_x_plus_1_signChanges : signChangesInCoeffs = 2` — the first count-2
(Descartes-tight) evaluation. Docker VERIFIED
(`Proofs.DescartesRuleOfSignsOQ01OQ03`, 3064 jobs, EXIT 0, 0 sorry / 0 axiom /
no native_decide). leanFile 14→20 theorems, 386→554 lines.

## Blockers

None.

## Next Action

The `Fin 3` (quadratic) sign-change theory is COMPLETE. Remaining open directions
(unchanged): (a) prove the three comparison facts (B1)-(B3) for *general*
polynomials to make the general Sturm ⟹ Descartes implication unconditional;
(b) the mechanical step of replacing the base file's two quadratic `axiom`
declarations with theorems (proofs now exist here as `x2_minus_1_signChanges` /
`x2_plus_1_signChanges`; needs the `Fin 3` helpers relocated into the base file,
since it cannot import this descendant); (c) a general `Fin n` sign-change count
(the length-3 case is now a template — adjacent pairs jumping across zero blocks).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Session 2026-07-09 (researcher-8) — general Fin n same-sign ⇒ 0 sign changes

Generalized the small-case (`Fin 2`/`Fin 3`) sign-change lemmas to *arbitrary*
length `n` for the one implication that holds unconditionally: a same-signed
sequence has no sign change. Added 3 verified axiom-free theorems —
`countSignChanges_eq_zero_of_nonneg`, `countSignChanges_eq_zero_of_nonpos`
(general `Fin n`), and the polynomial corollary
`signChangesInCoeffs_eq_zero_of_coeff_nonneg` (a real polynomial with nonnegative
coefficients has no coefficient sign variation — the coefficient side of "nonneg
coefficients ⇒ no positive root"). leanFile 554→614 lines, 20→23 theorems,
0 sorry / 0 new axiom. docker-build VERIFIED (Proofs.DescartesRuleOfSignsOQ01OQ03,
3064 jobs, exit 0, Lean v4.26.0).
