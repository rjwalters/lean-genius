# Research State: solution-of-cubic-oq-03-oq-03-oq-01

## Current State
**Phase**: ORIENT
**Path**: full
**Iteration**: 1

## Current Focus
Reframed the OQ. The "Ferrari factorization axioms" it names are ALREADY proven
theorems in `GeneralQuartic.lean` (lines 167/183/207/232/323). The file has
**3 axioms, 0 sorries**. The genuine residual is exactly:
- A1 `quartic_has_four_roots` (FTA root-set, line 268)
- A2 `biquadratic_forward` (quadratic formula, line 275)
- A3 `biquadratic_backward` (converse, line 283)

## Active Approach
Discharge A3 → A2 → A1. All bearers confirmed present at Mathlib v4.26.0:
`Complex.cpow_nat_inv_pow` (s²=p²−4r), `IsAlgClosed.splits`,
`Splits.eq_prod_roots_of_monic`, `Splits.natDegree_eq_card_roots`,
`Polynomial.mem_roots`. Math verified build-free via `verify_quartic_axioms.py`
(all assertions pass).

## Blockers
- Docker hangs this session → no Lean build, ACT deferred.
- Aristotle backend down ("Resource not found") → no async submit.

## Next Action
ACT (build-gated): write the 3 discharges (~150–200 LOC total). A3 easiest
(rewrite `s²`, `ring`); A2 via `(w−z₁)(w−z₂)` + `mul_eq_zero`; A1 via alg-closed
splitting + card-4 multiset enumeration. Then `meta.json` axiomCount 3 → 0.
