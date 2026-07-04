# Research State: weak-goldbach-oq-01

## Current State
**Phase**: ACT (in progress)
**Path**: full
**Since**: 2026-07-03
**Iteration**: 4

## Current Focus
Discharging the `schnirelmann_basis_theorem` axiom in `WeakGoldbach.lean`. The
**covering** component and now the **entire iteration bookkeeping** are built and
verified in `proofs/Proofs/SchnirelmannBasis.lean` (0 sorry / 0 axiom). The
**sole** remaining ingredient is Schnirelmann's inequality itself.

## Active Approach
Schnirelmann's theorem, decomposed:
- [DONE] Covering lemma: σA+σB ≥ 1 ⟹ A⊕B ⊇ ℕ  (`sumset_covers_of_density_add_ge_one`).
- [DONE] Terminal + iteration bookkeeping (r8, iter 4): `IsSumOfAtMost` +
  composition (`.add`), the `h`-fold sum-set `sumsetPow`, and the reduction
  `isAdditiveBasis_of_sumsetPow_density_ge_half : σ(sumsetPow A h) ≥ ½ ⟹
  IsAdditiveBasis A (2h)`. Closes the "an element of h·A is a sum of ≤h elements
  of A" gap and the order-2h composition.
- [OPEN] Schnirelmann's inequality: σ(A⊕B) ≥ σA+σB−σA·σB — the gap-counting step.
  **Now the only missing piece**: iterating it drives some σ(sumsetPow A h) above
  ½, and the reduction above then discharges the axiom outright.

## Attempt Count
- Total attempts: 3 (1 survey, 2 act)
- Approaches tried: covering lemma (SUCCESS), iteration bookkeeping (SUCCESS),
  sumset inequality (not yet attempted — the sole remaining gap)

## Blockers
- Schnirelmann's inequality is the delicate gap-counting argument (Ruzsa,
  *Sumsets and structure*); an open Mathlib TODO. Non-trivial to formalize.
- Binary Goldbach itself remains genuinely open (must stay axiomatized).

## Next Action
Formalize Schnirelmann's inequality `σ(A⊕B) ≥ σA+σB−σA·σB` (with 0∈A, 0∈B), then
the iteration; this closes the chain to `schnirelmann_basis_theorem`. The covering
finisher is already in place in `SchnirelmannBasis.lean`.
