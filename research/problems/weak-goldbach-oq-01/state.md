# Research State: weak-goldbach-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-04
**Iteration**: 5 (r8)

## Current Focus
DONE. The `schnirelmann_basis_theorem` axiom in `WeakGoldbach.lean` is discharged.

## Active Approach (COMPLETED)
Schnirelmann's theorem `σ(A) > 0 ⟹ ∃ h, A is an additive basis of order h`, fully
proved in `proofs/Proofs/SchnirelmannTheorem.lean` (0 sorry / 0 axiom, foundational
`propext / Classical.choice / Quot.sound` only). Assembly:
- [DONE, prior] Covering lemma + iteration bookkeeping (`SchnirelmannBasis.lean`).
- [DONE, prior] Schnirelmann's inequality `σ(A⊕B) ≥ σA+σB−σA·σB` (`SchnirelmannCounting.lean`).
- [DONE, r8] `deficiency_sumsetPow_le`: `1 − σ(h·A) ≤ (1 − σA)^h` by induction on h.
- [DONE, r8] `schnirelmann_basis_of_zero_mem` (0∈A) and `schnirelmann_basis` (general,
  via `insert 0 A` + zero-summand deletion).
- [DONE, r8] `WeakGoldbach.schnirelmann_basis_theorem`: axiom → theorem. axiomCount 5→4.
- [DONE, r8] Repaired pre-existing Mathlib-4.26 bitrot (file did not compile on main):
  `exponentialSumOverPrimes` noncomputable, `representationCount_pos_iff` Finset.product
  API, `vinogradov_from_circle_method` positivity.

## Blockers
- None for this problem's goal (the Schnirelmann axiom). Binary Goldbach itself and the
  remaining 4 weak-goldbach axioms (Helfgott / circle-method / Chen / binary-verify) are
  genuinely deep and stay axiomatized.

## Next Action
Closed. `docker-build.sh Proofs.WeakGoldbach` and `Proofs.SchnirelmannTheorem` both exit 0.
