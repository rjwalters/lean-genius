# Research State: weak-goldbach-oq-01

## Current State
**Phase**: ACT (in progress)
**Path**: full
**Since**: 2026-07-03
**Iteration**: 3

## Current Focus
Discharging the `schnirelmann_basis_theorem` axiom in `WeakGoldbach.lean`. Split
into two components; the **covering** component is now built and verified in
`proofs/Proofs/SchnirelmannBasis.lean` (Schnirelmann's covering lemma + the
density-≥-½ basis-of-order-2 corollary, 0 sorry / 0 axiom).

## Active Approach
Schnirelmann's theorem, decomposed:
- [DONE] Covering lemma: σA+σB ≥ 1 ⟹ A⊕B ⊇ ℕ  (`sumset_covers_of_density_add_ge_one`).
- [OPEN] Schnirelmann's inequality: σ(A⊕B) ≥ σA+σB−σA·σB — the gap-counting step.
- [OPEN] Iteration 1−σ(h·A) ≤ (1−σA)^h to reach density > ½, then apply the
  order-2 corollary to `h·A` ⟹ basis of order 2h ⟹ discharge the axiom.

## Attempt Count
- Total attempts: 2 (1 survey, 1 act)
- Approaches tried: covering lemma (SUCCESS), sumset inequality (not yet attempted)

## Blockers
- Schnirelmann's inequality is the delicate gap-counting argument (Ruzsa,
  *Sumsets and structure*); an open Mathlib TODO. Non-trivial to formalize.
- Binary Goldbach itself remains genuinely open (must stay axiomatized).

## Next Action
Formalize Schnirelmann's inequality `σ(A⊕B) ≥ σA+σB−σA·σB` (with 0∈A, 0∈B), then
the iteration; this closes the chain to `schnirelmann_basis_theorem`. The covering
finisher is already in place in `SchnirelmannBasis.lean`.
