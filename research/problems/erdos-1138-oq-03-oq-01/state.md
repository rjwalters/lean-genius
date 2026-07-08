# Research State: erdos-1138-oq-03-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-07-05
**Iteration**: 2

## Completion
VERIFIED and merged in PR #35062: `proofs/Proofs/Erdos1138OQ03OQ01.lean`, 0 sorries,
0 local axioms, 3 theorems, 1 inherited axiom (`Erdos1138OQ03.baker_harman_pintz`).
The build-blocked survey note below is superseded. Do not re-serve.

## Current Focus
Scoped a tractable oq-01 for the fresh (previously EMPTY, no problem.md) candidate:
BHP axiom ⟹ `maxPrimeGap x / x → 0` (unconditional prime-gap sublinearity), the twin of
the parent's conditional `cramer_implies_gap_sublinear`.

## Active Approach
Real-analysis squeeze: `maxPrimeGap x / x ≤ x^(-0.475) → 0`. Envelope limit from
`Real.tendsto_rpow_neg_atTop` ∘ `tendsto_natCast_atTop_atTop`; squeeze via `squeeze_zero`.
Both Mathlib lemmas statically verified present. Full sketch in knowledge.md.

## Attempt Count
- Total attempts: 1 (survey only)
- Approaches tried: 1 (squeeze-to-zero from the BHP exponent 0.525 < 1)

## Blockers
Build-blocked this session (Docker down; disk ~97%; 0 oleans on disk, #33336). No Lean
compiled — per honesty/axiom-integrity policy, no unverifiable proof was written. The
sketch is analysis-standard and Mathlib-reachable but MUST be built before any "verified"
claim.

## Next Action
Build-capable session: create `proofs/Proofs/Erdos1138OQ03OQ01.lean` (import
`Proofs.Erdos1138OQ03`) with `bhp_implies_gap_littleo` (+ optional ε-form), build via
docker-build.sh, then add gallery entry `src/data/proofs/erdos-1138-oq-03-oq-01/` with
status `axiomatized` (inherits the `baker_harman_pintz` axiom).
