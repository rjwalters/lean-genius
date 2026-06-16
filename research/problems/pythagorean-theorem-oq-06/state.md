# Current State

**Phase**: ACT
**Since**: 2026-06-16
**Iteration**: 1

## Current Focus

de Gua's theorem formalized in `proofs/Proofs/DeGuaTheorem.lean` (0 sorry / 0 axiom).
Build-verifying `Proofs.DeGuaTheorem`, then register + add gallery data.

## Active Approach

Cross-product / Binet–Cauchy reduction to a single polynomial identity, discharged
by `linear_combination` (coefficients numerically verified over 10⁵ samples).
Three theorems: `de_gua_core` (edge-vector), `de_gua` (vertex form), `de_gua_axis_aligned`.

## Blockers

None mathematically. Verification gated on Docker build completing (in progress).

## Next Action

Confirm green build → register in `Proofs.lean` → add gallery data → PR.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
