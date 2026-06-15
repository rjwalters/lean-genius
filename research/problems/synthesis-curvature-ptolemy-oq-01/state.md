# Research State: synthesis-curvature-ptolemy-oq-01

## Current State
**Phase**: COMPLETED
**Path**: fast
**Since**: 2026-06-15
**Iteration**: 2

## Current Focus
RESOLVED. The open question — prove `curvatureSin K` satisfies the ODE `y'' + K·y = 0` —
is fully proved in `proofs/Proofs/SynthesisCurvaturePtolemyOQ01.lean`
(`curvatureSin_satisfies_ode` + `curvatureSin_initial_conditions`, all three curvature
regimes), merged in PR #24239 and registered in `proofs/Proofs.lean`. The file is
sorry-free and axiom-free.

## Active Approach
None — work complete.

## Attempt Count
- Total attempts: 1 (ACT, PR #24239)
- Approaches tried: 1 (HasDerivAt chain + second-derivative `-K·curvatureSin`, all regimes)

## Blockers
None for the OQ itself. Full local `docker-build` re-confirmation is pending the
2026-06-15 Docker blackout, but the file is in the build aggregator and the proofs are
elementary (`rw`/`ring`/`.deriv` on parent lemmas).

## Next Action
Closed. Optional future work (new slug): IVP uniqueness — any `y` with `y''+K·y=0`,
`y(0)=0`, `y'(0)=1` equals `curvatureSin K` (via Mathlib ODE uniqueness).
