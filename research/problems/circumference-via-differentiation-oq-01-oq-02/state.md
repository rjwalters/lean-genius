# Research State: circumference-via-differentiation-oq-01-oq-02

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-15
**Iteration**: 2
**Last Updated**: 2026-06-15 (researcher-9)

## Current Focus
L^p unit ball volume / surface-derivative identity. ANSWERED: the volume formula
`V_n(p) = 2^n Γ(1/p+1)^n / Γ(n/p+1)` and the scaling `Vol{‖x‖_p≤r}=V_n(p)·r^n`
give `dV/dr = n·V_n(p)·r^(n-1)`. This equals the Euclidean Hausdorff surface
measure ONLY for p=2 (and a.e. for p=∞); for finite p≠2 it equals the
coarea-weighted surface `∫ 1/|∇‖·‖_p| dℋ^{n-1}`, NOT the Euclidean perimeter.

## Active Approach
Build-free ORIENT (Docker + Aristotle both down). Independent numeric verifier
`verify_lp_ball.py` (ALL PASS). Discovered Mathlib already proves the volume
(`MeasureTheory.volume_sum_rpow_le`); authored a build-pending UNREGISTERED Lean
file with the derivative half proven and the Mathlib-aligned defs.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Lean ACT is Docker-gated (no build this session); file left UNREGISTERED.
- **Surface side blocked on Mathlib**: v4.26 has no coarea formula (only
  `Hausdorff.lean`), so the always-true weighted surface identity cannot yet be
  stated faithfully in Lean.

## Next Action
When Docker returns: build `CircumferenceViaDifferentiationOQ01OQ02.lean`, add a
`volume = ENNReal.ofReal (lpBallVolumeFn n p r)` bridge via `rw
[volume_sum_rpow_le]`, register in `Proofs/Proofs.lean`. The surface-equality
half stays blocked pending an upstream coarea formula.

## Iteration log
* **S1** (2026-06-15, OBSERVE): stub created.
* **S2** (2026-06-15, researcher-9, ORIENT): sharp answer (coarea distinction) +
  all-pass verifier; found Mathlib's `volume_sum_rpow_le`; build-pending Lean
  file with the derivative theorem proven.
