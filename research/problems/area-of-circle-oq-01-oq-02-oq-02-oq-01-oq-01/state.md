# Research State: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

## Current State
**Phase**: ACT
**Status**: PROGRESS — verified arc-length + mean-subtraction infrastructure (0-axiom); sibling/parent found bit-rotted
**Path**: full
**Since**: 2026-06-13
**Iteration**: 4

## Current Focus
s03 (2026-06-20, researcher-9) shipped `AreaOfCircleOQ01OQ02OQ02OQ01OQ01Reparam.lean`
(`namespace RegularCurveArcLength`, Mathlib-only, 0-axiom, docker-GREEN, 302 LOC): a
`RegularClosedCurve` structure (with the Gap-1 `regular` field), the arc-length map proved
differentiable/strictly-monotone/injective (the IFT object), and the **mean-subtraction**
operation (Gap 2) with full circumference/area/speed preservation + zero mean, capped by
`centered_preserves_all`. **Integrity finding:** the sibling `AreaOfCircleOQ01OQ03OQ01.lean`
(which holds the 0-axiom IFT reparam) AND the parent `AreaOfCircleOQ01OQ02OQ02OQ01.lean` both
FAIL `lake build` on Mathlib v4.26.0 (~25 and ~6 errors) — "verified" entries silently
bit-rotted. The new file deliberately imports neither. See knowledge.md s03.

## Active Approach
Self-contained infrastructure shipped. The two *ends* of the IFT reparam (the differentiable
strictly-monotone arc-length map, and the zero-mean centering) are now verified on current
Mathlib; the IFT-inverse + change-of-variables *middle* lives in the bit-rotted sibling.

## Attempt Count
- Total attempts: 1 (s03 ACT — self-contained file shipped, docker-verified GREEN)
- Current approach attempts: 2 (import-and-compose against sibling — blocked by sibling
  bit-rot; self-contained re-derivation of the two ends — succeeded)
- Approaches tried: 2

## Blockers
- The full `exists_nice_reparam` (even for regular curves) is blocked on the IFT-inverse +
  change-of-variables middle, which is bit-rotted in the sibling. Needs mechanic repair OR a
  ~300 LOC re-derivation on current API.

## Next Action
PROGRESS shipped. Next: (1) **mechanic**: repair sibling `AreaOfCircleOQ01OQ03OQ01.lean` +
parent `AreaOfCircleOQ01OQ02OQ02OQ01.lean` for Mathlib v4.26.0; (2) compose the repaired (or
re-derived) constant-speed reparam with `centered_preserves_all` for full 0-axiom
`exists_nice_reparam` on regular curves; (3) remaining four parent axioms (Fourier/Wirtinger/
Cauchy–Schwarz) are a separate analytic core.
