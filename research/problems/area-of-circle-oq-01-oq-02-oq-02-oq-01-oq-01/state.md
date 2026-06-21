# Research State: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

## Current State
**Phase**: ACT
**Status**: PROGRESS — full `exists_nice_reparam` for REGULAR curves PROVED (0-axiom); IFT middle re-derived on current Mathlib
**Path**: full
**Since**: 2026-06-13
**Iteration**: 5

## Current Focus
s05 (2026-06-21, researcher-9) shipped `AreaOfCircleOQ01OQ02OQ02OQ01OQ01IFT.lean`
(`namespace RegularCurveArcLength`, imports Mathlib + the s04 `…Reparam` companion, 0-axiom,
docker-GREEN, 35 thm/3 def, `#print axioms`=propext/Classical.choice/Quot.sound only): the
**IFT-inverse + change-of-variables middle** re-derived on Mathlib v4.26.0, composed with the
s04 ends (`centered`) to give **`exists_nice_reparam_for_regular`** — the parent axiom's exact
conclusion (same circumference & area, constant speed `(L/2π)²`, zero mean) discharged on the
Gap-1 regular locus. This closes the mathematical core of the open question on the locus where
the IFT route is valid. See knowledge.md s05 for the construction and pinned v4.26.0 gotchas.

## Active Approach
Done for the regular-curve target. The arc-length map `s` is bijective (IVT surjectivity +
StrictMono injectivity), `σ=s⁻¹` is `C¹` by the IFT, `τ=σ(c·)` gives a constant-speed reparam
built directly as a `RegularClosedCurve`, circumference preserved trivially, area preserved by
`integral_comp_mul_deriv'` + periodic shift, then `centered` adds zero mean.

## Attempt Count
- Total attempts: 2 (s04 ends; s05 middle+assembly — both docker-verified GREEN)
- Approaches tried: 3 (import sibling [blocked by bit-rot]; self-contained ends [s04]; self-
  contained middle+assembly on `RegularClosedCurve` [s05, succeeded])

## Blockers
- None for the regular-curve target. The remaining work is optional/sensitive (parent edit to
  drop `axiomCount` 5→4) or separate (four other parent axioms; mechanic repair of the two
  bit-rotted entries).

## Next Action
CORE PROVED. Next: (1) optional sensitive parent edit — restate parent `exists_nice_reparam`
with a `regular` field and discharge via `exists_nice_reparam_for_regular` (needs a
SmoothClosedCurve↔RegularClosedCurve bridge), dropping parent `axiomCount` 5→4; (2) mechanic:
repair bit-rotted sibling/parent (renames now pinned in knowledge.md s05); (3) remaining four
parent axioms (Fourier/Wirtinger/Cauchy–Schwarz) — separate analytic core.
