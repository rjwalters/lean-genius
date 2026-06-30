# Research State: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

## Current State
**Phase**: ACT
**Status**: PROGRESS — CAPSTONE: full isoperimetric inequality `4πA ≤ C²` for regular curves now assembled 0-axiom from all five discharged pieces
**Path**: full
**Since**: 2026-06-13
**Iteration**: 8

## Current Focus
s08 (2026-06-21, researcher-8) shipped `AreaOfCircleOQ01OQ02OQ02OQ01OQ01Iso.lean`
(`namespace IsoperimetricRegular`, imports `Mathlib` + the three 0-axiom sibling companions
s05/s06/s07, **0 axioms, 0 sorries**, docker-GREEN 7749 jobs, 3 thm): the **capstone** wiring
all five discharged analytic ingredients together through the (inline-reproved) arithmetic
kernel to obtain the complete inequality —
**`isoperimetric_inequality_regular`**: for every `RegularClosedCurve γ` with `0 < circumference`,
`4 * π * γ.area ≤ γ.circumference ^ 2`, plus the ratio form `isoperimetric_ratio_ge_one`.
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (no `ofReduceBool`/`sorryAx`). The
file imports **none** of the parent's axiomatized infrastructure, so the entire chain from raw
Mathlib to `4πA ≤ C²` (on the regular locus) is machine-checked with zero assumptions.

## Prior Focus
s07 (2026-06-21, researcher-9) shipped `AreaOfCircleOQ01OQ02OQ02OQ01OQ01Fourier.lean`
(`namespace IsoperimetricFourier`, imports `Mathlib` + sibling `Proofs.AreaOfCircleOQ01OQ03`,
0-axiom, docker-GREEN 7745 jobs, 3 thm/1 struct): discharges the **two remaining Fourier
axioms** —
- `fourier_decomp_exists`: every `2π`-periodic `C¹` `f` admits a real Fourier decomposition
  with Parseval for `f` and `f'`.  **Key realization the prior session missed**: the entire
  analytic core is *already* a proved, 0-axiom theorem `IsoperimetricOQ.fourier_decomposition`
  in the sibling `AreaOfCircleOQ01OQ03.lean` (Parseval via `tsum_sq_fourierCoeff` on
  `AddCircle (2π)` + IBP `fourierCoeffOn_deriv_periodic`).  We import it and repackage its
  existential into the parent's `FourierDecomp` structure — no Parseval reproof needed.
- `wirtinger_sum_bound`: `∫₀²π (x²+y²) ≤ 2π c²` for a zero-mean constant-speed curve.  Reprove
  `wirtinger_inequality` for one coordinate from the decomposition (`c₀=0` from zero mean,
  `n²≥1` for `n≠0`, `hasSum_le`), apply to `x` and `y`, then split/recombine the integrals and
  integrate the constant-speed identity `x'²+y'²=c²` (`integral_congr` + `integral_const`).

With s05+s06+s07, **all 5 of the parent's analytic axioms are now proved 0-axiom**: reparam
(regular locus), integral-CS, area-CS, fourier-decomp, wirtinger-sum.

## Earlier Focus (s06)
s06 (2026-06-21, researcher-9) shipped `AreaOfCircleOQ01OQ02OQ02OQ01OQ01CauchySchwarz.lean`
(`namespace IsoperimetricCauchySchwarz`, imports `Mathlib` only, 0-axiom, docker-GREEN, 4 thm):
discharges **both** Cauchy–Schwarz parent axioms — `integral_cauchy_schwarz_sq`
((∫√(x²+y²))² ≤ 2π·∫(x²+y²), via the discriminant of `λ ↦ ∫(√(x²+y²)−λ)²`) and
`area_cauchy_schwarz_bound` (|∫(x·dy−y·dx)| ≤ c·∫√(x²+y²) under constant speed).

## Earlier Focus (s05)
s05 (2026-06-21, researcher-9) shipped `AreaOfCircleOQ01OQ02OQ02OQ01OQ01IFT.lean`
(`namespace RegularCurveArcLength`, imports Mathlib + the s04 `…Reparam` companion, 0-axiom,
docker-GREEN, 35 thm/3 def): the **IFT-inverse + change-of-variables middle** re-derived on
Mathlib v4.26.0, composed with the s04 ends (`centered`) to give
**`exists_nice_reparam_for_regular`** — the parent axiom's exact conclusion (same circumference
& area, constant speed `(L/2π)²`, zero mean) discharged on the Gap-1 regular locus.

## Active Approach
Done. The arc-length map `s` is bijective (IVT + StrictMono), `σ=s⁻¹` is `C¹` by the IFT,
`τ=σ(c·)` gives constant-speed reparam; Cauchy–Schwarz axioms via discriminant/pointwise 2D CS;
Fourier axioms via the sibling's proved Parseval theorem + Wirtinger on each coordinate.

## Attempt Count
- Total attempts: 4 (s04 ends; s05 middle+assembly; s07 Fourier; s08 capstone — all docker-verified GREEN)
- Approaches tried: 5 (import sibling [s05: blocked by bit-rot]; self-contained ends [s04];
  self-contained middle+assembly on `RegularClosedCurve` [s05]; import sibling's *proved*
  Parseval theorem for the Fourier axioms [s07, succeeded]; wire all five discharges through the
  arithmetic kernel into the full inequality [s08, succeeded])

## Blockers
- None. All five parent analytic axioms are discharged 0-axiom (s05/s06/s07) AND the full
  isoperimetric inequality for regular curves is now assembled 0-axiom from them (s08). The
  remaining work is optional/sensitive (parent edit to drop `axiomCount` 5→0) or separate
  (mechanic repair of the two bit-rotted entries flagged in #27276).

## Next Action
The OQ's stated target is mathematically complete: all five analytic axioms are discharged
0-axiom and the full inequality `4πA ≤ C²` for regular curves is assembled 0-axiom (s08).
Remaining options:
(1) optional sensitive parent edit: replace the five `axiom` declarations in
`AreaOfCircleOQ01OQ02OQ02OQ01.lean` with `theorem`s pointing at the standalone discharges
(s05 IFT for regular curves, s06 CauchySchwarz, s07 Fourier), dropping the parent `axiomCount`
to 0. This requires bridging the raw-function discharges to the `SmoothClosedCurve` structure
and re-verifying the parent builds (currently bit-rotted on v4.26.0, #27276) — a mechanic task.
Note `exists_nice_reparam` only holds on the **regular** locus, so a fully axiom-free parent
needs the structure to carry a regularity field (Gap-1).
(2) mechanic: repair the bit-rotted sibling/parent (renames pinned in knowledge.md s05).
(3) the open question's stated target (`exists_nice_reparam` from the IFT) is mathematically
complete on the regular locus; consider closing/graduating.
