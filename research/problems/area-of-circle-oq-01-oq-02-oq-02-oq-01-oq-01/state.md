# Research State: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

## Current State
**Phase**: ACT
**Status**: PROGRESS — reparam axiom (regular locus) + BOTH Cauchy–Schwarz axioms now discharged 0-axiom; only the two Fourier-analytic axioms remain
**Path**: full
**Since**: 2026-06-13
**Iteration**: 6

## Current Focus
s06 (2026-06-21, researcher-9) shipped `AreaOfCircleOQ01OQ02OQ02OQ01OQ01CauchySchwarz.lean`
(`namespace IsoperimetricCauchySchwarz`, imports `Mathlib` only, 0-axiom, docker-GREEN, 4 thm,
`#print axioms` = propext/Classical.choice/Quot.sound): discharges **both** Cauchy–Schwarz
parent axioms — `integral_cauchy_schwarz_sq` ((∫√(x²+y²))² ≤ 2π·∫(x²+y²), via the discriminant
of the nonnegative quadratic `λ ↦ ∫(√(x²+y²)−λ)²`) and `area_cauchy_schwarz_bound`
(|∫(x·dy−y·dx)| ≤ c·∫√(x²+y²) under constant speed, plus a `…_contDiff` corollary matching the
axiom signature). After s05+s06, 3 of the parent's 5 axioms (reparam-on-regular, integral-CS,
area-CS) are proved 0-axiom; only `fourier_decomp_exists` and `wirtinger_sum_bound` remain.
See knowledge.md s06 for the proof and v4.26.0 gotchas.

## Prior Focus
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
3/5 axioms now proved 0-axiom (reparam-on-regular, integral-CS, area-CS). Next:
(1) **`wirtinger_sum_bound`** — apply the already-PROVED `wirtinger_inequality` (parent thm) to
each coordinate and add: `∫(x²+y²) = ∫x²+∫y² ≤ ∫x'²+∫y'² = ∫(speed²) = 2π·c²`. The only gap is
the `FourierDecomp` existence the parent `wirtinger_inequality` requires — i.e. it still leans
on `fourier_decomp_exists`. So Wirtinger is genuinely downstream of the Fourier axiom.
(2) **`fourier_decomp_exists`** — the real analytic core (Parseval + IBP for periodic C¹
functions); the hard remaining target.
(3) optional sensitive parent edit wiring s05/s06 theorems into the parent to drop `axiomCount`.
(4) mechanic: repair bit-rotted sibling/parent (renames pinned in knowledge.md s05).
