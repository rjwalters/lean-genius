# Research State: erdos-1215-oq-02

## Current State
**Phase**: PROVE
**Path**: full
**Since**: 2026-07-09T15:40:18-07:00
**Iteration**: 4

## Current Focus
Planar **area** of the cyclotomic level set `{|Φ_n(z)| < C}`, squeezed between the
two concentric discs established in iter 3.

## Active Approach
Approach A/B hybrid: elementary two-sided factor bounds `‖z‖-1 ≤ ‖z-μ‖ ≤ ‖z‖+1`
on primitive-root factors, giving `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)| ≤ (‖z‖+1)^{φ(n)}`, then
`φ(n)`-th roots to pin the level set between concentric balls.

## Attempt Count
- Total attempts: 4
- Current approach attempts: 1
- Approaches tried: 2

## Blockers
None for the geometric sandwich. The genuinely open driver (does a cyclotomic
labyrinth exist / path-length ≤ C·n) still needs polynomial-lemniscate topology and
rectifiable-path arc length not yet in Mathlib.

## Progress Log
- Iter 2 (researcher-4): level set bounded by `max 2 (C+1)`; escape-to-∞ path
  impossible for all C (`CyclotomicPolynomialsOQ02OQ01.lean`).
- Iter 3 (researcher-6): sharpened outer radius to `1 + C^{1/φ(n)}`, added inner
  ball containment; `1 + C^{1/φ(n)} ≤ max 2 (C+1)` and → 2 as φ(n) → ∞
  (`CyclotomicPolynomialsOQ02OQ02.lean`, VERIFIED 0/0).
- Iter 4 (researcher-5): pushed the iter-3 two-sided ball containment through the
  Lebesgue measure on `ℂ≅ℝ²` (`Complex.volume_closedBall` + `measure_mono`), giving
  the disc-area squeeze `π·r² ≤ area{|Φ_n|<C} ≤ π·(1+C^{1/φ(n)})²` and finite-area
  (`CyclotomicPolynomialsOQ02OQ03.lean`, VERIFIED 0/0, docker `[7746/7746]`).

## Next Action
Small-n (n=3,4,6) explicit lemniscate geometry / component count (the genuinely open
driver, needs polynomial-lemniscate topology Mathlib currently lacks). Area is now
sandwiched between the two discs; a sharper area asymptotic would need the exact
lemniscate boundary, not just the ball containment.
