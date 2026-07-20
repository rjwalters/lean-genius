# Research State: erdos-1215-oq-02

## Current State
**Phase**: PROVE
**Path**: full
**Since**: 2026-07-09T15:40:18-07:00
**Iteration**: 7

## Current Focus
The literal OQ-02 target — an admissible bounded-length PATH from 0 to the
boundary of `{|Φ_n|<C}` — for the cases where that set is convex, i.e. the
degree-one cyclotomics `Φ_1 = X-1`, `Φ_2 = X+1`. All six prior iterations proved
only *containment/area/radius/symmetry* facts and never constructed a path;
iteration 7 constructs one. `n ≥ 3` (non-convex lemniscates) remains the open
driver.

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
- Iter 4b: outer *radius* `1+C^{1/φ(n)}` is antitone in the degree and `→ 2`, giving
  uniform confinement of high-degree lemniscates in `closedBall(0, 2+ε)`
  (`CyclotomicPolynomialsOQ02OQ04.lean`); `Φ_n` are explicit unit-circle witnesses,
  axiom-free re-derivation of the parent negative answer
  (`CyclotomicPolynomialsOQ02OQ05.lean`).
- Iter 5 (researcher-6): **area** analogue of OQ02OQ04 — the sharp outer disc area
  `π·(1+C^{1/φ(n)})²` has floor `4π`, is antitone in the degree, and `→ 4π` as
  `φ(n) → ∞` (`CyclotomicPolynomialsOQ02OQ06.lean`, UNVERIFIED — docker infra down,
  containerd content-store blob I/O error; assembled on the VERIFIED OQ02OQ04 radius
  lemmas via `Tendsto.pow`/`Tendsto.const_mul`/`rpow_le_rpow`, all API-checked vs the
  local mathlib pin).
- Iter 6 (researcher-9): sharp **inner** radius `C^{1/φ(n)}-1` pinned
  (`CyclotomicPolynomialsOQ02OQ07.lean`, VERIFIED axiom-free
  `[propext,Classical.choice,Quot.sound]`, direct-lean build vs prebuilt mathlib
  oleans, bypassing the locked/contended shared `.lake`). Closes the two-sided
  *sharp radius* sandwich `ball(0,C^{1/φ(n)}-1) ⊆ {|Φ_n|<C} ⊆ closedBall(0,1+C^{1/φ(n)})`
  (OQ02OQ03 had only a free inner radius `r`); proves `|Φ_n(0)|=1`
  (`∏‖0-μ‖=∏‖μ‖=1`), the origin is an *interior* point for `C>1`
  (`zero_mem_interior_levelSet`), and a sharp inner-radius area lower bound
  `π·(C^{1/φ(n)}-1)² ≤ area{|Φ_n|<C}` via `Complex.volume_ball` — the inner
  companion to OQ02OQ03's outer-area bound. Mechanism: `‖z‖<C^{1/φ(n)}-1 ⟹
  (‖z‖+1)^{φ(n)}<C` by `pow_lt_pow_left₀`+`Real.rpow_inv_natCast_pow`, then the
  OQ02OQ02 upper bound. Also confirmed OQ02OQ06 (iter 5, was UNVERIFIED) rebuilds
  clean via the same direct-lean path.

- Iter 7 (researcher-1): **first admissible-PATH construction**
  (`CyclotomicPolynomialsOQ02OQ08.lean`, VERIFIED axiom-free
  `[propext,Classical.choice,Quot.sound]`, host lean v4.31 vs prebuilt mathlib
  oleans). Defined `HasStraightEscape P c L` (a ray `γ t = t•v` from 0 that reaches
  the boundary `|P|=c`, stays in the closed sublevel set, and has segment length
  `≤ L`), sidestepping the missing rectifiable-arc-length infra by using the
  straight-segment length. Proved `hasStraightEscape_linear_unitRoot`: every linear
  `X-a` with `‖a‖=1` and `c>1` has such a path of length `c-1` (ray `t•(-a)`).
  Specialised to `Φ_1` (`a=1`) and `Φ_2` (`a=-1`) via `cyclotomic_one/two`, then
  `cyclotomic_deg_one_hasStraightEscape_linear_bound` gives the OQ-02 target form
  `length ≤ c·n` for `n∈{1,2}`. This is the FIRST iteration to build a path rather
  than a containment; the length `c-1` is `O(1)`, far under the linear `c·n` target.

## Next Action
`n ≥ 3` (`Φ_3,Φ_4,Φ_6`): here the sublevel set stops being convex (quadratic
lemniscate, can split into components), so the straight-ray trick of iter 7 no
longer works and a genuine path through a possibly-disconnected region is needed.
This is the genuinely open driver — needs polynomial-lemniscate topology / component
count and a rectifiable arc-length functional Mathlib still lacks. The elementary
*containment/area/radius/symmetry* surface (iters 2–6) plus the *convex-case path*
(iter 7) are now saturated; further progress requires new Mathlib infrastructure, not
another elementary bound.
