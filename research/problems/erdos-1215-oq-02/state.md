# Research State: erdos-1215-oq-02

## Current State
**Phase**: PROVE
**Path**: full
**Since**: 2026-07-09T15:40:18-07:00
**Iteration**: 6

## Current Focus
The sharp **inner** radius `C^{1/φ(n)}-1` and origin interiority: closing the
two-sided *sharp radius* sandwich `ball(0, C^{1/φ(n)}-1) ⊆ {|Φ_n|<C} ⊆
closedBall(0, 1+C^{1/φ(n)})` to mirror the two-sided *area* sandwich of OQ02OQ03.

## Active Approach
Approach A/B hybrid: elementary two-sided factor bounds `‖z‖-1 ≤ ‖z-μ‖ ≤ ‖z‖+1`
on primitive-root factors, giving `(‖z‖-1)^{φ(n)} ≤ |Φ_n(z)| ≤ (‖z‖+1)^{φ(n)}`, then
`φ(n)`-th roots to pin the level set between concentric balls.

## Attempt Count
- Total attempts: 5
- Current approach attempts: 1
- Approaches tried: 3

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

- Iter 7 (researcher-1): **RADIAL EXIT PATH** — first actual *path* result for the
  family (all prior OQ02 work pinned only ball/area *shape*). The positive-real-axis
  segment `[0, t*]` from `0` to the first level-`C` crossing stays strictly inside
  `{|Φ_n| < C}`, ends exactly on the boundary `|Φ_n(t*)| = C`, and has length
  `t* ≤ 1 + C^{1/φ(n)}` (n-uniform, `→ 2`). Mechanism: `g(t)=|Φ_n(t)|` continuous,
  `g(0)=1<C`, OQ02OQ01 lower bound forces `g(1+C^{1/φ(n)})≥C`; `t*=sInf` of the closed
  crossing set is the first crossing (`IsClosed.csInf_mem` + `intermediate_value_Icc`
  for exactness). This is the cyclotomic **positive** counterpart to Mac Lane's general
  **negative** answer: a single radial ray already exits, so `{|Φ_n| < C}` is *not* a
  labyrinth. Needs **no** arc-length / rectifiable-path infrastructure (the noted Mathlib
  gap for the *general* #1215) — a segment's length is its endpoint distance.
  (`CyclotomicPolynomialsOQ02OQ08.lean`, VERIFIED docker `[8580/8580]`, 0-axiom
  `[propext,Classical.choice,Quot.sound]`; `radial_exit` + `radial_exit_pathLength`.)

## Next Action
Small-n (n=3,4,6) explicit lemniscate geometry / component count (the genuinely open
driver, needs polynomial-lemniscate topology Mathlib currently lacks). Both radius and
area are now pinned on BOTH sides (sharp inner `C^{1/φ(n)}-1` / outer `1+C^{1/φ(n)}`);
note the inner radius `→ 0` while the outer `→ 2` as `φ(n)→∞`, so the two-sided disc
squeeze is not asymptotically tight — pinning the true interior area needs the exact
lemniscate boundary, not ball containment. The radial-exit path (iter 7) gives a short
exit along ℝ_{≥0}; a natural refinement is whether *every* boundary point is reachable by
a bounded-length path (not just one exit ray) — that likely still needs the labyrinth-free
topology of the full lemniscate, currently beyond Mathlib.

## Status (researcher-3, 2026-07-24) — OQ10: sublevel disconnection landed

`CyclotomicPolynomialsOQ02OQ10.lean`: {|Φ_n| < C} NOT preconnected for n ≥ 3,
0 < C ≤ imProd n (real-axis avoidance + conjugate pair in opposite half-planes);
for n = 4 sharp at the question's own C = 1. Component count ≥ 2 in the small-C
regime — first sublevel-topology fact. Next: imProd 4 = 1 as named theorem;
per-lobe connectivity (exact count 2); large-C reconnection. Deep driver unchanged.
