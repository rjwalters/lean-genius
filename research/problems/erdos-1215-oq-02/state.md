# Research State: erdos-1215-oq-02

## Current State
**Phase**: PROVE
**Path**: full
**Since**: 2026-07-09T15:40:18-07:00
**Iteration**: 10 (OQ12 PREP — per-petal connectivity design locked, ACT-ready)

## Iter 10 — OQ12 PREP: exact two-path-component structure (researcher-2, 2026-07-24, doc-only)

Design for the next ACT (`CyclotomicPolynomialsOQ02OQ12.lean`): upgrade OQ11's
disconnection to the EXACT component count — each Cassini petal is
path-connected (star-shaped about its focus), so `{|(z−a)(z−b)| < C}` has
exactly two path-components in the separated regime `4C < ‖a−b‖²`.

### Core mathematical content (fully worked, sympy-verified this session)

**Ray monotonicity / star-shapedness.** For `w := z − a`, `c := b − a`,
`W := ‖w‖`, `D := ‖c‖`, `x := (w * conj c).re`, and `s ∈ [0, 1]` with
`2W ≤ D`, the Cassini product does not increase toward the focus:
`‖s•w‖·‖s•w − c‖ ≤ ‖w‖·‖w − c‖`. Squared form is polynomial; certificate:

```
W²(W²−2x+D²) − s²W²(s²W²−2sx+D²) = W²·[G + 2(1−s³)(WD − x)]   (decomposition)
G := (1−s⁴)W² − 2WD(1−s³) + (1−s²)D²
   = (1−s)·(D − W(1+s))·(D(1+s) − W(1+s²))                     (factorization)
```

All three `G`-factors and `(1−s³)`, `(WD − x)` are ≥ 0 given `0 ≤ s ≤ 1`,
`2W ≤ D`, Cauchy–Schwarz `x ≤ WD` — so `nlinarith` with product hints
`mul_nonneg (mul_nonneg h1ms hf1) hf2` and `mul_nonneg h1ms3 hWDx` should
close the squared inequality. Factor positivity: `D − W(1+s) ≥ D − 2W ≥ 0`;
`D(1+s) − W(1+s²) ≥ D − 2W ≥ 0` (`W(1+s²) ≤ 2W`, `D ≤ D(1+s)`).

### Lean target statements (new leaf `CyclotomicPolynomialsOQ02OQ12.lean`)

1. `cassini_segment_le {a b z : ℂ} (h : 2*‖z−a‖ ≤ ‖b−a‖) {s : ℝ}
   (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : ‖(s•(z−a)) * (a + s•(z−a) − b)‖ ≤
   ‖(z−a)*(z−b)‖` — via the certificate. Note `a + s•(z−a) − b =
   s•(z−a) − (b−a)` by `ring_nf`; `‖s•w‖ = s*W` by `norm_smul` +
   `Real.norm_of_nonneg`.
2. `starConvex_petal` : `StarConvex ℝ a ({z | ‖(z−a)*(z−b)‖ < C} ∩
   Metric.ball a (Real.sqrt C))` under `4C < ‖a−b‖²` — segment point stays
   in the ball (`sW ≤ W < √C`) and under the level (`cassini_segment_le`
   with `2W < 2√C = √(4C) ≤ D`).
3. `isPathConnected_petal` — from 2 (route A: `StarConvex.isPathConnected`
   if present in v4.31; route B fallback: explicit `JoinedIn` via the
   segment path `t ↦ a + t•(z−a)`, continuous affine).
4. `quadratic_lemniscate_two_path_components {a b C} (hC : 0 < C)
   (hsep : 4C < ‖a−b‖²) : (∀ z ∈ S, JoinedIn S z a ∨ JoinedIn S z b) ∧
   ¬ JoinedIn S a b` for `S = {z | ‖(z−a)(z−b)‖ < C}` — cover by OQ11
   `quadratic_lemniscate_subset_union`; per-petal `JoinedIn` from 3 via
   `JoinedIn.mono` (petal ⊆ S); negative half from OQ11
   `sqrt_balls_disjoint` applied to the preconnected range of a putative
   path (mirror of `not_isPreconnected_quadratic_lemniscate`'s cover
   argument). b-petal case = a-petal lemma with foci swapped
   (`mul_comm` inside the norm; `norm_sub_rev` for `‖b−a‖ = ‖a−b‖`).
5. Specializations n = 3, 4, 6 mirroring OQ11's sections (foci
   `omega3/omega3'`, `I/−I`, `zeta6/zeta6'`; thresholds `C < 3/4`, `< 1`,
   `< 3/4`): exactly two path-components sub-threshold.

### v4.31 name-risk list (probe at ACT)

- normSq ↔ norm² bridge: `Complex.sq_abs` / `Complex.normSq_eq_abs` /
  possibly `Complex.normSq_eq_norm_sq`; expansions `Complex.normSq_sub`,
  `Complex.normSq_mul`, `Complex.normSq_ofReal`; `Complex.real_smul`.
- Cauchy–Schwarz step: `Complex.abs_re_le_abs` (may be `…_le_norm`);
  name-safe fallback: `x² ≤ normSq w * normSq c` from `Complex.normSq_apply`
  + `sq_nonneg (…).im`, then `x ≤ WD` via `abs_le_abs` on square roots, or
  feed the squared form to nlinarith.
- A ≤ B from A² ≤ B² (A,B ≥ 0): avoid `pow_le_pow_iff_left` drift — use
  `nlinarith [norm_nonneg …, sq_nonneg (A+B)]`.
- `StarConvex.isPathConnected` existence; `JoinedIn.mono`;
  `isConnected_range γ.continuous` for the path-range cover argument.
- Known v4.31: `push_neg` → `push Not at h`; `Set.notMem_empty`.

### Why this rung (and not others)

- Option (a) sharpness (connectivity for `C ≥ (‖a−b‖/2)²`) needs a
  through-the-neck path construction — genuinely harder, no certificate.
- Option (c) quartic φ(n)=4 (n=5,8,10,12) needs a 4-focus cover +
  4-ball disjointness regime — natural AFTER the exact-count template
  exists at 2 foci.
- The genuine open driver (C > 1 labyrinth / path-length ≤ C·n) remains
  blocked ("materially new mechanism required").

## Current Focus
Component topology of the lemniscate. Iter 9 (OQ02OQ11) delivered the first
disconnection result: the quadratic cyclotomic lemniscates (n = 3, 4, 6 — the complete
φ(n) = 2 case, Cassini ovals) split into two petals for small C. Still open: component
count in the C > 1 regime (every-boundary-point reachability driver), and sharpness
(connectivity above the Cassini threshold).

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
- Iter 8 (researcher-3): **EXIT IN EVERY DIRECTION** — generalized OQ02OQ08's radial
  exit to arbitrary unit direction `u`: first crossing `t*` along every ray with NEW
  two-sided sharp bound `C^{1/φ(n)}-1 ≤ t* ≤ 1+C^{1/φ(n)}` (lower bound new even for
  `u=1`, via OQ07's sharp inner ball); level curve `{|Φ_n|=C}` meets every ray inside
  the sharp annulus (boundary radially surrounds origin, n-uniformly); straight-segment
  length packaging. (`CyclotomicPolynomialsOQ02OQ10.lean`, VERIFIED docker
  `[8580/8580]`, 0-axiom `[propext,Classical.choice,Quot.sound]`; `ray_exit` +
  `levelCurve_meets_every_ray` + `ray_exit_pathLength`.) The DIRECTIONAL half of the
  iter-7 refinement question is now closed; the every-boundary-point half still needs
  lemniscate component topology (blocked, unchanged).

- Iter 9 (researcher-3, 2026-07-24): **FIRST COMPONENT-TOPOLOGY RESULT** — the small-n
  tractable layer delivered for the complete quadratic case. `n = 3, 4, 6` are exactly
  the indices with `φ(n) = 2`; their lemniscates are Cassini ovals with foci at the two
  primitive roots. General Cassini disconnection engine (`{|z−a||z−b| < C}` covered by
  the two focal `√C`-balls; disjoint when `4C < |a−b|²`; each contains a focus, so
  `IsPreconnected` fails on the cover): `{|Φ₃| < C}` and `{|Φ₆| < C}` are DISCONNECTED
  (not preconnected/connected/path-connected) for `0 < C < 3/4` (foci `√3` apart),
  `{|Φ₄| < C}` for `0 < C < 1` (foci `2` apart). Byproduct: `cyclotomic 4 ℂ = X² + 1`,
  absent from Mathlib, proved via `cyclotomic_expand_eq_cyclotomic`.
  (`CyclotomicPolynomialsOQ02OQ11.lean`, VERIFIED docker `[8577/8577]`, 0-sorry/0-axiom.)

## Next Action
The every-boundary-point half of the reachability question: is EVERY point of the level
curve `{|Φ_n|=C}` reachable from 0 by a bounded-length path inside the set? The first
crossing along each ray reaches one boundary point per direction (iter 8); boundary
points that are NOT first crossings (behind folds of the lemniscate, if any exist) are
untouched. Deciding whether such points exist at all needs the connected-component /
fold structure of the cyclotomic lemniscate in the relevant regime `C > 1` —
polynomial-lemniscate topology Mathlib still lacks (blocked, unchanged for `C > 1`).
The small-C half is now settled for the quadratic case (iter 9): remaining small-n
follow-ups are (a) sharpness — connectivity for `C` above the Cassini threshold
`(|a−b|/2)²`; (b) exact component count 2 (per-petal connectivity); (c) the quartic
`φ(n) = 4` cases `n = 5, 8, 10, 12` (multi-focus, multi-petal).
