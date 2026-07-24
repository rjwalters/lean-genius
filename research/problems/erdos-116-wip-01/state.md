# Research State: erdos-116-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-20
**Iteration**: 2

## Current Focus
Axiom-free topology of the polynomial lemniscate `Sₚ = {z : |p(z)| < 1}` for
`p ∈ UnitDiskPoly n`, built on the parent's root-factorization definitions.

## Status (S1, researcher-1, 2026-07-20) — Sₚ open / measurable / bounded
New file `proofs/Proofs/Erdos116WIP01.lean` (6 decls, 0 ax / 0 sorry,
host-verified `[propext, Classical.choice, Quot.sound]`). Discharges **Key lemma 1**
of problem.md: `continuous_eval`, `isOpen_sublevelSet`, `measurableSet_sublevelSet`,
`sublevelSet_subset_closedBall` (`Sₚ ⊆ closedBall 0 2`), `isBounded_sublevelSet`.

## Active Approach
Elementary complex-analysis / measure-theory scaffolding from the root product
`p(z) = ∏(z - zᵢ)`. The deep KLR `c/log n` lower bound and Pólya's `π` upper bound
rest on logarithmic potential theory absent from Mathlib and stay isolated.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- The KLR `c/log n` lower bound (and the `1/log n` vs `1/log log n` gap) is
  deep-blocked (route: logarithmic potential theory / value-distribution; reopen:
  materially new Mathlib potential-theory API required). Only the
  well-definedness/topology scaffolding is session-sized.

## Status (S4, researcher-1, 2026-07-22) — elementary layer SATURATED (stand-down)

The well-definedness / topology scaffolding is now **fully discharged** (all 0-axiom,
host-verified) across the earlier sessions and their merged PRs:
- **S1 (PR #40007)** `Sₚ` open / measurable / bounded (`Sₚ ⊆ closedBall 0 2`).
- **S2 (PR #40032)** finite 2D Lebesgue measure — the item the old "Next Action" below
  requested is DONE (`volume_sublevelSet_lt_top`, `volume_realProd_sublevelSet_lt_top` via the
  `ℂ ≅ ℝ²` volume-preserving equiv; `sublevelMeasure = volume.toReal` faithful).
- **S3 (PR #40898)** strict positivity (`volume_sublevelSet_pos`, `sublevelMeasure_pos`) — a
  nonempty open planar set has positive measure. So `0 < μ < ⊤`.

No session-sized elementary work remains: open/measurable/bounded/finite/positive are all
proven. The ONLY open content is DEEP and absent from Mathlib — the KLR `c/log n` lower bound,
Pólya's `π` upper bound, and the `1/log n` vs `1/log log n` gap (logarithmic potential theory /
lemniscate-area value distribution). These must be isolated as a single named assumption when
upgrading the gallery entry, not chased at the elementary layer. **STAND DOWN.**

## Next Action (SUPERSEDED — completed in S2, PR #40032)
~~Finiteness of `sublevelMeasure`: `Sₚ` is bounded + measurable ⟹ finite 2D
Lebesgue measure; bridge the parent's `ℝ×ℝ` sublevel set to `Sₚ ⊆ ℂ` via the
`ℂ ≅ ℝ²` measure isomorphism, then `measure_lt_top`.~~ Done. See S4 above: elementary
layer saturated; remaining work is deep potential theory (deep-blocked).

## Status (S5, researcher-1, 2026-07-22) — exact areas: z^n extremal = π, degree-1 invariance

New rung the saturated well-definedness layer did not cover: **exact values** of the
area functional (everything before only pinned `0 < μ < ∞`). All 0-axiom,
host-verified (`lake env lean` exit 0, fresh v4.31 olean chain):
- `allRootsZero n` (all roots at 0, `p(z) = zⁿ`): `sublevelSet = ball 0 1` exactly
  (`pow_lt_one_iff_of_nonneg`), `volume = π` (`Complex.volume_ball`), and
  `sublevelMeasure (allRootsZero n) = Real.pi` — first exact area value in the vein.
- `singleRoot z₀`: every degree-1 lemniscate is `ball z₀ 1`, so `sublevelMeasure ≡ π`
  independent of the root — the extremal problem is degenerate at degree 1.
- `exists_sublevelMeasure_eq_pi`: the conjectured extremal value π is attained at
  every degree n ≥ 1 — the attainment half of the sharp Pólya-type upper bound.

Remaining moves are still only the DEEP ones (KLR `c/log n` lower, Pólya `π` upper,
the `1/log n` vs `1/log log n` gap — logarithmic potential theory absent from
Mathlib). Elementary layer now saturated *including* exact-value computations.

## Status (S6, researcher-1, 2026-07-23, PR #42280 — merged) — explicit lower bound

(Back-filled by researcher-3: S6 did not update this file.) First *quantitative*
lower bound: `ball z₁ (1/(2·3^{n−1})) ⊆ Sₚ` (near factor `< r`, far factors `≤ 3`),
hence `sublevelMeasure_ge'`: `π/(4·9^{n−1}) ≤ sublevelMeasure P` for all `n ≠ 0`.

## Status (S7, researcher-3, 2026-07-24) — the extremal quantity A(n) itself

Everything through S6 was *per-configuration*. This session formalizes the object
the EHP problem is actually about — the extremal function
`minLemniscateArea n := ⨅ P : UnitDiskPoly n, sublevelMeasure P` — and pins it:
- `minLemniscateArea_le` (`A(n) ≤ area Sₚ`, via `ciInf_le` + `BddBelow` from the
  parent's `sublevelMeasure_nonneg`), `minLemniscateArea_nonneg`;
- **two-sided bounds** `π/(4·9^{n−1}) ≤ A(n) ≤ π` for `n ≥ 1`
  (`le_minLemniscateArea` via `le_ciInf` + S6's `sublevelMeasure_ge'`;
  `minLemniscateArea_le_pi` via the `zⁿ` witness), so `minLemniscateArea_pos`;
- **exact values** `A(0) = 0` (degree-0 lemniscate `{|1| < 1}` is empty:
  `eval_degree_zero`/`sublevelSet_degree_zero`/`sublevelMeasure_degree_zero`) and
  `A(1) = π` — with the constructor-free degree-1 chain
  (`eval_degree_one` … `sublevelMeasure_degree_one`) showing the area functional
  is constant `π` on ALL of `UnitDiskPoly 1`, not just `singleRoot` images;
- deep asymptotics isolated as named `Prop`s (NO axioms): `PommerenkeLowerBound`
  (`c/n⁴`), `KLRLowerBound` (`c/log n`, = EHP resolution), `KLRUpperBound`
  (`C/log log n`); plus the one elementary implication machine-checked:
  `pommerenkeLowerBound_of_klrLowerBound` (`log n ≤ n ≤ n⁴`, constant shrunk to
  `min c π` to handle `n = 1` via `A(1) = π`).

Lean notes: `gcongr` closes the `min c π / n⁴ ≤ c / log n` step (needs `0 ≤ c`,
`0 < log n` in context; discharges `log n ≤ n⁴` from context itself);
`Real.log_le_self`, `pow_le_pow_right₀`; `Complex.abs 1` does NOT simp via
`map_one` in this snapshot — use the defeq `have h1 : ‖·‖ < 1 := hz` + `norm_one`
idiom. Host-verified (borrowed sibling oleans, clean) + docker build.

Remaining open content unchanged and still DEEP: proofs of the three named Props
(logarithmic potential theory absent from Mathlib). The elementary layer is now
saturated *including* the extremal quantity; next genuinely new rungs would be
`A` monotone/asymptotic structure (unclear elementary) or Pólya `π` upper bound
per-configuration (deep). STAND DOWN at elementary layer after this.
