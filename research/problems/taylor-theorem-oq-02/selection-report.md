# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 533 in-progress, 1238 completed

## Selected Problem

- **ID**: taylor-theorem-oq-02
- **Name**: Characterize Taylor remainder interaction with Lean analytic function API
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among fresh candidates (76)**: EMPTY knowledge tier (0 items)
   combined with tractability 7 gives the top score among uninitiated problems.
2. **Domain diversity**: Recent selections were combinatorics (burnside-counting-oq-01),
   graph coloring (unit-distance-independence-oq-02), and algebra (vietas-formulas-oq-02).
   Analysis is underrepresented — this rebalances the pipeline.
3. **Tractability 7 is strong for autonomous research**: The Lean Mathlib `Analysis.Calculus.Taylor`
   module is well-documented. The analytic function API (`AnalyticOn`, `HasFPowerSeriesAt`) is
   mature. The gap between "Taylor polynomial remainder → 0" and "analytic iff Taylor series
   converges" is a meaningful but bridgeable step, not an open conjecture.

## Rejection Summary

- **Candidates considered**: 15 available
- **Candidates rejected**: 14
  - `triangular-reciprocals-oq-02` (score 75): C tier, significance 5 — below quality bar
  - `factor-remainder-nullstellensatz-oq-02` (score 67): Good but lower tractability (6)
  - `buffons-needle-oq-01-oq-04` (score 66): Geometry/probability, significance 6
  - `wolstenholme-theorem-oq-03` (score 66): Number theory, significance 6
  - `erdos-ko-rado-oq-04` (score 57): Tractability 5, significance 7 — harder for autonomous research
  - `brouwer-fixed-point-oq-04-oq-04` (score 56): Constructive content extraction is subtle
  - `szemeredi-theorem-oq-01` (score 48): Significance 8 but tractability 4 — too hard solo
  - `prime-gap-bounds-oq-03` (score -1923): MODERATE knowledge (11 items), lower priority
  - Already-initialized (skip re-selecting): `euler-identity-oq-01-oq-04`,
    `unit-distance-independence-oq-02`, `vietas-formulas-oq-02`, `erdos-szekeres-oq-01`,
    `mean-value-theorem-oq-04`, `taylor-sincos-convergence-oq-01`
- **Confidence**: medium (score spread between top 2 is modest: 76 vs 75, but tier difference justifies)

## Related Gallery Proofs

- `taylor-theorem`: Parent proof (Wiedijk #35) — verified, 0 sorries. Provides
  `taylor_lagrange_remainder`, `taylor_cauchy_remainder`, `taylor_remainder_bound`. OQ-02
  asks what happens when f is analytic (not just smooth).
- `taylor-theorem-oq-03`: Taylor series convergence of `exp` via Cauchy remainder —
  verified with mathlib badge. Shows the blueprint: use Cauchy form, bound remainder,
  take limit. OQ-02 generalizes this to arbitrary analytic functions.
- `taylor-sincos-convergence`: Related — convergence of sin/cos Taylor series.
  Provides `sinPartialSum` infrastructure that may inform analytic API patterns.

## The Core Problem

The Taylor theorem proof uses `taylor_mean_remainder_lagrange`/`_cauchy` from
`Mathlib.Analysis.Calculus.Taylor`. These give: for some ξ,
```
f(x) = Tₙ(x) + Rₙ(x)
```
where Rₙ depends on `iteratedDeriv f (n+1) ξ`.

The **analytic function API** in Mathlib uses:
- `AnalyticOn ℝ f s` — f has a convergent power series at every point in s
- `HasFPowerSeriesAt f p x` — f equals its power series p at x
- `HasFPowerSeriesOnBall f p x r` — convergence on a ball

**OQ-02 asks**: Can we connect these? Specifically:
1. If `AnalyticOn ℝ f s`, does the Taylor remainder `Rₙ(x) → 0` as n → ∞?
2. Can we express `taylorWithinEval` in terms of `FormalMultilinearSeries`?
3. Is there a Mathlib lemma like `AnalyticAt.hasFPowerSeriesAt` that we can bridge to?

## Suggested First Steps

1. **OBSERVE**: Search Mathlib for bridging lemmas — look for `AnalyticOn.taylor`,
   `hasFPowerSeriesAt_iff`, and whether `iteratedDeriv` connects to `FormalMultilinearSeries`.
   Check `Mathlib.Analysis.Analytic.Basic` and `Mathlib.Analysis.Calculus.Taylor`.
2. **ORIENT via Scout**: Survey how `taylor-theorem-oq-03` (exp convergence) bridges
   Cauchy remainder to convergence — this is the template. Check if that proof uses
   `AnalyticOn` or only smoothness + derivative bounds.
3. **DECIDE**: Formulate a concrete theorem statement, e.g.:
   ```lean
   theorem analytic_taylor_remainder_tendsto {f : ℝ → ℝ} {x₀ : ℝ}
       (hf : AnalyticAt ℝ f x₀) (x : ℝ) :
       Filter.Tendsto (fun n => f x - taylorWithinEval f n (Set.univ) x₀ x)
         Filter.atTop (nhds 0)
   ```
   Or alternatively find the Mathlib theorem that already says this and write a
   wrapper that makes it accessible from the Taylor proof context.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 533 |
| Completed | 1238 |
| Blocked | 1 |
| **Total** | **~1787** |

## Candidate Pool Health

Pool depth is adequate (15 available). No replenishment needed immediately.

- Pool depth: **adequate**
- Recommendation: Pool healthy — 15 available problems span analysis, algebra,
  combinatorics, number theory, topology, and probability.
- Next refresh recommended: When available count drops below 5
