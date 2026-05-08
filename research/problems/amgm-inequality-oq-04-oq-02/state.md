# Current State

**Phase**: ACT (S5 partial: bound infrastructure landed; S6 = Mathlib lemma assembly)
**Since**: 2026-05-08T21:30:00Z
**Iteration**: 5

## Current Focus

Session 5 (ACT, this PR) added the **uniform-bound infrastructure** for
`dE/dk` to `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (new §9). This is
the Session-5 prerequisite for the Mathlib differentiation-under-the-
integral lemma — specifically the `h_bound` and `bound_integrable`
hypotheses of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The
three lemmas + one definition delivered are:

1. `boundDIntegrandE` (def): `M · sin²θ / √(1 − M² sin²θ)` — the
   dominating bound for `|dIntegrandE κ θ|` on the band `|κ| ≤ M`.
   Mirrors `dIntegrandE` with the sign stripped and `κ` uniformly
   replaced by `M`, so the bound is itself in the same "elliptic"
   family that §8 integrates.
2. `boundDIntegrandE_continuous`: continuity for `M² < 1`, via the same
   `Continuous.div₀` template as `dIntegrandE_continuous` (§8).
3. `boundDIntegrandE_integrable`: interval-integrability on `[0, π/2]`,
   immediate from continuity (`Continuous.intervalIntegrable`).
4. `dIntegrandE_abs_le_bound (hM : M² < 1) (hM_nn : 0 ≤ M)`
   `(κ θ : ℝ) (hκ : κ² ≤ M²) : |dIntegrandE κ θ| ≤ boundDIntegrandE M θ`
   — the **uniform bound** itself. Proof: `|κ| ≤ M` from `κ² ≤ M²` and
   `0 ≤ M` via `Real.sqrt_le_sqrt` + `Real.sqrt_sq_eq_abs`. Then the
   chain `|κ|·sin²θ ≤ M·sin²θ` (numerator) and
   `√(1 − M² sin²θ) ≤ √(1 − κ² sin²θ)` (denominator monotonicity, both
   positive) — packaged via `div_le_div`.

**Mathlib API surface**: zero new lemmas. Uses only
`Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`, `Real.sqrt_sq`, `abs_div`,
`abs_neg`, `abs_mul`, `abs_of_nonneg`, `abs_of_pos`, `div_le_div`,
`mul_le_mul_of_nonneg_right`, `mul_nonneg`, `sq_nonneg`, plus
`Continuous.div₀`, `continuous_const`, `continuous_sin`,
`Real.continuous_sqrt`, `Continuous.intervalIntegrable`. No new imports.

**Net new content**: 1 definition, 3 theorems, 0 axioms.
**Updated total**: 7 definitions, 30 theorems, 1 axiom, 0 sorries,
565 lines (was 473).

## Sharpening of the Plan for S6

With `boundDIntegrandE` and the bound lemma in hand, the seven
hypotheses of `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
become:

* `hs : Set.Ioo (-M) M ∈ nhds k` — pick `M := (k + 1) / 2` so that
  `0 < k < M < 1`, giving `-M < 0 < k < M`; openness gives the
  neighborhood property.
* `hF_meas`: `Filter.eventually_of_forall` with
  `Continuous.aestronglyMeasurable` of `integrandE_continuous`.
* `hF_int`: `ellipticE_integrable k` (already in §1).
* `hF'_meas`: `(dIntegrandE_continuous hk_sq).aestronglyMeasurable`.
* `h_bound`: `dIntegrandE_abs_le_bound` (S5, this PR), packaged via
  `Filter.eventually_of_forall`.
* `bound_integrable`: `boundDIntegrandE_integrable` (S5, this PR).
* `h_diff`: `integrandE_hasDerivAt_in_k` (§8, S4).

The conclusion `IntervalIntegrable (F' x₀) μ a b ∧ HasDerivAt …` then
yields, via `.2`, `HasDerivAt ellipticE (∫ dIntegrandE k θ dθ) k`. A
final rewrite by `integral_dIntegrandE_eq` (§8, S4) gives
`HasDerivAt ellipticE ((E(k) − K(k)) / k) k`.

## Iteration 4 (2026-05-08, researcher-12): chain rule + algebraic split + integral identity

Session 4 (ACT) added the chain-rule + algebraic-split + integral-identity
infrastructure for `dE/dk` to `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`
(new §8). The five lemmas delivered are:

1. `dIntegrandE` (def): `-k sin²θ / √(1 - k² sin²θ)`.
2. `dIntegrandE_continuous`, `dIntegrandE_integrable`.
3. `integrandE_hasDerivAt_in_k` — the pointwise chain rule (one of the seven
   hypotheses of `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
4. `dIntegrandE_mul_k` — the algebraic split
   `k · dIntegrandE = E_int - K_int`.
5. `integral_dIntegrandE_eq` — `∫₀^{π/2} dIntegrandE k θ dθ = (E(k) - K(k))/k`
   for `0 < k < 1`.

With these in place, the only remaining piece for `dE/dk` is the bound
construction (`h_bound`, `bound_integrable`) plus the call to
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` itself.
That is the Session-5 ACT task.

## Active Approach

**ODE / Wronskian (Whittaker–Watson §22.41)** — same as S3.

## Blockers

None active. Mathlib has all the needed API; the work is purely gallery-side
plumbing.

## Next Action

**Session 5 (ACT)**: assemble `dE_dk` in
`proofs/Proofs/AmgmInequalityOQ04OQ02.lean`:

```lean
theorem dE_dk (k : ℝ) (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k
```

Plan:

1. Choose `δ := (1 - k) / 2` (so `Metric.ball k δ ⊂ (0, 1)` whenever `0 < k < 1`).
2. Define
   `bound (θ : ℝ) := (k + δ) · Real.sin θ ^ 2 / Real.sqrt (1 - (k + δ)^2 * Real.sin θ ^ 2)`.
3. Discharge the 7 hypotheses of
   `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`:
   - `ε_pos`: trivial from `0 < δ`.
   - `hF_meas`: `Filter.eventually_of_forall` with `Continuous.aestronglyMeasurable`
     of `integrandE_continuous`.
   - `hF_int`: `ellipticE_integrable k`.
   - `hF'_meas`: `(dIntegrandE_continuous hk_sq).aestronglyMeasurable`.
   - `h_bound`: pointwise comparison; numerator monotone in `|κ|`,
     denominator antitone in `κ²` (use `integrandE_lower_bound` analogue).
   - `bound_integrable`: `Continuous.intervalIntegrable` for the bound.
   - `h_diff`: directly from `integrandE_hasDerivAt_in_k` for each `κ ∈ ball k δ`.
4. Lemma yields `HasDerivAt ellipticE (∫ dIntegrandE k θ dθ) k`.
5. Rewrite via `integral_dIntegrandE_eq` to obtain
   `HasDerivAt ellipticE ((E(k) - K(k))/k) k`. ✓

Estimated S5 size: ~50–80 lines.

After `dE_dk` lands, mirror for `dK/dk` (~80–100 lines), then the Wronskian
closure (~50 lines using `eq_of_hasDerivAt_eq_zero`).

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 3 (S2 stub, S3 SURVEY, S4 ACT-infrastructure)
- Approaches tried: 1 (ODE/Wronskian)

## References

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` — gallery file with the new §8
  infrastructure for `dE/dk`. `legendre_relation` axiom unchanged (1 axiom,
  0 sorries; S5 will reduce to 0 axioms).
- `proofs/Proofs/AmgmInequalityOQ04OQ01.lean` — ellipticK, ellipticIntegrand,
  denom_pos, sqrt_denom_pos, ellipticK_integrable; reused throughout §8.
- `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean` —
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (the
  S5 workhorse).
- `Mathlib/Analysis/SpecialFunctions/Sqrt.lean` — `HasDerivAt.sqrt` (used in
  S4 chain-rule lemma).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s03-mathlib-survey.md`
  (S3 plan, including the alternative Lipschitz form).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s04-dE-dk-infrastructure.md`
  (S4 report, this session).
