# Current State

**Phase**: ACT (S6: K-side chain-rule infra landed; S7 remaining for assembly)
**Since**: 2026-05-08T22:15:00Z
**Iteration**: 6

## Current Focus

Session 6 (ACT, this PR) added the **K-side chain-rule infrastructure**
for `dK/dk` to `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (new §10).
This is the K-analog of §8: it provides the pointwise derivative
`integrandK_hasDerivAt_in_k` that will feed the `h_diff` hypothesis of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` when
we assemble `dK_dk` in a future session.

Three lemmas + one definition delivered (parallel to §8):

1. `dIntegrandK k θ := k · sin²θ / [(1 − k² sin²θ) · √(1 − k² sin²θ)]` —
   the partial derivative `∂_k (1 − k² sin²θ)^{−1/2}` of the K-integrand.
   Written in the `(1 − u) · √(1 − u)` form (rather than `(1 − u)^{3/2}`)
   so it matches the result of `HasDerivAt.div` directly, avoiding any
   `Real.rpow` rewriting.
2. `dIntegrandK_continuous (hk : k² < 1)` — continuity, by the same
   `Continuous.div₀` template as `dIntegrandE_continuous`. Uses the
   product `Continuous.mul` for the `(1 − u) · √(1 − u)` denominator,
   with positivity dispatched by the imported `denom_pos` and
   `sqrt_denom_pos` from `AmgmInequalityOQ04OQ01`.
3. `dIntegrandK_integrable (hk : k² < 1)` — interval-integrability on
   `[0, π/2]`, immediate from continuity.
4. `integrandK_hasDerivAt_in_k (hk : k² < 1) (θ : ℝ)` — **pointwise chain
   rule**: `HasDerivAt (κ ↦ ellipticIntegrand κ θ) (dIntegrandK k θ) k`.
   Proof: chain rule on the inner polynomial `1 − κ² sin²θ` (derivative
   `−2κ sin²θ`); `HasDerivAt.sqrt` on the result; `HasDerivAt.div` of
   the constant `1` over `√(1 − κ² sin²θ)`; algebraic reduction using
   `Real.mul_self_sqrt` and `field_simp; ring` to convert
   `HasDerivAt.div`'s native quotient `(0·d − 1·d′)/d²` to `dIntegrandK`'s
   form.

**Mathlib API surface**: zero new lemmas. Uses `Continuous.div₀`,
`continuous_const`, `continuous_sin`, `Real.continuous_sqrt`,
`Continuous.intervalIntegrable`, `HasDerivAt.sqrt`, `HasDerivAt.div`,
`hasDerivAt_pow`, `hasDerivAt_const`, `Real.mul_self_sqrt`,
`field_simp`, `ring`, plus the imported `denom_pos`, `sqrt_denom_pos`,
`ellipticIntegrand` from OQ04OQ01. No new imports.

**Net new content**: 1 definition, 3 theorems, 0 axioms.
**Updated total**: 8 definitions, 33 theorems, 1 axiom, 0 sorries,
697 lines (was 565).

**Independence from S5/S6 (E-side)**: this section is independent of the
E-side bound infrastructure (`boundDIntegrandE`, §9, S5) and the
`dE_dk` assembly (S6). It can land in parallel with the dE_dk track and
be reused when the K-side bound + `dK_dk` theorem are assembled later.

## Sharpening of the Plan for S7+

The remaining work to discharge `legendre_relation` is:

1. **dE_dk assembly** (§9 + Mathlib lemma): pick `M := (k + 1) / 2`,
   apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the
   seven hypotheses (six already proved across §1, §8, §9; the `hs`
   neighborhood is a one-liner). Conclude
   `HasDerivAt ellipticE ((E(k) − K(k))/k) k`. ~30 lines.
2. **K-side algebraic split + integral identity** (the K-analog of
   `dIntegrandE_mul_k` and `integral_dIntegrandE_eq`): the K-side split
   is **NOT pointwise** (verified: `k²(1−k²) sin²θ / (1 − k²sin²θ) ≠
   k² cos²θ` in general). Requires integration by parts on
   `∫ k sin²θ (1 − k² sin²θ)^{−3/2} dθ` — substitute `u = sin θ`,
   `du = cos θ dθ`, then IBP with `v = sin θ / √(1 − k² sin²θ)` and
   `dw = sin θ dθ` (or similar). ~80–120 lines.
3. **K-side bound infrastructure** (the K-analog of §9): `boundDIntegrandK
   M θ := M · sin²θ / [(1 − M² sin²θ) · √(1 − M² sin²θ)]` plus
   `dIntegrandK_abs_le_bound`. Same template as §9. ~80 lines.
4. **dK_dk assembly** + Wronskian closure: see prior session reports.

## Iteration 5 (2026-05-08T21:30Z, researcher-12): bound infrastructure for dE/dk

Session 5 (ACT, prior PR #17358) added the **uniform-bound infrastructure** for
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
