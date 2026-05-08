# S5 (2026-05-08, researcher-12): Uniform-bound infrastructure for `dE/dk`

**Phase**: ACT
**Outcome**: progress (S5 partial — bound infrastructure landed, S6 = Mathlib lemma assembly)
**Build**: pending (no local Docker access this session)

## Goal

Provide the `h_bound` and `bound_integrable` ingredients of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` so
that S6 can assemble `dE_dk : HasDerivAt ellipticE ((E−K)/k) k` from the
S4 components (chain rule, algebraic split, integral identity).

## Deliverables

New section §9 in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (+92 lines):

* `boundDIntegrandE (M θ : ℝ) : ℝ := M · sin²θ / √(1 − M² sin²θ)`
  — the dominating bound, defined for any `M`.
* `boundDIntegrandE_continuous (hM : M² < 1)` — Continuous via the
  same `Continuous.div₀` template as `dIntegrandE_continuous` (§8).
* `boundDIntegrandE_integrable (hM : M² < 1)` — IntervalIntegrable on
  `[0, π/2]` via `Continuous.intervalIntegrable`.
* `dIntegrandE_abs_le_bound (hM : M² < 1) (hM_nn : 0 ≤ M) (κ θ : ℝ)`
  `(hκ : κ² ≤ M²) : |dIntegrandE κ θ| ≤ boundDIntegrandE M θ` — the
  uniform pointwise bound. Proof: `|κ| ≤ M` from `κ² ≤ M²` and `0 ≤ M`
  via `Real.sqrt_le_sqrt`/`Real.sqrt_sq_eq_abs`. The bound itself
  reduces, after `abs_div`/`abs_neg`/`abs_mul`, to a single `div_le_div`
  call: numerator monotonicity from `mul_le_mul_of_nonneg_right` and
  denominator monotonicity from `Real.sqrt_le_sqrt`.

Counts: 7 defs, 30 thms, 1 axiom (unchanged: `legendre_relation`),
0 sorries, 565 lines (was 6/27/1/0/473).

## Plan refinement: band-radius `M` instead of ball-radius `δ`

The original S5 plan (in S4's session report) chose `δ := (1−k)/2` and
worked on `Metric.ball k δ`. This is suboptimal: for `k ≤ 1/3` we have
`k − δ ≤ 0`, so the natural bound `|κ| ≤ k + δ` becomes loose (the
ball straddles 0).

The S5 (this session) replacement uses the open band `Set.Ioo (-M) M`
with `M := (k + 1)/2`:

* `0 < k < M` (since `M − k = (1−k)/2 > 0` from `k < 1`)
* `M < 1` (since `M = (k+1)/2 < 1` from `k < 1`)
* `0 < M` (so `0 ≤ M` is automatic for `dIntegrandE_abs_le_bound`)
* `Set.Ioo (-M) M ∈ nhds k` (open interval containing `k`)
* `|κ| < M ⟹ κ² < M²` (squaring nonneg sides)

This gives a clean closed-form bound (no `min` of cases) and the
strict-< nbhd condition needed by Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

## Mathlib API surface (S5)

Zero new lemmas required. All terms used:

* From the file's own §1–§8: `dIntegrandE`, `boundDIntegrandE`,
  `AmgmInequalityOQ04OQ01.sqrt_denom_pos`.
* From Mathlib (already imported via `import Mathlib`): `sq_nonneg`,
  `lt_of_le_of_lt`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`,
  `Real.sqrt_sq`, `abs_div`, `abs_neg`, `abs_mul`, `abs_of_nonneg`,
  `abs_of_pos`, `div_le_div`, `mul_le_mul_of_nonneg_right`, `mul_nonneg`,
  `Continuous.div₀`, `continuous_const`, `continuous_sin`,
  `Real.continuous_sqrt`, `Continuous.intervalIntegrable`, `nlinarith`.

No new imports.

## What's left for S6

Apply
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
with `M := (k + 1) / 2` and the seven hypotheses listed in `state.md`'s
"Sharpening of the Plan for S6" section. Estimated ~50–80 lines of
tactic code, dominated by the `Filter.eventually_of_forall` packaging
of the `h_bound` and `h_diff` hypotheses (both currently in pointwise
form in §8/§9) and the openness/membership argument for `Set.Ioo (-M) M`.

## Notes on build

This session's edits were not built under Docker (no local access this
iteration). The Lean code follows the §8 templates verbatim, so the
risk is API-name drift (e.g. `Continuous.div₀` vs `Continuous.div`).
Spot-check from inspection:

* `Continuous.div₀` is used identically in `dIntegrandE_continuous`
  (S4, presumably already builds): same signature here.
* `Real.sqrt_sq_eq_abs` and `Real.sqrt_sq` are stable Mathlib names.
* `div_le_div` (4-argument variant) is the `OrderedField`/`LinearOrder`
  flavor; if it has been renamed, `div_le_div_of_nonneg_left` /
  `div_le_div_iff` with manual rearrangement are drop-in replacements.

A future Docker build will confirm; if a name has drifted, the fix is
purely lexical and S6 can roll it in.
