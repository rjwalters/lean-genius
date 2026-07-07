/-
Central Limit Theorem OQ-02-OQ-04: Ibragimov's CLT for Polynomial α-Mixing Sequences

**Question.** Suppose {X_n} is a stationary α-mixing sequence with E[X₁] = 0,
E[|X₁|^{2+δ}] < ∞ for some δ > 0, and the mixing coefficients decay at the
*polynomial* rate α(n) ≤ C · n^{−r}. What is the sharp threshold on r that
yields the central limit theorem?

**Answer.** The sharp threshold is `r > (2 + δ) / δ`. Under this hypothesis,
the Ibragimov (1962) covariance summability condition

  ∑_n α(n)^{δ/(2+δ)} < ∞

is satisfied, and the long-run variance σ² = Var(X₁) + 2∑_{k≥1} Cov(X₁, X_{k+1})
exists and is finite. If additionally σ² > 0, then S_n/√n →_d N(0, σ²).

**S28 (this session): L^∞ (symmetric-window) Davydov estimate.** Added
`linfty_covariance_le_four_alpha` and `truncated_covariance_le_four_alpha_sq`
(both PROVEN, 0-axiom): specialize the S27 signed estimate
`|Cov(f,g)| ≤ α·(M−m)·(N−n)` to the *symmetric* truncation window
`[−Bf, Bf] × [−Bg, Bg]`, yielding the canonical `L^∞` Davydov bound
`|Cov(f,g)| ≤ 4·α·Bf·Bg` from the single essential-sup hypotheses `|f| ≤ Bf`,
`|g| ≤ Bg` (unpacked via `abs_le`; the window-width product `(2Bf)(2Bg)`
collapses to `4·Bf·Bg` by `ring`). The equal-bound corollary
`truncated_covariance_le_four_alpha_sq` gives `|Cov| ≤ 4·α·T²` for a common
truncation level `T` — verbatim the constant the L^p density step of
`davydov_covariance_inequality` pays for the bounded part after truncating at
level `T`, before the Hölder tail in the mixing rate `α^{(p−2)/p}` is added.
Sorries unchanged (2).

**S27: signed bounded-variable Davydov estimate.** Added
`signed_bounded_covariance_le_alpha_mul_rectangle` (PROVEN, 0-axiom): lifts the
S26 non-negative bounded estimate `|Cov(f,g)| ≤ α·M·N` to *signed* bounded
variables `m ≤ f ≤ M`, `n ≤ g ≤ N`, giving `|Cov(f,g)| ≤ α·(M−m)·(N−n)`. The
proof shifts `f ↦ f − m`, `g ↦ g − n` to the non-negative range via the S19
translation-invariance lemmas (`covariance_add_const_left/right`) — the exact
constant-shift reduction those lemmas were introduced to serve — and applies S26
to the shifts. Product integrabilities for the linearity identities come from
`Integrable.bdd_mul` (each shift is bounded measurable on a probability space).
For a symmetric truncation `[−T, T]` (`m = −T`, `M = T`) the window width is
`2T`, so the truncated base estimate reads `|Cov| ≤ 4 α T²` — the form the L^p
density step (Hölder over truncation level) consumes. Sorries unchanged (2).

**Status of this file (S5b — `davydov_indicator_bound` — indicator base case of
Davydov's covariance inequality, third order-theory ingredient now proven).**

S5b (this session) discharges the third and final order-theory ingredient
flagged in the structural decomposition of `davydov_covariance_inequality`:
`davydov_indicator_bound` states that
`|μ(A ∩ B).toReal − μ(A).toReal · μ(B).toReal| ≤ alphaMixingCoeff μ ℱ 𝒢` for
measurable indicators `A ∈ ℱ`, `B ∈ 𝒢`. The proof peels the 4-fold nested ⨆
via `le_ciSup_of_le` at the two `Set Ω` layers (with `BddAbove` witnesses
uniformly derived from `indicator_cov_le_one`) and `ciSup_pos` at the two
`Prop` layers. After S5b, the open Davydov decomposition reduces to the L^p
density step alone (S5c target, ~100 lines: truncation + Hölder).

Sorries remaining: 2 (unchanged — this PR adds one proven theorem; the two
sorries `davydov_covariance_inequality` (S5c) and `mixing_clt_ibragimov` (S6+)
remain).

**S22 (this session): marginal-side layer-cake integration.** Added
`mean_eq_survival_lt_Ioc` and `mean_prod_eq_double_survival_lt_Ioc` (both
PROVEN, 0-axiom). The first integrates the S21 pointwise super-level identity
into the bounded Cavalieri form `∫ f = ∫_{(0,M]} μ.real{t < f} dt` (strict `<`,
matching the super-level indicators of `superlevel_setOf_measurable`); it is
derived from Mathlib's `Integrable.integral_eq_integral_meas_lt` by restricting
the `Ioi 0` tail to the finite window `(0, M]` (the survival probability
vanishes for `t > M` by boundedness). The second gives the *product of
marginals* as a separable double survival integral
`(∫f)(∫g) = ∫_{(0,M]}∫_{(0,N]} μ.real{t<f}·μ.real{s<g}` — the factorized half of
the covariance layer-cake `Cov(f,g) = ∫∫ Cov(𝟙_{f>t}, 𝟙_{g>s})`, collapsed by
`integral_const_mul`/`integral_mul_const` (no product-measure Fubini needed since
the integrand factorizes). Only the joint term `∫ f·g = ∫∫ μ.real{t<f ∧ s<g}`
(the genuine `Ω × [0,M] × [0,N]` Fubini swap) remains for S23; subtracting it
from the marginal term yields the covariance representation. Sorries
unchanged (2).

**S19 (this session): covariance translation-invariance.** Added
`covariance_add_const_left` and `covariance_add_const_right` (PROVEN, 0-axiom):
`Cov(f + c, g) = Cov(f, g)` and `Cov(f, g + c) = Cov(f, g)` in the explicit
`∫ f·g − (∫ f)(∫ g)` form, under integrability of `f`, `g`, `f·g` on a
probability measure. These are the algebraic reduction the Davydov density step
(S5c) uses to replace a signed bounded `f ∈ [m, M]` by the *nonnegative* shift
`f − m ∈ [0, M − m]` (the form required by the layer-cake / super-level
indicator decomposition). Pure Bochner linearity: `integral_add` +
`integral_const_mul` on the joint integral, `∫ c ∂μ = c` on the marginal.
Sorries unchanged (2).

**Earlier session: S17 — simple-function (finite-sum) covariance bound.**
Added `finset_indicator_covariance_le_alpha` (PROVEN, 0-axiom): lifts the S16
single-cell bound to a *pair of simple functions*
`f = ∑ᵢ aᵢ 1_{Aᵢ}` (σPair 0-measurable) and `g = ∑ⱼ bⱼ 1_{Bⱼ}`
(σPair 1-measurable):
`|Cov(f, g)| ≤ (∑ᵢ |aᵢ|)(∑ⱼ |bⱼ|) α(ℱ, 𝒢)`.
The covariance is bilinear, so the joint integral and the product of marginals
both distribute (`Finset.sum_mul_sum`, pushed through `integral_finset_sum`
using per-cell integrability `(aᵢ1_{Aᵢ})(bⱼ1_{Bⱼ}) = aᵢbⱼ 1_{Aᵢ∩Bⱼ}`) into the
double sum `∑ᵢ∑ⱼ Cov(aᵢ1_{Aᵢ}, bⱼ1_{Bⱼ})`; two applications of
`Finset.abs_sum_le_sum_abs` + the S16 per-cell bound + `Finset.sum_mul_sum`
collect the constant. This discharges the *algebraic* content of ingredient 4
(the "L^p density step") in the structural decomposition below — every
`σPair`-measurable simple function is exactly such a finite indicator
combination — leaving only the analytic residue (truncation of `X, Y` to bounded
simple approximants + Hölder amplification to `‖X‖_{L^p}‖Y‖_{L^p}`) for a later
session. No sorry reduction this session — purely additive infrastructure.

**Earlier session: S16 — scaled-indicator covariance bound.**
Added `scaled_indicator_covariance_le_alpha` (PROVEN): promotes the unit
`indicator_covariance_le_alpha` to arbitrary real scalars,
`|Cov(a 1_A, b 1_B)| ≤ |a| |b| α(ℱ, 𝒢)`, by pulling the scalars through the
bilinear covariance (`integral_const_mul` on the joint and marginal integrals)
and `abs_mul`. This is the single-cell building block of the simple-function
step toward `davydov_covariance_inequality`: a sub-σ-measurable simple function
`∑ aᵢ 1_{Aᵢ}` covaried against `∑ bⱼ 1_{Bⱼ}` reduces, by bilinear expansion, to
a finite sum of exactly these scaled-cell bounds.

**Earlier session: S5a — Mathlib drift fix.**
Closed a previously open Mathlib-drift sorry that was carried forward from S2:
the ζ-function summability fact `Σ n^{-s} < ∞ ↔ s > 1`. We use
`Real.summable_nat_rpow : Summable ((n:ℝ)^p) ↔ p < -1` from
`Mathlib.Analysis.PSeries`; with `p = -s` and `s > 1` the equivalence yields the
result by a single `linarith`. Sorry count: 3 → 2.

**Earlier session: S4 ACT (build-fix + structural decomposition).**
S3 (PR #17820) merged at `build pending` and never actually compiled
on `origin/main`. The compile blockers were:
(a) stale import `Mathlib.Probability.Variance` (file removed in Mathlib drift).
(b) typeclass synthesis quirk where direct
    `(ℱ 𝒢 : MeasurableSpace Ω)` args compete with the ambient
    `[MeasurableSpace Ω]` instance at every call to `alphaMixingCoeff`.
(c) bound name `σ²` (superscript 2) is not a valid Lean identifier.

This session (S4) fixes all three blockers and **gets the file building
cleanly**, AND adds the structural decomposition of `davydov_covariance_inequality`
into named ingredients (documented in the proof outline of that theorem):

S4 deliverables (this session):
- **Build fix**: removed stale `Mathlib.Probability.Variance` import,
  refactored `davydov_covariance_inequality` to take
  `(σPair : Fin 2 → MeasurableSpace Ω)` (the parent file's
  `σ_k : ℕ → MeasurableSpace Ω` pattern) instead of `(ℱ 𝒢 : MS Ω)` to
  dodge the typeclass-synthesis competition, renamed `σ²` → `σsq` in
  `mixing_clt_ibragimov`.
- **`indicator_cov_le_one` (PROVEN)**: the per-term `[0, 1]` envelope helper
  — the `BddAbove` witness for any further work on the nested suprema in
  `alphaMixingCoeff`.
- **Documented structural decomposition**: the docstring of
  `davydov_covariance_inequality` now identifies the 3 named order-theory
  ingredients (`alphaMixingCoeff_le_one`, `alphaMixingCoeff_nonneg`,
  `davydov_indicator_bound`) onto which the L^p version reduces, plus the
  L^p density step. Each ingredient has a clear strategy; the order-theory
  facts are mechanic-pass targets.

Carried forward from S3 (unchanged math, mild signature/identifier tweaks):
- `Stationary`, `PolynomialMixingRate`, `MomentBound2δ` predicates.
- `IbragimovHypotheses` structure (16 fields — S6 ACT adds `past_le` and
  `future_le` per Finding E from PR #19289).
- `polynomial_summable_of_exponent_gt_one`, `ibragimov_threshold_summable`.
- `stationary_eLpNorm_eq`, `polynomial_mixing_summable`.
- `longrun_variance_absolutely_convergent` (proven modulo Davydov sorry;
  call site updated to use the `Fin 2 → MS Ω` σ-pair pattern).

Sorries remaining (2, unchanged in count from S3, but the file now builds):
- `davydov_covariance_inequality` — full L^p version,
  `|Cov(X, Y)| ≤ 12 · α^((p-2)/p) · ‖X‖_p · ‖Y‖_p`. Structurally reduces to
  `davydov_indicator_bound` + L^p density step (~100 lines, S5 target).
- `mixing_clt_ibragimov` — main CLT, S6+ target.

Axioms: 0 — parent `CentralLimitTheoremOQ02.lean` carries the abstract α-mixing
infrastructure; this file consumes rather than re-axiomatizes.

Per the S1/S2 plan, this file builds on the parent
`CentralLimitTheoremOQ02.lean`, which defines `alphaMixingCoeff`,
`AlphaMixingSequence`, and `longRunVariance`.
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Proofs.CentralLimitTheoremOQ02

open MeasureTheory ProbabilityTheory Filter Real Topology

namespace CentralLimitTheoremOQ02OQ04

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Part I: Stationarity, Mixing, and Moment Predicates -/

/-- A sequence `X : ℕ → Ω → ℝ` is *stationary* under `μ` if every shift
preserves the marginal distribution. We state the predicate in its weakest
useful form here — pairwise identical distribution `X k =ᵈ X 0` — which is the
slice needed for the long-run variance computation. The full joint-stationarity
predicate (over all finite tuples) is the natural completion and would be
introduced in S6+ when invoking the Bernstein block decomposition.
-/
def Stationary (μ : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ k, IdentDistrib (X k) (X 0) μ μ

/-- *Polynomial α-mixing rate*: `α n ≤ C · n^{-r}` for all `n ≥ 1`. The exponent
`r > 0` controls the speed of decay of dependence between the past and the
future at lag `n`. Ibragimov's CLT requires `r > (2 + δ) / δ` where `δ` is the
moment-bound exponent. -/
def PolynomialMixingRate (α : ℕ → ℝ) (C r : ℝ) : Prop :=
  0 < C ∧ 0 < r ∧ ∀ n : ℕ, 1 ≤ n → α n ≤ C * (n : ℝ) ^ (-r)

/-- *Uniform `(2 + δ)`-th moment bound*: for all `k`, `∫ |X k|^{2 + δ} dμ < ∞`.

The standard Ibragimov CLT requires `δ > 0` (strictly more than 2 moments).
The formulation matches Mathlib's `MemLp` hypothesis for `p = 2 + δ`. -/
def MomentBound2δ (μ : Measure Ω) (X : ℕ → Ω → ℝ) (δ : ℝ) : Prop :=
  ∀ k, MemLp (X k) (ENNReal.ofReal (2 + δ)) μ

/-- *Ibragimov's hypotheses* bundle: a stationary α-mixing sequence with mean
zero, uniformly bounded `(2 + δ)`-th moments, and polynomial mixing decay at
rate strictly exceeding the sharp threshold `(2 + δ) / δ`.

The sharp threshold `r > (2 + δ) / δ` arises from the requirement that the
Ibragimov covariance summability series

  ∑_n α(n)^{δ/(2+δ)}

converges; substituting the polynomial bound α(n) ≤ C · n^{−r} gives
∑_n n^{−rδ/(2+δ)}, which is summable iff `rδ/(2+δ) > 1`, i.e., `r > (2 + δ) / δ`.

**S3 extension.**  The structure now records three additional fields that were
missing in S2:  (i) `alpha_nonneg`, since the abstract α-mixing coefficient is
a supremum of |·| values, but the parent file's `alphaMixingCoeff_nonneg`
lemma is omitted due to nested `ciSup` elaboration complexity, so the numerical
bound `alpha` needs explicit nonnegativity;  (ii) `past_measurable` and
(iii) `future_measurable`, which assert that `X k` is measurable with respect
to its own past/future σ-algebra (a hidden assumption needed for any
Davydov-type covariance bound to apply at the per-term level).
-/
structure IbragimovHypotheses
    (μ : Measure Ω) (X : ℕ → Ω → ℝ) (δ C r : ℝ) where
  /-- Joint stationarity (marginal slice). -/
  stationary : Stationary μ X
  /-- Each `X k` is integrable under μ. -/
  integrable : ∀ k, Integrable (X k) μ
  /-- Mean zero: `∫ X k dμ = 0`. -/
  mean_zero : ∀ k, ∫ ω, X k ω ∂μ = 0
  /-- Moment exponent `δ > 0`. -/
  delta_pos : 0 < δ
  /-- The `(2 + δ)`-th moment is finite. -/
  moment_bound : MomentBound2δ μ X δ
  /-- The numerical mixing coefficient bound. -/
  alpha : ℕ → ℝ
  /-- The numerical bound is nonnegative. -/
  alpha_nonneg : ∀ n, 0 ≤ alpha n
  /-- The past σ-algebra at time `k`. -/
  pastSigma : ℕ → MeasurableSpace Ω
  /-- The future σ-algebra at time `k+n`. -/
  futureSigma : ℕ → MeasurableSpace Ω
  /-- `X k` is measurable with respect to the past at time `k`. -/
  past_measurable : ∀ k, Measurable[pastSigma k] (X k)
  /-- `X k` is measurable with respect to the future at time `k`. -/
  future_measurable : ∀ k, Measurable[futureSigma k] (X k)
  /-- The past σ-algebra at time `k` is a sub-σ-algebra of the ambient measurable
      structure on `Ω`. This is true by construction in any standard filtration; it
      is made explicit here because `indicator_covariance_le_alpha` (S5c-prep, line
      443) needs both sub-σ measurability AND ambient `MeasurableSet` at its call
      site (in particular for level sets `{ω | X ω > t}` arising from the
      level-set decomposition in `davydov_covariance_inequality`'s L^p density
      step, S5c target). -/
  past_le : ∀ k, pastSigma k ≤ (inferInstance : MeasurableSpace Ω)
  /-- The future σ-algebra at time `k` is a sub-σ-algebra of the ambient
      measurable structure on `Ω`. Companion to `past_le`; see that field's
      docstring for motivation. -/
  future_le : ∀ k, futureSigma k ≤ (inferInstance : MeasurableSpace Ω)
  /-- `alpha n` bounds the abstract α-mixing coefficient at lag `n`. -/
  alpha_bound : ∀ k n,
    CentralLimitTheoremOQ02.alphaMixingCoeff μ (pastSigma k) (futureSigma (k + n))
      ≤ alpha n
  /-- The numerical bound decays at polynomial rate. -/
  poly_rate : PolynomialMixingRate alpha C r
  /-- The sharp threshold: the polynomial decay exponent strictly exceeds
      `(2 + δ) / δ`. -/
  rate_admissible : r > (2 + δ) / δ

/-! ## Part II: Elementary summability helpers -/

/-- *Polynomial summability* of `n^{-s}` for `s > 1`: the standard ζ-function
fact, derived from Mathlib's `Real.summable_nat_rpow` (which characterises
`Summable (n ↦ n ^ p)` as `p < -1`). With `p = -s` and `s > 1` we get
`-s < -1`. -/
theorem polynomial_summable_of_exponent_gt_one (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
  Real.summable_nat_rpow.mpr (by linarith)

/-- *Sharp-threshold corollary*: under Ibragimov's hypotheses with
`r > (2 + δ) / δ`, the Ibragimov covariance series ∑ n^{−rδ/(2+δ)} is summable. -/
theorem ibragimov_threshold_summable (δ r : ℝ)
    (hδ : 0 < δ) (hr : r > (2 + δ) / δ) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(r * δ / (2 + δ)))) := by
  apply polynomial_summable_of_exponent_gt_one
  have h2δ_pos : 0 < 2 + δ := by linarith
  have h_rδ_gt : 2 + δ < r * δ := by
    have step : ((2 + δ) / δ) * δ < r * δ := mul_lt_mul_of_pos_right hr hδ
    rwa [div_mul_cancel₀ (2 + δ) (ne_of_gt hδ)] at step
  rw [lt_div_iff₀ h2δ_pos]
  linarith

/-! ## Part II-bis: Truncation tail second-moment bound (S18, this session)

The Lindeberg condition (S9 target) and the L^p density step inside Davydov's
inequality both hinge on a *truncation tail estimate*: when a random variable
has a finite `p`-th moment for some `p > 2`, its **second** moment restricted to
the large-values region `{|X| > T}` decays like `T^{-(p-2)}`. This is the
quantitative form of uniform integrability of `X²` that powers the
negligibility of the truncated remainder in every block-CLT argument.

The two lemmas below are pure real-analysis / measure-theory facts (no α-mixing,
no `IbragimovHypotheses`), so they are self-contained forward infrastructure —
directly reusable in the S8–S9 Bernstein-block Lindeberg verification. -/

/-- **Pointwise truncation bound.** On the large-values region `T < |x|`, with
`2 ≤ p`, the square is dominated by the `p`-th power scaled by `T^{2-p}`:
`x² ≤ T^{2-p} · |x|^p`.

Proof: `x² = |x|² = |x|^p · |x|^{2-p}` (with `|x|^{2-p}` a `Real.rpow`), and since
the exponent `2 - p ≤ 0` and `0 < T ≤ |x|`, base-antitonicity of `rpow` at a
nonpositive exponent (`Real.rpow_le_rpow_of_nonpos`) gives `|x|^{2-p} ≤ T^{2-p}`. -/
theorem sq_le_rpow_of_large {p T x : ℝ} (hp : 2 ≤ p) (hT : 0 < T)
    (hx : T < |x|) :
    x ^ 2 ≤ T ^ (2 - p) * |x| ^ p := by
  have hxpos : 0 < |x| := lt_trans hT hx
  have hxnn : (0 : ℝ) ≤ |x| := le_of_lt hxpos
  have hxp_nn : 0 ≤ |x| ^ p := Real.rpow_nonneg hxnn p
  have hexp : (2 : ℝ) - p ≤ 0 := by linarith
  have hanti : |x| ^ (2 - p) ≤ T ^ (2 - p) :=
    Real.rpow_le_rpow_of_nonpos hT (le_of_lt hx) hexp
  -- `x² = |x|^(2:ℝ)`
  have h1 : x ^ 2 = |x| ^ (2 : ℝ) := by
    rw [← sq_abs x, ← Real.rpow_natCast |x| 2]; norm_num
  -- `|x|^(2:ℝ) = |x|^p · |x|^(2-p)`
  have h2 : |x| ^ (2 : ℝ) = |x| ^ p * |x| ^ (2 - p) := by
    rw [← Real.rpow_add hxpos]; congr 1; ring
  calc x ^ 2 = |x| ^ p * |x| ^ (2 - p) := by rw [h1, h2]
    _ ≤ |x| ^ p * T ^ (2 - p) := mul_le_mul_of_nonneg_left hanti hxp_nn
    _ = T ^ (2 - p) * |x| ^ p := by ring

/-- **Truncation tail second-moment bound** (S18, this session).

For a measurable `X` with integrable `p`-th power (`2 ≤ p`) and threshold `T > 0`,
the second moment on the large-values set `{ω | T < |X ω|}` is controlled by the
full `p`-th moment:
$$
\int_{\{T < |X|\}} X^2 \, d\mu \;\le\; T^{\,2-p} \int |X|^p \, d\mu.
$$

The proof integrates the pointwise bound `sq_le_rpow_of_large`: the indicator of
`X²` on the tail set is dominated everywhere by the integrable envelope
`T^{2-p} · |X|^p` (off the tail set the indicator is `0`, which is `≤` the
nonnegative envelope). `integral_mono` on the indicator form, then
`integral_indicator` and `integral_const_mul`, deliver the stated bound. -/
theorem truncation_tail_sq_le
    {μ : Measure Ω} {X : Ω → ℝ} {p T : ℝ}
    (hp : 2 ≤ p) (hT : 0 < T) (hX : Measurable X)
    (hXp : Integrable (fun ω => |X ω| ^ p) μ) :
    ∫ ω in {ω | T < |X ω|}, X ω ^ 2 ∂μ ≤ T ^ (2 - p) * ∫ ω, |X ω| ^ p ∂μ := by
  set S : Set Ω := {ω | T < |X ω|} with hS_def
  have habs_meas : Measurable (fun ω => |X ω|) := by
    simpa [Real.norm_eq_abs] using measurable_norm.comp hX
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const habs_meas
  have hT2p_nn : (0 : ℝ) ≤ T ^ (2 - p) := Real.rpow_nonneg (le_of_lt hT) _
  -- Integrable, nonnegative dominating envelope `g = T^(2-p) · |X|^p`.
  have hg_int : Integrable (fun ω => T ^ (2 - p) * |X ω| ^ p) μ := hXp.const_mul _
  -- The truncated square, written as an indicator.
  have hf_aesm : AEStronglyMeasurable (S.indicator (fun ω => X ω ^ 2)) μ :=
    ((hX.pow_const 2).aestronglyMeasurable).indicator hSmeas
  have hf_nn : ∀ ω, 0 ≤ S.indicator (fun ω => X ω ^ 2) ω := fun ω =>
    Set.indicator_nonneg (fun a _ => sq_nonneg (X a)) ω
  -- Pointwise domination `f ω ≤ g ω`, everywhere.
  have hbound : ∀ ω,
      S.indicator (fun ω => X ω ^ 2) ω ≤ T ^ (2 - p) * |X ω| ^ p := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      have hω' : T < |X ω| := hω
      exact sq_le_rpow_of_large hp hT hω'
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg hT2p_nn (Real.rpow_nonneg (abs_nonneg _) _)
  have hf_int : Integrable (S.indicator (fun ω => X ω ^ 2)) μ :=
    hg_int.mono' hf_aesm (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf_nn ω)]; exact hbound ω))
  have hstep :
      ∫ ω, S.indicator (fun ω => X ω ^ 2) ω ∂μ
        ≤ ∫ ω, T ^ (2 - p) * |X ω| ^ p ∂μ :=
    integral_mono hf_int hg_int hbound
  rw [integral_indicator hSmeas, integral_const_mul] at hstep
  exact hstep

/-! ## Part III: α-mixing coefficient basic facts (S4 deliverable)

The parent file `CentralLimitTheoremOQ02.lean` defines `alphaMixingCoeff` as a
4-fold nested supremum over measurable-pair indicators. This section proves
three facts about the nested suprema:

* `indicator_cov_le_one`: the per-term `[0, 1]` envelope, used as the
  `BddAbove` witness elsewhere.
* `alphaMixingCoeff_nonneg`: the 4-fold supremum is non-negative (S5; closes
  the omission noted in the parent file at line 444).
* `alphaMixingCoeff_le_one`: the 4-fold supremum is bounded above by `1`
  (S5; the upper-bound companion of `alphaMixingCoeff_nonneg`).

The two ingredient bounds dodge the parent file's "nested ciSup elaboration
complexity" obstacle by using `Real.iSup_nonneg` / `Real.iSup_le`, which are
reflective in `ι : Sort*` and so peel each `⨆` layer uniformly whether the
index is `Set Ω` (a `Type`) or `MeasurableSet …` (a `Prop`). The indicator
base case `davydov_indicator_bound` of Davydov's inequality
`|μ(A ∩ B).toReal - μ(A).toReal · μ(B).toReal| ≤ alphaMixingCoeff μ ℱ 𝒢` is
the remaining S5 mechanic-pass target (the `le_ciSup_of_le` direction; needs
a `BddAbove` discharge from `alphaMixingCoeff_le_one`).
-/

/-- A uniform `[0, 1]` envelope for the indicator-covariance term: for any two
sets `A, B` in a probability space, the absolute deviation of `μ(A ∩ B).toReal`
from `μ(A).toReal · μ(B).toReal` is at most `1`. This is the `BddAbove` witness
used inside the nested suprema of `alphaMixingCoeff`. -/
theorem indicator_cov_le_one
    {μ : Measure Ω} [IsProbabilityMeasure μ] (A B : Set Ω) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ 1 := by
  -- For a probability measure, every set's measure is ≤ μ(univ) = 1.
  have measure_le_one : ∀ s : Set Ω, μ s ≤ 1 := fun s => by
    calc μ s ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hAB_le : (μ (A ∩ B)).toReal ≤ 1 := by
    have := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) (measure_le_one (A ∩ B))
    simpa using this
  have hA_le : (μ A).toReal ≤ 1 := by
    have := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) (measure_le_one A)
    simpa using this
  have hB_le : (μ B).toReal ≤ 1 := by
    have := ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) (measure_le_one B)
    simpa using this
  have hAB_nn : 0 ≤ (μ (A ∩ B)).toReal := ENNReal.toReal_nonneg
  have hA_nn : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hB_nn : 0 ≤ (μ B).toReal := ENNReal.toReal_nonneg
  have hprod_nn : 0 ≤ (μ A).toReal * (μ B).toReal := mul_nonneg hA_nn hB_nn
  have hprod_le : (μ A).toReal * (μ B).toReal ≤ 1 := by
    calc (μ A).toReal * (μ B).toReal
        ≤ 1 * 1 := mul_le_mul hA_le hB_le hB_nn (by norm_num)
      _ = 1 := by norm_num
  rw [abs_le]
  refine ⟨by linarith, by linarith⟩

/-- **Non-negativity of `alphaMixingCoeff`** (S5 — discharges named ingredient (2)
of the Davydov structural decomposition; closes the omission noted in the parent
file `CentralLimitTheoremOQ02.lean` at line 444).

The defining 4-fold nested supremum has range contained in `[0, ∞)` since every
inner term is `|·|`. The proof peels the nested `⨆` one layer at a time via
`Real.iSup_nonneg`, which is reflective in `ι : Sort*` and therefore applies
uniformly whether the index is a `Type` (`Set Ω`) or a `Prop` (`MeasurableSet …`).
This avoids the per-level `BddAbove` discharge that the parent file flagged as
the elaboration blocker.

We follow the file convention of taking `σPair : Fin 2 → MeasurableSpace Ω` as
the σ-algebra pair (rather than direct `(ℱ 𝒢 : MeasurableSpace Ω)` args), to
dodge the Lean 4 typeclass-synthesis quirk where direct `MeasurableSpace Ω`
arguments compete with the ambient `[MeasurableSpace Ω]` instance — the same
pattern used by the parent file's `independent_implies_zero_mixing` and S4's
`davydov_covariance_inequality`. -/
theorem alphaMixingCoeff_nonneg
    {μ : Measure Ω} (σPair : Fin 2 → MeasurableSpace Ω) :
    0 ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  unfold CentralLimitTheoremOQ02.alphaMixingCoeff
  apply Real.iSup_nonneg; intro _A
  apply Real.iSup_nonneg; intro _hA
  apply Real.iSup_nonneg; intro _B
  apply Real.iSup_nonneg; intro _hB
  exact abs_nonneg _

/-- **`alphaMixingCoeff ≤ 1`** for a probability measure (S5 — discharges named
ingredient (1) of the Davydov structural decomposition).

The defining supremum ranges over the `[0, 1]`-valued indicator-covariance term
`|μ(A ∩ B).toReal - μ(A).toReal · μ(B).toReal|`, bounded by `1` via
`indicator_cov_le_one`. Since `1 ≥ 0`, `Real.iSup_le` applies at each of the 4
nested `⨆` layers without further `BddAbove` witnesses — the same reflective
trick used in `alphaMixingCoeff_nonneg`.

σ-algebras are passed via the `σPair : Fin 2 → MeasurableSpace Ω` function form
(cf. `alphaMixingCoeff_nonneg`). -/
theorem alphaMixingCoeff_le_one
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω) :
    CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) ≤ 1 := by
  unfold CentralLimitTheoremOQ02.alphaMixingCoeff
  apply Real.iSup_le _ (by norm_num); intro A
  apply Real.iSup_le _ (by norm_num); intro _hA
  apply Real.iSup_le _ (by norm_num); intro B
  apply Real.iSup_le _ (by norm_num); intro _hB
  exact indicator_cov_le_one A B

/-- **Indicator base case of Davydov's covariance inequality** (S5b — discharges
named ingredient (3) of the Davydov structural decomposition).

For measurable indicator sets `A ∈ σPair 0` and `B ∈ σPair 1` of a probability
measure `μ`, the absolute indicator-pair covariance is bounded by the α-mixing
coefficient:
$$
\bigl|\mu(A \cap B).\!toReal - \mu(A).\!toReal \cdot \mu(B).\!toReal\bigr|
   \;\le\; \alpha(\mathcal F, \mathcal G).
$$

This is the *defining* inequality of `alphaMixingCoeff` packaged for direct
use: the body of the 4-fold nested supremum, instantiated at our particular
measurable `A, B`. The proof peels each ⨆ layer using `le_ciSup_of_le` for
the two `Set Ω` layers and `ciSup_pos` for the two `Prop` layers, with the
`BddAbove` witnesses derived uniformly from `indicator_cov_le_one` — the
same `[0, 1]` envelope used by `alphaMixingCoeff_le_one`.

This closes the third and final order-theory ingredient flagged in the parent
`davydov_covariance_inequality` decomposition; combined with the S5 results
`alphaMixingCoeff_le_one` and `alphaMixingCoeff_nonneg`, the L^p Davydov bound
(S5c target, ~100 lines) now reduces purely to truncation + Hölder on top of
the indicator base case.

σ-algebras are passed via the `σPair : Fin 2 → MeasurableSpace Ω` function
form (cf. `alphaMixingCoeff_nonneg`, `alphaMixingCoeff_le_one`). -/
theorem davydov_indicator_bound
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {A B : Set Ω}
    (hA_meas : @MeasurableSet Ω (σPair 0) A)
    (hB_meas : @MeasurableSet Ω (σPair 1) B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤
      CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  unfold CentralLimitTheoremOQ02.alphaMixingCoeff
  -- BddAbove witness for the outer `Set Ω` layer: every term is ≤ 1, uniformly.
  have hBdd_outer :
      BddAbove (Set.range fun (A' : Set Ω) =>
        ⨆ (_ : @MeasurableSet Ω (σPair 0) A')
          (B' : Set Ω) (_ : @MeasurableSet Ω (σPair 1) B'),
          |(μ (A' ∩ B')).toReal - (μ A').toReal * (μ B').toReal|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨A', rfl⟩
    apply Real.iSup_le _ (by norm_num); intro _hA
    apply Real.iSup_le _ (by norm_num); intro B'
    apply Real.iSup_le _ (by norm_num); intro _hB
    exact indicator_cov_le_one A' B'
  -- BddAbove witness for the middle `Set Ω` layer (with A held fixed).
  have hBdd_inner :
      BddAbove (Set.range fun (B' : Set Ω) =>
        ⨆ (_ : @MeasurableSet Ω (σPair 1) B'),
          |(μ (A ∩ B')).toReal - (μ A).toReal * (μ B').toReal|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨B', rfl⟩
    apply Real.iSup_le _ (by norm_num); intro _hB
    exact indicator_cov_le_one A B'
  -- Peel the four ⨆ layers: Set Ω (outer) → Prop → Set Ω (inner) → Prop.
  refine le_ciSup_of_le hBdd_outer A ?_
  rw [ciSup_pos hA_meas]
  refine le_ciSup_of_le hBdd_inner B ?_
  rw [ciSup_pos hB_meas]
  -- After both rewrites the iSup collapses to the body, which equals the LHS.

/-! ## Part IV: Davydov's covariance inequality (S4 target, stated as sorry) -/

/-- **Indicator-pair covariance identity** (S4 stepping-stone helper).

For 0-1 indicators of measurable sets `A` and `B` in a probability space, the
covariance simplifies to a difference of joint and product measures:
$$
\int \mathbf 1_A \cdot \mathbf 1_B \, d\mu
   - \Bigl(\int \mathbf 1_A \, d\mu\Bigr) \cdot \Bigl(\int \mathbf 1_B \, d\mu\Bigr)
 = \mu(A \cap B) - \mu(A) \cdot \mu(B).
$$

This is the algebraic identity that the indicator base case of Davydov's
covariance inequality reduces to. The RHS is precisely the form bounded by
the α-mixing coefficient `alphaMixingCoeff` (defined as the supremum of `|RHS|`
over measurable pairs in the two σ-algebras), so combined with `le_ciSup`-type
reasoning, it yields the constant-1 indicator-pair Davydov bound. The
truncation + Hölder amplification step then promotes this base case to the
sharp-constant general L^p inequality with constant 12 (the S4 deliverable).

The proof is purely measure-theoretic: case analysis on `Set.indicator_apply`
identifies the pointwise product `1_A · 1_B = 1_{A ∩ B}`, then
`MeasureTheory.integral_indicator_one` evaluates each indicator integral as
`μ.real`. No supremum machinery is invoked at this layer. -/
theorem indicator_pair_covariance_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ
      - (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ)
    = μ.real (A ∩ B) - μ.real A * μ.real B := by
  have hAB : MeasurableSet (A ∩ B) := hA.inter hB
  -- Pointwise: `1_A(ω) · 1_B(ω) = 1_{A ∩ B}(ω)`, by case analysis on
  -- `Set.indicator_apply` (no nested-supremum machinery is invoked).
  have hprod :
      (fun ω : Ω => A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω)
        = (A ∩ B).indicator (1 : Ω → ℝ) := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;>
      simp [Set.mem_inter_iff, hωA, hωB]
  rw [hprod, integral_indicator_one hAB, integral_indicator_one hA,
      integral_indicator_one hB]

/-- **Indicator-pair Davydov covariance bound** (S5c-prep, this session).

Combines `indicator_pair_covariance_eq` (S4: the algebraic identity rewriting
the indicator covariance as `μ(A ∩ B) − μ(A) · μ(B)`) with
`davydov_indicator_bound` (S5b: the α-mixing bound on that measure-theoretic
difference) to package the *covariance-form* indicator bound:
$$
\Bigl|\!\int 1_A \cdot 1_B \, d\mu - \Bigl(\!\int 1_A \, d\mu\Bigr) \cdot
   \Bigl(\!\int 1_B \, d\mu\Bigr)\!\Bigr| \;\le\; \alpha(\mathcal F, \mathcal G).
$$

This is the exact form consumed by the L^p density step (S5c target): inside
the bilinear expansion of `Cov(X, Y)` over the level-set decompositions
`X = ∫₀^∞ (𝟙_{X>t} − 𝟙_{X<-t}) dt` (likewise for `Y`), this lemma supplies the
pointwise α-bound at each `(t, s)`, with the super- and sub-level sets all
σPair-measurable for the relevant sub-σ-algebras.

The bridge between `indicator_pair_covariance_eq` (whose RHS uses
`μ.real := (μ ·).toReal`) and `davydov_indicator_bound` (whose LHS uses
`(μ ·).toReal` directly) is closed by `Measure.real_def`. -/
theorem indicator_covariance_le_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {A B : Set Ω}
    (hA_amb : MeasurableSet A) (hB_amb : MeasurableSet B)
    (hA : @MeasurableSet Ω (σPair 0) A) (hB : @MeasurableSet Ω (σPair 1) B) :
    |∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ
      - (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ)|
    ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  rw [indicator_pair_covariance_eq hA_amb hB_amb]
  simp only [Measure.real_def]
  exact davydov_indicator_bound σPair hA hB

/-- **Scaled-indicator Davydov covariance bound** (S16, this session).

Promotes the unit-indicator bound `indicator_covariance_le_alpha` to arbitrary
real scalars `a, b` on each factor:
$$
\Bigl|\mathrm{Cov}\bigl(a\,\mathbf 1_A,\; b\,\mathbf 1_B\bigr)\Bigr|
   \;\le\; |a|\,|b|\;\alpha(\mathcal F, \mathcal G).
$$

The covariance is bilinear, so the scalars `a` and `b` factor straight through
both the joint integral `∫ (a 1_A)(b 1_B)` and the product of marginals
`(∫ a 1_A)(∫ b 1_B)`, leaving `a · b` times the unit-indicator covariance. Taking
absolute values and `abs_mul` splits `|a · b| = |a| · |b|`, and the unit bound
caps the remaining factor by `α`.

This is the single-cell building block of the simple-function step toward
`davydov_covariance_inequality`: a simple function measurable w.r.t. `σPair 0`
is a finite sum `∑ aᵢ 1_{Aᵢ}`, and bilinear expansion of the covariance against
`∑ bⱼ 1_{Bⱼ}` reduces to a finite sum of exactly these scaled-cell bounds (the
constant `∑|aᵢ| · ∑|bⱼ|` is then controlled by the `L^p` norms via the
level-set / Hölder amplification, the remaining S5c analytic content). -/
theorem scaled_indicator_covariance_le_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {A B : Set Ω} (a b : ℝ)
    (hA_amb : MeasurableSet A) (hB_amb : MeasurableSet B)
    (hA : @MeasurableSet Ω (σPair 0) A) (hB : @MeasurableSet Ω (σPair 1) B) :
    |∫ ω, (a * A.indicator (1 : Ω → ℝ) ω) * (b * B.indicator (1 : Ω → ℝ) ω) ∂μ
      - (∫ ω, a * A.indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, b * B.indicator (1 : Ω → ℝ) ω ∂μ)|
    ≤ |a| * |b| *
        CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  -- Pull the scalars out of the joint integral (`a · b` is a single constant).
  have hint_prod :
      ∫ ω, (a * A.indicator (1 : Ω → ℝ) ω) * (b * B.indicator (1 : Ω → ℝ) ω) ∂μ
        = (a * b) *
            ∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ := by
    have hpt :
        (fun ω : Ω => (a * A.indicator (1 : Ω → ℝ) ω) * (b * B.indicator (1 : Ω → ℝ) ω))
          = (fun ω : Ω =>
              (a * b) * (A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω)) := by
      funext ω; ring
    rw [hpt, integral_const_mul]
  -- Pull the scalars out of each marginal integral.
  have hint_A :
      ∫ ω, a * A.indicator (1 : Ω → ℝ) ω ∂μ
        = a * ∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ := integral_const_mul a _
  have hint_B :
      ∫ ω, b * B.indicator (1 : Ω → ℝ) ω ∂μ
        = b * ∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ := integral_const_mul b _
  rw [hint_prod, hint_A, hint_B]
  -- Factor `a · b` out of the whole covariance expression.
  have hfactor :
      (a * b) * (∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ)
        - (a * ∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ)
          * (b * ∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ)
        = (a * b) *
            (∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ
              - (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ)
                * (∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ)) := by ring
  rw [hfactor, abs_mul, abs_mul]
  have hbase := indicator_covariance_le_alpha (μ := μ) σPair hA_amb hB_amb hA hB
  exact mul_le_mul_of_nonneg_left hbase (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- **Simple-function Davydov covariance bound** (S17, this session).

Lifts the single-cell bound `scaled_indicator_covariance_le_alpha` to arbitrary
finite linear combinations of sub-σ-measurable indicators on each factor — i.e.
to a *pair of simple functions* `f = ∑ᵢ aᵢ 1_{Aᵢ}` (measurable w.r.t. `σPair 0`)
and `g = ∑ⱼ bⱼ 1_{Bⱼ}` (measurable w.r.t. `σPair 1`):
$$
\Bigl|\mathrm{Cov}(f, g)\Bigr|
   \;\le\; \Bigl(\sum_i |a_i|\Bigr)\Bigl(\sum_j |b_j|\Bigr)\,
     \alpha(\mathcal F, \mathcal G).
$$

**Why this is the right intermediate.** The covariance is bilinear, so expanding
`Cov(∑ᵢ aᵢ 1_{Aᵢ}, ∑ⱼ bⱼ 1_{Bⱼ})` distributes into the double sum
`∑ᵢ ∑ⱼ Cov(aᵢ 1_{Aᵢ}, bⱼ 1_{Bⱼ})` of per-cell covariances (`sum_mul_sum` on
both the joint integral — pushed through `integral_finset_sum` using
integrability of each cell — and the product of marginals). The triangle
inequality (`abs_sum_le_sum_abs`, twice) then reduces the whole bound to the
per-cell estimate `|Cov(aᵢ 1_{Aᵢ}, bⱼ 1_{Bⱼ})| ≤ |aᵢ| |bⱼ| α` supplied by
`scaled_indicator_covariance_le_alpha`, and `∑ᵢ ∑ⱼ |aᵢ| |bⱼ| = (∑ᵢ |aᵢ|)(∑ⱼ |bⱼ|)`
(`sum_mul_sum` again) collects the constant.

This is the general simple-function step gated in the S4 structural
decomposition of `davydov_covariance_inequality` (ingredient 4, the "L^p density
step"): every `σPair`-measurable simple function is exactly such a finite
indicator combination, so this lemma is the last purely-algebraic layer before
the remaining analytic content (truncation of `X, Y` to bounded simple
approximants + the Hölder amplification that turns `(∑|aᵢ|)(∑|bⱼ|)` into the
`‖X‖_{L^p} ‖Y‖_{L^p}` factor with the sharp exponent `(p-2)/p`). -/
theorem finset_indicator_covariance_le_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ)
    (A : ι → Set Ω) (B : κ → Set Ω)
    (hA_amb : ∀ i ∈ s, MeasurableSet (A i))
    (hB_amb : ∀ j ∈ t, MeasurableSet (B j))
    (hA : ∀ i ∈ s, @MeasurableSet Ω (σPair 0) (A i))
    (hB : ∀ j ∈ t, @MeasurableSet Ω (σPair 1) (B j)) :
    |∫ ω, (∑ i ∈ s, a i * (A i).indicator (1 : Ω → ℝ) ω)
            * (∑ j ∈ t, b j * (B j).indicator (1 : Ω → ℝ) ω) ∂μ
      - (∫ ω, ∑ i ∈ s, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, ∑ j ∈ t, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ)|
    ≤ (∑ i ∈ s, |a i|) * (∑ j ∈ t, |b j|)
        * CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  set α := CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) with hα
  -- Integrability of each scaled indicator on both factors.
  have hfI : ∀ i ∈ s, Integrable (fun ω => a i * (A i).indicator (1 : Ω → ℝ) ω) μ := by
    intro i hi
    exact ((integrable_const (1 : ℝ)).indicator (hA_amb i hi)).const_mul (a i)
  have hgI : ∀ j ∈ t, Integrable (fun ω => b j * (B j).indicator (1 : Ω → ℝ) ω) μ := by
    intro j hj
    exact ((integrable_const (1 : ℝ)).indicator (hB_amb j hj)).const_mul (b j)
  -- Integrability of each cell product `(aᵢ 1_{Aᵢ})(bⱼ 1_{Bⱼ}) = (aᵢbⱼ) 1_{Aᵢ∩Bⱼ}`.
  have hcellI : ∀ i ∈ s, ∀ j ∈ t,
      Integrable (fun ω => (a i * (A i).indicator (1 : Ω → ℝ) ω)
        * (b j * (B j).indicator (1 : Ω → ℝ) ω)) μ := by
    intro i hi j hj
    have hpt : (fun ω => (a i * (A i).indicator (1 : Ω → ℝ) ω)
          * (b j * (B j).indicator (1 : Ω → ℝ) ω))
        = (fun ω => (a i * b j) * (A i ∩ B j).indicator (1 : Ω → ℝ) ω) := by
      funext ω
      by_cases hωA : ω ∈ A i <;> by_cases hωB : ω ∈ B j <;>
        simp [Set.mem_inter_iff, hωA, hωB]
    rw [hpt]
    exact ((integrable_const (1 : ℝ)).indicator ((hA_amb i hi).inter (hB_amb j hj))).const_mul _
  -- Marginal integrals split over the finite sums.
  have hM1 : ∫ ω, ∑ i ∈ s, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ
      = ∑ i ∈ s, ∫ ω, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ :=
    integral_finset_sum s hfI
  have hM2 : ∫ ω, ∑ j ∈ t, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ
      = ∑ j ∈ t, ∫ ω, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ :=
    integral_finset_sum t hgI
  -- Joint integral: expand the product of sums, then split the double sum.
  have hJ : ∫ ω, (∑ i ∈ s, a i * (A i).indicator (1 : Ω → ℝ) ω)
              * (∑ j ∈ t, b j * (B j).indicator (1 : Ω → ℝ) ω) ∂μ
      = ∑ i ∈ s, ∑ j ∈ t,
          ∫ ω, (a i * (A i).indicator (1 : Ω → ℝ) ω)
            * (b j * (B j).indicator (1 : Ω → ℝ) ω) ∂μ := by
    have hpt : (fun ω => (∑ i ∈ s, a i * (A i).indicator (1 : Ω → ℝ) ω)
                * (∑ j ∈ t, b j * (B j).indicator (1 : Ω → ℝ) ω))
        = (fun ω => ∑ i ∈ s, ∑ j ∈ t,
            (a i * (A i).indicator (1 : Ω → ℝ) ω)
              * (b j * (B j).indicator (1 : Ω → ℝ) ω)) := by
      funext ω
      exact Finset.sum_mul_sum s t _ _
    rw [hpt,
      integral_finset_sum s (fun i hi =>
        integrable_finset_sum t (fun j hj => hcellI i hi j hj))]
    exact Finset.sum_congr rfl (fun i hi =>
      integral_finset_sum t (fun j hj => hcellI i hi j hj))
  -- Product of marginals as a double sum.
  have hP : (∫ ω, ∑ i ∈ s, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ)
              * (∫ ω, ∑ j ∈ t, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ)
      = ∑ i ∈ s, ∑ j ∈ t,
          (∫ ω, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ)
            * (∫ ω, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ) := by
    rw [hM1, hM2, Finset.sum_mul_sum]
  -- Assemble covariance as a double sum of per-cell covariances.
  rw [hJ, hP]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ s, ∑ j ∈ t,
        ((∫ ω, (a i * (A i).indicator (1 : Ω → ℝ) ω)
            * (b j * (B j).indicator (1 : Ω → ℝ) ω) ∂μ)
          - (∫ ω, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ)
            * (∫ ω, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ))|
        ≤ ∑ i ∈ s, |∑ j ∈ t,
            ((∫ ω, (a i * (A i).indicator (1 : Ω → ℝ) ω)
                * (b j * (B j).indicator (1 : Ω → ℝ) ω) ∂μ)
              - (∫ ω, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ)
                * (∫ ω, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ t,
            |(∫ ω, (a i * (A i).indicator (1 : Ω → ℝ) ω)
                * (b j * (B j).indicator (1 : Ω → ℝ) ω) ∂μ)
              - (∫ ω, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ)
                * (∫ ω, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ)| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, |a i| * |b j| * α :=
        Finset.sum_le_sum (fun i hi =>
          Finset.sum_le_sum (fun j hj =>
            scaled_indicator_covariance_le_alpha (μ := μ) σPair (a i) (b j)
              (hA_amb i hi) (hB_amb j hj) (hA i hi) (hB j hj)))
    _ = (∑ i ∈ s, |a i|) * (∑ j ∈ t, |b j|) * α := by
        rw [Finset.sum_mul_sum]
        simp_rw [Finset.sum_mul]

/-- **Nonnegative-coefficient simple-function Davydov bound** (S20, this session).

Specialization of `finset_indicator_covariance_le_alpha` to the case where every
cell weight is nonnegative (`0 ≤ aᵢ`, `0 ≤ bⱼ`). The absolute values in the
constant then collapse — `∑ᵢ |aᵢ| = ∑ᵢ aᵢ` and `∑ⱼ |bⱼ| = ∑ⱼ bⱼ` — so the
bound reads with the plain coefficient sums:
$$
\Bigl|\mathrm{Cov}(f, g)\Bigr|
   \;\le\; \Bigl(\sum_i a_i\Bigr)\Bigl(\sum_j b_j\Bigr)\,
     \alpha(\mathcal F, \mathcal G).
$$

**Why this is the right increment.** The super-level (layer-cake) decomposition
of a *nonnegative* bounded variable carries only nonnegative weights, so this is
exactly the form the Davydov density step produces once the signed variable has
been shifted to `[0, M]` (via `covariance_add_const_left/right`, S19). Removing
the absolute values is what lets the coefficient sum *telescope to the range* of
the function — the content of `telescoping_layer_covariance_le_alpha` below —
rather than growing without bound as the partition is refined. -/
theorem finset_indicator_covariance_le_alpha_of_nonneg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ)
    (A : ι → Set Ω) (B : κ → Set Ω)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ j ∈ t, 0 ≤ b j)
    (hA_amb : ∀ i ∈ s, MeasurableSet (A i))
    (hB_amb : ∀ j ∈ t, MeasurableSet (B j))
    (hA : ∀ i ∈ s, @MeasurableSet Ω (σPair 0) (A i))
    (hB : ∀ j ∈ t, @MeasurableSet Ω (σPair 1) (B j)) :
    |∫ ω, (∑ i ∈ s, a i * (A i).indicator (1 : Ω → ℝ) ω)
            * (∑ j ∈ t, b j * (B j).indicator (1 : Ω → ℝ) ω) ∂μ
      - (∫ ω, ∑ i ∈ s, a i * (A i).indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, ∑ j ∈ t, b j * (B j).indicator (1 : Ω → ℝ) ω ∂μ)|
    ≤ (∑ i ∈ s, a i) * (∑ j ∈ t, b j)
        * CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  have hbase := finset_indicator_covariance_le_alpha (μ := μ) σPair s t a b A B
    hA_amb hB_amb hA hB
  have hsa : ∑ i ∈ s, |a i| = ∑ i ∈ s, a i :=
    Finset.sum_congr rfl (fun i hi => abs_of_nonneg (ha i hi))
  have hsb : ∑ j ∈ t, |b j| = ∑ j ∈ t, b j :=
    Finset.sum_congr rfl (fun j hj => abs_of_nonneg (hb j hj))
  rwa [hsa, hsb] at hbase

/-- **Telescoping layer-cake Davydov bound** (S20, this session).

The discretized layer-cake step of Davydov's inequality for *bounded* variables.
Given increasing grids `sg, ug : ℕ → ℝ` with `sg 0 = 0`, `sg m = M`, `ug 0 = 0`,
`ug n = N`, form the super-level step approximants with telescoping weights
`sg (k+1) − sg k ≥ 0` and `ug (k+1) − ug k ≥ 0` attached to sub-σ-measurable
level sets `A k` (w.r.t. `σPair 0`) and `B k` (w.r.t. `σPair 1`). Then
$$
\Bigl|\mathrm{Cov}(f_{\mathrm{step}}, g_{\mathrm{step}})\Bigr|
   \;\le\; M \cdot N \cdot \alpha(\mathcal F, \mathcal G).
$$

**The point.** The coefficient sums telescope to the ranges by
`Finset.sum_range_sub`:
`∑_{k<m} (sg (k+1) − sg k) = sg m − sg 0 = M` (and likewise `N`), *independently
of the grid* `sg`. Refining the partition therefore does **not** inflate the
constant — it stays pinned at `M · N`. This is precisely the uniform bound that
survives the layer-cake limit and turns the `(∑|aᵢ|)(∑|bⱼ|)` simple-function
estimate into the sharp `‖X‖_∞ ‖Y‖_∞`-type factor of the bounded-variable
Davydov inequality. The nonnegativity of the weights (needed to drop the
absolute values, `finset_indicator_covariance_le_alpha_of_nonneg`) is exactly
what makes the telescoping legitimate; a signed decomposition would give
`∑|Δ|`, not `∑ Δ`.

Combined with the constant-shift invariance of S19 (which reduces a signed
`f ∈ [m, M]` to the nonnegative `f − m ∈ [0, M − m]`), this is the final
*algebraic* layer of `davydov_covariance_inequality`; the residual content is
the analytic passage from step functions to general bounded/`L^p` variables
(monotone convergence for the layer-cake limit + Hölder amplification to the
`(p−2)/p` exponent). -/
theorem telescoping_layer_covariance_le_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    (m n : ℕ) (sg ug : ℕ → ℝ) (M N : ℝ)
    (A : ℕ → Set Ω) (B : ℕ → Set Ω)
    (hsg_mono : Monotone sg) (hug_mono : Monotone ug)
    (hsg0 : sg 0 = 0) (hsgm : sg m = M)
    (hug0 : ug 0 = 0) (hugn : ug n = N)
    (hA_amb : ∀ k ∈ Finset.range m, MeasurableSet (A k))
    (hB_amb : ∀ k ∈ Finset.range n, MeasurableSet (B k))
    (hA : ∀ k ∈ Finset.range m, @MeasurableSet Ω (σPair 0) (A k))
    (hB : ∀ k ∈ Finset.range n, @MeasurableSet Ω (σPair 1) (B k)) :
    |∫ ω, (∑ k ∈ Finset.range m, (sg (k + 1) - sg k) * (A k).indicator (1 : Ω → ℝ) ω)
            * (∑ k ∈ Finset.range n, (ug (k + 1) - ug k) * (B k).indicator (1 : Ω → ℝ) ω) ∂μ
      - (∫ ω, ∑ k ∈ Finset.range m, (sg (k + 1) - sg k) * (A k).indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, ∑ k ∈ Finset.range n, (ug (k + 1) - ug k) * (B k).indicator (1 : Ω → ℝ) ω ∂μ)|
    ≤ M * N * CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  -- Telescoping weights are nonnegative (grids are monotone).
  have ha : ∀ k ∈ Finset.range m, 0 ≤ sg (k + 1) - sg k := fun k _ =>
    sub_nonneg.mpr (hsg_mono (Nat.le_succ k))
  have hb : ∀ k ∈ Finset.range n, 0 ≤ ug (k + 1) - ug k := fun k _ =>
    sub_nonneg.mpr (hug_mono (Nat.le_succ k))
  -- Apply the nonnegative-coefficient simple-function bound.
  have hbound := finset_indicator_covariance_le_alpha_of_nonneg (μ := μ) σPair
    (Finset.range m) (Finset.range n)
    (fun k => sg (k + 1) - sg k) (fun k => ug (k + 1) - ug k) A B ha hb
    hA_amb hB_amb hA hB
  -- The coefficient sums telescope to the ranges `M`, `N`.
  have hSsum : ∑ k ∈ Finset.range m, (sg (k + 1) - sg k) = M := by
    rw [Finset.sum_range_sub sg m, hsgm, hsg0, sub_zero]
  have hUsum : ∑ k ∈ Finset.range n, (ug (k + 1) - ug k) = N := by
    rw [Finset.sum_range_sub ug n, hugn, hug0, sub_zero]
  rwa [hSsum, hUsum] at hbound

/-! ### Covariance translation-invariance (S19 — algebraic reduction for the
     L^p density step)

The Davydov density step (`davydov_covariance_inequality`, S5c) reduces a
signed bounded variable `f` with values in `[m, M]` to the *nonnegative* shift
`f − m ∈ [0, M − m]`, which is the form required by the layer-cake /
super-level indicator decomposition `f − m = ∫₀^{M−m} 1_{f − m > t} dt`. That
reduction is legitimate precisely because covariance is unchanged when a
constant is added to either argument:
`Cov(f + c, g) = Cov(f, g)` and `Cov(f, g + c) = Cov(f, g)`.

Both identities are pure linearity of the Bochner integral together with
`∫ c ∂μ = c` on a probability measure; they carry no assumption beyond
integrability of `f`, `g`, and the product `f · g`. -/

/-- **Covariance is invariant under adding a constant to the left argument.**

`Cov(f + c, g) = Cov(f, g)`, where covariance is written in the explicit form
`∫ f·g − (∫ f)(∫ g)` used throughout this file. The proof splits the joint
integral `∫ (f + c)·g = ∫ f·g + c ∫ g` and the marginal `∫ (f + c) = ∫ f + c`
(using `IsProbabilityMeasure μ`, so `∫ c ∂μ = c`); the two `c ∫ g` terms then
cancel. This is the algebraic reduction that lets the Davydov density step
replace a bounded `f ∈ [m, M]` by the nonnegative shift `f − m`. -/
theorem covariance_add_const_left
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (c : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    (∫ ω, (f ω + c) * g ω ∂μ) - (∫ ω, (f ω + c) ∂μ) * (∫ ω, g ω ∂μ)
      = (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ) := by
  have hcg : Integrable (fun ω => c * g ω) μ := hg.const_mul c
  -- Joint integral splits: `∫ (f + c)·g = ∫ f·g + c ∫ g`.
  have hjoint : (∫ ω, (f ω + c) * g ω ∂μ)
      = (∫ ω, f ω * g ω ∂μ) + c * ∫ ω, g ω ∂μ := by
    have hpt : (fun ω => (f ω + c) * g ω) = (fun ω => f ω * g ω + c * g ω) := by
      funext ω; ring
    rw [hpt, integral_add hfg hcg, integral_const_mul]
  -- Marginal integral splits: `∫ (f + c) = ∫ f + c` (probability measure).
  have hmarg : (∫ ω, (f ω + c) ∂μ) = (∫ ω, f ω ∂μ) + c := by
    rw [integral_add hf (integrable_const c), integral_const]; simp
  rw [hjoint, hmarg]; ring

/-- **Covariance is invariant under adding a constant to the right argument.**

`Cov(f, g + c) = Cov(f, g)`, the right-hand companion of
`covariance_add_const_left`. Proved analogously by splitting the joint integral
`∫ f·(g + c) = ∫ f·g + c ∫ f` and the marginal `∫ (g + c) = ∫ g + c`. -/
theorem covariance_add_const_right
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (c : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    (∫ ω, f ω * (g ω + c) ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, (g ω + c) ∂μ)
      = (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ) := by
  have hcf : Integrable (fun ω => c * f ω) μ := hf.const_mul c
  -- Joint integral splits: `∫ f·(g + c) = ∫ f·g + c ∫ f`.
  have hjoint : (∫ ω, f ω * (g ω + c) ∂μ)
      = (∫ ω, f ω * g ω ∂μ) + c * ∫ ω, f ω ∂μ := by
    have hpt : (fun ω => f ω * (g ω + c)) = (fun ω => f ω * g ω + c * f ω) := by
      funext ω; ring
    rw [hpt, integral_add hfg hcf, integral_const_mul]
  -- Marginal integral splits: `∫ (g + c) = ∫ g + c` (probability measure).
  have hmarg : (∫ ω, (g ω + c) ∂μ) = (∫ ω, g ω ∂μ) + c := by
    rw [integral_add hg (integrable_const c), integral_const]; simp
  rw [hjoint, hmarg]; ring

/-! ### Layer-cake primitives (S21 — analytic reduction for the L^p density step)

The remaining content of `davydov_covariance_inequality` after the S16–S20
*algebraic* layers (scaled-cell → simple-function → telescoping-step bound, plus
the S19 constant-shift reduction to nonnegative variables) is the *analytic*
passage from step functions to a general bounded nonnegative variable. That
passage rests on the **layer-cake identity**: a nonnegative `x ∈ [0, M]` is the
Lebesgue integral of its super-level indicators,
`x = ∫₀^M 𝟙_{t < x} dt`. Fed pointwise at `x = f ω` and integrated in `ω`
(Fubini), this rewrites `Cov(f, g)` as a double `t`-integral of the *indicator*
covariances `Cov(𝟙_{f > s}, 𝟙_{g > t})`, each of which is already bounded by
`α` via `indicator_covariance_le_alpha` — provided the super-level sets are
measurable in the respective sub-σ-algebras (`superlevel_setOf_measurable`). -/

/-- **Pointwise layer-cake identity.** For `0 ≤ x ≤ M`, the super-level
indicator `t ↦ 𝟙_{t < x}` integrates to `x` over `[0, M]`:
`∫₀^M 𝟙_{t < x} dt = x`. The integrand is (a.e.) the indicator of `Iio x`, so
the interval integral equals `volume (Ioc 0 M ∩ Iio x) = volume (Ioo 0 x) = x`
(the last step uses `0 ≤ x` and `x ≤ M`). This is the elementary atom of the
layer-cake representation used in the analytic (`L^p` density) step of Davydov's
inequality. -/
theorem layer_cake_pointwise {x M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) :
    ∫ t in (0:ℝ)..M, (if t < x then (1:ℝ) else 0) = x := by
  have hind : (fun t : ℝ => if t < x then (1:ℝ) else 0)
      = (Set.Iio x).indicator (fun _ => (1:ℝ)) := by
    funext t; simp [Set.indicator_apply, Set.mem_Iio]
  rw [hind, intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ M),
    MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioc 0 M ∩ Set.Iio x = Set.Ioo 0 x := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h0, _⟩, hx'⟩; exact ⟨h0, hx'⟩
    · rintro ⟨h0, hx'⟩; exact ⟨⟨h0, by linarith⟩, hx'⟩
  rw [hset, MeasureTheory.setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  rw [MeasureTheory.measureReal_def, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hx]

/-- **Layer-cake representation** (`x = ∫₀^M 𝟙_{t < x} dt` for `0 ≤ x ≤ M`).

The `.symm` orientation of `layer_cake_pointwise`, stated as a rewrite that
replaces a bounded nonnegative scalar by its super-level integral. This is the
form consumed by the analytic step: apply at `x = f ω` for a nonnegative
`f ≤ M`, then Fubini-swap the `ω`- and `t`-integrals to expose the indicator
covariances. -/
theorem layer_cake_repr {x M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) :
    x = ∫ t in (0:ℝ)..M, (if t < x then (1:ℝ) else 0) :=
  (layer_cake_pointwise hx hxM).symm

/-- **Pointwise product layer-cake identity.** For `0 ≤ x ≤ M` and `0 ≤ y ≤ N`,
the product `x · y` is the double super-level integral
`∫₀^M ∫₀^N 𝟙_{s < x} · 𝟙_{t < y} dt ds`.

This is the *pointwise* (per-`ω`) input to the analytic step of Davydov's
inequality applied at `x = f ω`, `y = g ω`: it isolates the nested
interval-integral algebra (`intervalIntegral.integral_const_mul` /
`integral_mul_const` peel one indicator factor at a time, each collapsed by
`layer_cake_pointwise`), leaving only the measure-theoretic Fubini swap of the
`ω`-integral against the product `[0,M]×[0,N]` for the S22 covariance
representation `Cov(f,g) = ∫∫ Cov(𝟙_{f>s}, 𝟙_{g>t}) ds dt`. -/
theorem layer_cake_pointwise_prod {x y M N : ℝ}
    (hx : 0 ≤ x) (hxM : x ≤ M) (hy : 0 ≤ y) (hyN : y ≤ N) :
    x * y = ∫ s in (0:ℝ)..M, ∫ t in (0:ℝ)..N,
      (if s < x then (1:ℝ) else 0) * (if t < y then (1:ℝ) else 0) := by
  have hinner : ∀ s : ℝ, (∫ t in (0:ℝ)..N,
      (if s < x then (1:ℝ) else 0) * (if t < y then (1:ℝ) else 0))
      = (if s < x then (1:ℝ) else 0) * y := by
    intro s
    rw [intervalIntegral.integral_const_mul, layer_cake_pointwise hy hyN]
  simp_rw [hinner]
  rw [intervalIntegral.integral_mul_const, layer_cake_pointwise hx hxM]

omit [MeasurableSpace Ω] in
/-- **Super-level sets are sub-σ-measurable.** If `X` is measurable w.r.t. a
σ-algebra `m`, then every super-level set `{ω | t < X ω}` is `m`-measurable.

This is the measurability hypothesis needed to feed the layer-cake indicators
`𝟙_{X > t}` into `indicator_covariance_le_alpha`: the σ-algebra requirements
`@MeasurableSet Ω (σPair 0) A` / `@MeasurableSet Ω (σPair 1) B` of the indicator
covariance bound are discharged for `A = {X > s}`, `B = {Y > t}` exactly when
`X`, `Y` are measurable w.r.t. `σPair 0`, `σPair 1` respectively. -/
theorem superlevel_setOf_measurable {m : MeasurableSpace Ω}
    {X : Ω → ℝ} (hX : Measurable[m] X) (t : ℝ) :
    @MeasurableSet Ω m {ω | t < X ω} :=
  measurableSet_lt measurable_const hX

/-- **Mean survival representation over `Ioc 0 M`** (strict-`<` layer cake for a
bounded nonnegative random variable). For an integrable `f` with `0 ≤ f ≤ M`
(a.e.), the expectation is the integral of the *super-level* (survival)
probability over `(0, M]`:
`∫ f = ∫_{(0,M]} μ.real {ω | t < f ω} dt`.

Mathlib's `Integrable.integral_eq_integral_meas_lt` gives the tail integral over
the whole ray `Ioi 0` (Cavalieri's principle); the boundedness `f ≤ M` collapses
the survival probability to `0` for `t > M`, so the integral may be restricted to
`Ioc 0 M` (via `setIntegral_eq_of_subset_of_ae_diff_eq_zero`). The strict `<`
convention matches the super-level indicators `𝟙_{t < f}` of
`superlevel_setOf_measurable` used in the Davydov density step (S5c), and the
finite window `(0, M]` is exactly the interval range appearing in
`layer_cake_pointwise`. -/
theorem mean_eq_survival_lt_Ioc
    {μ : Measure Ω} {f : Ω → ℝ} {M : ℝ}
    (hf_int : Integrable f μ) (hf_nn : 0 ≤ᵐ[μ] f)
    (hf_bdd : f ≤ᵐ[μ] (fun _ => M)) :
    ∫ ω, f ω ∂μ = ∫ t in Set.Ioc 0 M, μ.real {ω | t < f ω} := by
  rw [MeasureTheory.Integrable.integral_eq_integral_meas_lt hf_int hf_nn]
  rw [setIntegral_eq_of_subset_of_ae_diff_eq_zero
      nullMeasurableSet_Ioi Set.Ioc_subset_Ioi_self ?_]
  apply Filter.Eventually.of_forall (fun t ht => ?_)
  have htM : M < t := by
    simp_all only [Set.mem_diff, Set.mem_Ioi, Set.mem_Ioc, not_and, not_le]
  have obs : μ {ω | M < f ω} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hf_bdd] with a ha using not_lt.mpr ha
  rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
  exact Or.inl <| measure_mono_null (fun a ha => lt_trans htM ha) obs

/-- **Product of marginals as a separable double survival integral.** For two
bounded nonnegative integrable random variables `f ∈ [0, M]`, `g ∈ [0, N]`
(a.e.), the product of the means factors through the survival functions:
`(∫ f)(∫ g) = ∫_{(0,M]} ∫_{(0,N]} μ.real{t < f} · μ.real{s < g} ds dt`.

This is the *product-of-marginals* half of the covariance layer-cake
representation `Cov(f,g) = ∫∫ Cov(𝟙_{f>t}, 𝟙_{g>s}) ds dt`. Because the
integrand factorizes as `A(t)·B(s)` with `A(t) = μ.real{t < f}` independent of
`s` and `B(s) = μ.real{s < g}` independent of `t`, no product-measure Fubini is
needed: the constants pull out of each 1-D integral (`integral_const_mul` inner,
`integral_mul_const` outer) and the double integral collapses to the product of
the two single survival integrals, each rewritten by `mean_eq_survival_lt_Ioc`.
The remaining joint term `∫ f·g = ∫∫ μ.real{t < f ∧ s < g}` (the genuine
bivariate layer cake, requiring the `Ω × [0,M] × [0,N]` Fubini swap) is deferred
to a later session; subtracting the two yields the covariance representation. -/
theorem mean_prod_eq_double_survival_lt_Ioc
    {μ : Measure Ω} {f g : Ω → ℝ} {M N : ℝ}
    (hf_int : Integrable f μ) (hf_nn : 0 ≤ᵐ[μ] f) (hf_bdd : f ≤ᵐ[μ] (fun _ => M))
    (hg_int : Integrable g μ) (hg_nn : 0 ≤ᵐ[μ] g) (hg_bdd : g ≤ᵐ[μ] (fun _ => N)) :
    (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)
      = ∫ t in Set.Ioc 0 M, ∫ s in Set.Ioc 0 N,
          μ.real {ω | t < f ω} * μ.real {ω | s < g ω} := by
  rw [mean_eq_survival_lt_Ioc hf_int hf_nn hf_bdd,
      mean_eq_survival_lt_Ioc hg_int hg_nn hg_bdd]
  simp_rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_mul_const]

/-- **Bounded layer-cake atom over `Ioc`.** The `Set.Ioc`-restricted companion of
`layer_cake_pointwise`: for `0 ≤ x ≤ M`, `∫_{(0,M]} 𝟙_{t < x} dt = x`. Identical
value to the interval-integral form (`intervalIntegral.integral_of_le` identifies
`∫ t in 0..M` with `∫ t in Set.Ioc 0 M` since `0 ≤ M`), but stated over the
`setIntegral`/`Measure.restrict` measure so it can be applied *inside* the Fubini
swap of `mean_mul_eq_double_joint_survival_lt_Ioc`, where the interval variable
lives against `volume.restrict (Set.Ioc 0 M)`. -/
theorem layer_cake_pointwise_Ioc {x M : ℝ} (hx : 0 ≤ x) (hxM : x ≤ M) :
    ∫ t in Set.Ioc 0 M, (if t < x then (1:ℝ) else 0) = x := by
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ M by linarith)]
  exact layer_cake_pointwise hx hxM

/-- **Joint bivariate layer-cake representation of `∫ f·g`** (S23, this session).
For two bounded nonnegative integrable random variables `f ∈ [0, M]`, `g ∈ [0, N]`
(a.e.), the mean of the product is the double integral of the *joint* survival
probability:
`∫ f·g = ∫_{(0,M]} ∫_{(0,N]} μ.real {ω | t < f ω ∧ s < g ω} ds dt`.

This is the *joint* half of the covariance layer-cake representation, the genuine
bivariate term deferred by `mean_prod_eq_double_survival_lt_Ioc`. Subtracting the
product-of-marginals half (S22) yields
`Cov(f,g) = ∫∫ (μ.real{t<f ∧ s<g} - μ.real{t<f}·μ.real{s<g}) ds dt
          = ∫∫ Cov(𝟙_{f>t}, 𝟙_{g>s}) ds dt`,
the representation feeding the indicator covariance bound
`indicator_covariance_le_alpha` in the `L^p` density step of Davydov's inequality.

**Proof.** The inner `s`-integral collapses without a product-measure Fubini: at
fixed `t`, `{ω | t < f ω ∧ s < g ω} = {ω | s < g ω} ∩ {ω | t < f ω}`, so its
survival probability is `(μ.restrict {t < f}).real {s < g}`, and
`mean_eq_survival_lt_Ioc` applied to the finite measure `μ.restrict {t < f}` turns
`∫_{(0,N]} (μ.restrict {t<f}).real {s<g} ds` into `∫_{{t<f}} g = ∫ g·𝟙_{t<f}`.
The remaining single `t`-integral is swapped against the `ω`-integral by Fubini
(`integral_integral_swap`; the integrand `(ω,t) ↦ g ω · 𝟙_{t<f ω}` is dominated
in norm by `‖g ∘ Prod.fst‖`, integrable on `μ ⊗ volume|_{(0,M]}` via
`Integrable.comp_fst` since `volume (Ioc 0 M) < ∞`), collapsing via the pointwise
atom `layer_cake_pointwise_Ioc` to `∫ g·f = ∫ f·g`. -/
theorem mean_mul_eq_double_joint_survival_lt_Ioc
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ} {M N : ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (_hf_int : Integrable f μ) (hf_nn : 0 ≤ᵐ[μ] f) (hf_bdd : f ≤ᵐ[μ] (fun _ => M))
    (hg_int : Integrable g μ) (hg_nn : 0 ≤ᵐ[μ] g) (hg_bdd : g ≤ᵐ[μ] (fun _ => N)) :
    ∫ ω, f ω * g ω ∂μ
      = ∫ t in Set.Ioc 0 M, ∫ s in Set.Ioc 0 N,
          μ.real {ω | t < f ω ∧ s < g ω} := by
  -- Inner `s`-integral collapse via `mean_eq_survival_lt_Ioc` on `μ.restrict {t<f}`.
  have hcollapse : ∀ t : ℝ,
      (∫ s in Set.Ioc 0 N, μ.real {ω | t < f ω ∧ s < g ω})
        = ∫ ω, g ω * (if t < f ω then (1:ℝ) else 0) ∂μ := by
    intro t
    have hB : MeasurableSet {ω | t < f ω} := measurableSet_lt measurable_const hf_meas
    have hrw : ∀ s : ℝ, μ.real {ω | t < f ω ∧ s < g ω}
        = (μ.restrict {ω | t < f ω}).real {ω | s < g ω} := by
      intro s
      have hset : {ω | t < f ω ∧ s < g ω} = {ω | s < g ω} ∩ {ω | t < f ω} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        exact and_comm
      rw [hset, measureReal_def, measureReal_def,
          Measure.restrict_apply (measurableSet_lt measurable_const hg_meas)]
    simp_rw [hrw]
    rw [← mean_eq_survival_lt_Ioc hg_int.restrict (ae_restrict_of_ae hg_nn)
          (ae_restrict_of_ae hg_bdd), ← MeasureTheory.integral_indicator hB]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    by_cases h : t < f ω <;> simp [h]
  -- Product-measure integrability of the swapped integrand.
  haveI hνfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) M)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hmeas : Measurable
      (Function.uncurry (fun (ω : Ω) (t : ℝ) => g ω * (if t < f ω then (1:ℝ) else 0))) := by
    have h1 : Measurable (fun z : Ω × ℝ => g z.1) := hg_meas.comp measurable_fst
    have hset : MeasurableSet {z : Ω × ℝ | z.2 < f z.1} :=
      measurableSet_lt measurable_snd (hf_meas.comp measurable_fst)
    have h2 : Measurable (fun z : Ω × ℝ => if z.2 < f z.1 then (1:ℝ) else 0) :=
      Measurable.ite hset measurable_const measurable_const
    exact h1.mul h2
  have hInt : Integrable
      (Function.uncurry (fun (ω : Ω) (t : ℝ) => g ω * (if t < f ω then (1:ℝ) else 0)))
      (μ.prod (volume.restrict (Set.Ioc (0:ℝ) M))) := by
    have hgfst : Integrable (fun z : Ω × ℝ => g z.1)
        (μ.prod (volume.restrict (Set.Ioc (0:ℝ) M))) :=
      hg_int.comp_fst (volume.restrict (Set.Ioc (0:ℝ) M))
    refine hgfst.norm.mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => ?_))
    show ‖g z.1 * (if z.2 < f z.1 then (1:ℝ) else 0)‖ ≤ ‖g z.1‖
    rw [norm_mul]
    have hind : ‖(if z.2 < f z.1 then (1:ℝ) else 0)‖ ≤ 1 := by
      by_cases h : z.2 < f z.1 <;> simp [h]
    calc ‖g z.1‖ * ‖(if z.2 < f z.1 then (1:ℝ) else 0)‖
        ≤ ‖g z.1‖ * 1 := by gcongr
      _ = ‖g z.1‖ := mul_one _
  -- Assemble: rewrite inner integral, Fubini swap, collapse outer integral.
  symm
  calc (∫ t in Set.Ioc 0 M, ∫ s in Set.Ioc 0 N, μ.real {ω | t < f ω ∧ s < g ω})
      = ∫ t in Set.Ioc 0 M, ∫ ω, g ω * (if t < f ω then (1:ℝ) else 0) ∂μ := by
        simp_rw [hcollapse]
    _ = ∫ ω, (∫ t in Set.Ioc 0 M, g ω * (if t < f ω then (1:ℝ) else 0)) ∂μ :=
        (integral_integral_swap hInt).symm
    _ = ∫ ω, g ω * f ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hf_nn, hf_bdd] with ω hω_nn hω_bd
        rw [MeasureTheory.integral_const_mul, layer_cake_pointwise_Ioc hω_nn hω_bd]
    _ = ∫ ω, f ω * g ω ∂μ := by simp_rw [mul_comm]

/-- **Survival-function integrability atom** (S24, this session). For a finite
measure `μ` on `Ω`, the real-valued survival function
`t ↦ μ.real {ω | t < f ω}` is Lebesgue-integrable over any finite window
`(0, M]` of the threshold variable `t`.

The survival function is *antitone* in `t` (a larger threshold carves out a
smaller super-level set `{ω | t < f ω}`, whose measure is therefore no larger),
hence measurable via `Antitone.measurable`; and it is uniformly bounded above by
`μ.real univ < ∞` (finiteness) and below by `0` (`measureReal_nonneg`). A bounded
measurable function on the finite-measure interval `(0, M]` is integrable
(`Measure.integrableOn_of_bounded`). No measurability of `f` is needed —
`measure_mono` acts on the outer measure. This mirrors the survival-integrability
step inside Mathlib's `BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt`.

**Role.** This is the reusable atom that discharges the survival-integrand
side-conditions of the covariance layer-cake representation
`covariance_eq_double_survival_covariance`: the product inner integrand
`μ.real{t<f} · μ.real{s<g}` is a constant multiple of a survival function
(`Integrable.const_mul`), and the joint inner integrand
`μ.real{t<f ∧ s<g} = (μ.restrict {t<f}).real{s<g}` is the survival function for
the restricted finite measure `μ.restrict {t<f}`. -/
theorem survival_lt_integrableOn_Ioc
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Ω → ℝ) (M : ℝ) :
    IntegrableOn (fun t => μ.real {ω | t < f ω}) (Set.Ioc 0 M) := by
  apply Measure.integrableOn_of_bounded (M := μ.real Set.univ) measure_Ioc_lt_top.ne
  · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
    exact fun _ _ hst => measure_mono (fun _ h => hst.trans_lt h)
  · apply Filter.Eventually.of_forall (fun t => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_mono (Set.subset_univ _)

/-- **Covariance layer-cake representation** (S24, this session). For two bounded
nonnegative integrable random variables `f ∈ [0, M]`, `g ∈ [0, N]` (a.e.), the
covariance is the double integral over the threshold window `(0,M] × (0,N]` of the
*indicator covariance* `Cov(𝟙_{f>t}, 𝟙_{g>s}) = μ{t<f ∧ s<g} - μ{t<f}·μ{s<g}`:
$$
  \mathrm{Cov}(f, g)
    = \int_0^M \!\!\int_0^N
        \big(\mu\{t<f \wedge s<g\} - \mu\{t<f\}\,\mu\{s<g\}\big)\, ds\, dt.
$$

This is the assembly the S22/S23 docstrings flagged as "subtracting the two
halves yields the covariance representation": the joint half
(`mean_mul_eq_double_joint_survival_lt_Ioc`, S23) gives `∫ f·g`, the
product-of-marginals half (`mean_prod_eq_double_survival_lt_Ioc`, S22) gives
`(∫ f)(∫ g)`, and linearity of the (set) integral (`integral_sub`, applied once
on the outer `t`-integral and once inside on the `s`-integral) combines the two
double integrals into a single double integral of the pointwise difference.

The four survival integrabilities required by `integral_sub` split into two
*inner* ones — discharged here via the `survival_lt_integrableOn_Ioc` atom (the
product integrand is a constant multiple of a survival function; the joint
integrand is a survival function for the restricted measure `μ.restrict {t<f}`)
— and two *outer* ones, taken as hypotheses `h_joint_outer` / `h_prod_outer`
(each follows from the atom via `integral_const_mul` for the product and via the
antitonicity of the collapsed `t ↦ ∫_{t<f} g` for the joint; deferred to keep
this assembly leaf-clean).

This representation feeds `indicator_covariance_le_alpha` — each integrand
`Cov(𝟙_{f>t}, 𝟙_{g>s})` is bounded in absolute value by the α-mixing coefficient
— in the `L^p` density (`S5c`) step of `davydov_covariance_inequality`. -/
theorem covariance_eq_double_survival_covariance
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f g : Ω → ℝ} {M N : ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f μ) (hf_nn : 0 ≤ᵐ[μ] f) (hf_bdd : f ≤ᵐ[μ] (fun _ => M))
    (hg_int : Integrable g μ) (hg_nn : 0 ≤ᵐ[μ] g) (hg_bdd : g ≤ᵐ[μ] (fun _ => N))
    (h_joint_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 N, μ.real {ω | t < f ω ∧ s < g ω}) (Set.Ioc 0 M))
    (h_prod_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 N, μ.real {ω | t < f ω} * μ.real {ω | s < g ω})
      (Set.Ioc 0 M)) :
    (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)
      = ∫ t in Set.Ioc 0 M, ∫ s in Set.Ioc 0 N,
          (μ.real {ω | t < f ω ∧ s < g ω}
            - μ.real {ω | t < f ω} * μ.real {ω | s < g ω}) := by
  -- Inner integrabilities from the survival atom.
  have h_prod_inner : ∀ t : ℝ, IntegrableOn
      (fun s => μ.real {ω | t < f ω} * μ.real {ω | s < g ω}) (Set.Ioc 0 N) :=
    fun t => (survival_lt_integrableOn_Ioc g N).const_mul (μ.real {ω | t < f ω})
  have h_joint_inner : ∀ t : ℝ, IntegrableOn
      (fun s => μ.real {ω | t < f ω ∧ s < g ω}) (Set.Ioc 0 N) := by
    intro t
    haveI : IsFiniteMeasure (μ.restrict {ω | t < f ω}) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_lt_top μ _⟩
    refine (survival_lt_integrableOn_Ioc (μ := μ.restrict {ω | t < f ω}) g N).congr_fun
      (fun s _ => ?_) measurableSet_Ioc
    have hset : {ω | t < f ω ∧ s < g ω} = {ω | s < g ω} ∩ {ω | t < f ω} := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; exact and_comm
    rw [hset, measureReal_def, measureReal_def,
        Measure.restrict_apply (measurableSet_lt measurable_const hg_meas)]
  -- Assemble: rewrite both halves, then combine the two double integrals via
  -- linearity of the integral (outer once, inner pointwise).
  rw [mean_mul_eq_double_joint_survival_lt_Ioc hf_meas hg_meas hf_int hf_nn hf_bdd
        hg_int hg_nn hg_bdd,
      mean_prod_eq_double_survival_lt_Ioc hf_int hf_nn hf_bdd hg_int hg_nn hg_bdd,
      ← integral_sub h_joint_outer h_prod_outer]
  refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
  exact (integral_sub (h_joint_inner t) (h_prod_inner t)).symm

/-- **Survival-covariance integrand α-bound** (S25, this session).

The integrand of the covariance layer-cake representation
`covariance_eq_double_survival_covariance` is, at every threshold pair `(t, s)`,
the *indicator covariance* of the super-level sets `{t < f}` and `{s < g}`:
$$
  \mu\{t<f \wedge s<g\} - \mu\{t<f\}\,\mu\{s<g\}
    = \mathrm{Cov}\bigl(\mathbf 1_{\{t<f\}},\, \mathbf 1_{\{s<g\}}\bigr).
$$
When `f` is `σPair 0`-measurable and `g` is `σPair 1`-measurable, this is
bounded in absolute value by the α-mixing coefficient, *uniformly in* `(t, s)`:
$$
  \bigl|\mu\{t<f \wedge s<g\} - \mu\{t<f\}\,\mu\{s<g\}\bigr|
    \;\le\; \alpha(\mathcal F, \mathcal G).
$$

**Proof.** The joint super-level set factors as an intersection,
`{ω | t < f ω ∧ s < g ω} = {ω | t < f ω} ∩ {ω | s < g ω}`, so after unfolding
`μ.real` as `(μ ·).toReal` the integrand is exactly the quantity bounded by
`davydov_indicator_bound`. The two sub-σ measurability side-conditions are
supplied by `superlevel_setOf_measurable` (the super-level set of an
`m`-measurable function is `m`-measurable).

**Role.** This is the pointwise majorant that turns the double survival integral
of `covariance_eq_double_survival_covariance` into the bounded-variable Davydov
estimate `|Cov(f, g)| ≤ α · M · N`: the constant bound `α`, integrated over the
threshold window `(0, M] × (0, N]`, contributes `α` times the window area (the
S26 assembly). Because the bound is uniform in the threshold pair, no
integrability of the integrand is needed at this layer — only the two
measurability hypotheses on `f` and `g`. -/
theorem survival_covariance_integrand_le_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {f g : Ω → ℝ}
    (hf : Measurable[σPair 0] f) (hg : Measurable[σPair 1] g)
    (t s : ℝ) :
    |μ.real {ω | t < f ω ∧ s < g ω}
        - μ.real {ω | t < f ω} * μ.real {ω | s < g ω}|
      ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  have hset : {ω | t < f ω ∧ s < g ω}
      = {ω | t < f ω} ∩ {ω | s < g ω} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  have hA := superlevel_setOf_measurable (m := σPair 0) hf t
  have hB := superlevel_setOf_measurable (m := σPair 1) hg s
  rw [hset]
  simp only [measureReal_def]
  exact davydov_indicator_bound σPair hA hB

/-- **Inner survival integral bound** (S26 inner assembly): integrating the uniform
α-bound of `survival_covariance_integrand_le_alpha` over the inner window `(0, N]`
majorises the inner survival integral by `α · N`. This is the inner half of the
double-integral assembly, feeding the bounded-variable Davydov estimate. -/
theorem inner_survival_covariance_le_alpha_length
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {f g : Ω → ℝ}
    (hf : Measurable[σPair 0] f) (hg : Measurable[σPair 1] g)
    (t N : ℝ) (hN : 0 ≤ N) :
    |∫ s in Set.Ioc 0 N,
        (μ.real {ω | t < f ω ∧ s < g ω}
          - μ.real {ω | t < f ω} * μ.real {ω | s < g ω})|
      ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) * N := by
  have hbound : ∀ s ∈ Set.Ioc (0 : ℝ) N,
      ‖μ.real {ω | t < f ω ∧ s < g ω}
          - μ.real {ω | t < f ω} * μ.real {ω | s < g ω}‖
        ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
    intro s _
    rw [Real.norm_eq_abs]
    exact survival_covariance_integrand_le_alpha σPair hf hg t s
  have hkey := norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Set.Ioc (0 : ℝ) N)
    (f := fun s => μ.real {ω | t < f ω ∧ s < g ω}
        - μ.real {ω | t < f ω} * μ.real {ω | s < g ω})
    measure_Ioc_lt_top hbound
  rw [Real.norm_eq_abs] at hkey
  have hmr : volume.real (Set.Ioc (0 : ℝ) N) = N := by
    rw [Real.volume_real_Ioc, sub_zero, max_eq_left hN]
  rwa [hmr] at hkey

/-- **Bounded-variable Davydov estimate** (S26, this session): the double-integral
assembly.

For non-negative random variables `f ∈ [0, M]` and `g ∈ [0, N]` with `f`
measurable w.r.t. `σPair 0` and `g` w.r.t. `σPair 1`, the covariance is bounded by
the α-mixing coefficient times the area of the threshold window:
$$
  \bigl|\mathrm{Cov}(f, g)\bigr|
    \;=\; \Bigl|\!\int f g \,-\, \bigl(\!\int f\bigr)\bigl(\!\int g\bigr)\Bigr|
    \;\le\; \alpha(\mathcal F, \mathcal G)\cdot M\cdot N.
$$

**Proof.** Two ingredients, chained through `norm_setIntegral_le_of_norm_le_const`:

* **S24** (`covariance_eq_double_survival_covariance`) rewrites the covariance as
  the double survival integral over the rectangle `(0, M] × (0, N]`,
  `∫_{(0,M]} ∫_{(0,N]} (μ\{t<f ∧ s<g\} − μ\{t<f\}·μ\{s<g\}) ds dt`.
* **S25** (`survival_covariance_integrand_le_alpha`) bounds the integrand by `α`
  *uniformly* in the threshold pair `(t, s)`.

The uniform pointwise bound integrates twice against Lebesgue measure. The inner
`s`-integral over `(0, N]` is majorised by `α · N` (constant bound `α` times
`volume (0, N] = N`); this constant `α · N` then bounds the outer `t`-integral,
giving `α · N · M`. Reordering the product yields `α · M · N`. Because the
integrand bound is uniform, no integrability of the integrand is used at this
layer beyond the two outer survival-integrabilities inherited by S24 — the
estimate is purely `‖∫_s f‖ ≤ C · |s|` applied twice.

**Role.** This is the bounded-variable (truncated) case of Davydov's inequality.
The remaining `davydov_covariance_inequality` sorry lifts this to general `L^p`
variables via truncation + Hölder with the mixing rate `α^{(p-2)/p}`; this lemma
supplies the base estimate that truncation reduces to. -/
theorem bounded_covariance_le_alpha_mul_rectangle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {f g : Ω → ℝ} {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_sig : Measurable[σPair 0] f) (hg_sig : Measurable[σPair 1] g)
    (hf_int : Integrable f μ) (hf_nn : 0 ≤ᵐ[μ] f) (hf_bdd : f ≤ᵐ[μ] (fun _ => M))
    (hg_int : Integrable g μ) (hg_nn : 0 ≤ᵐ[μ] g) (hg_bdd : g ≤ᵐ[μ] (fun _ => N))
    (h_joint_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 N, μ.real {ω | t < f ω ∧ s < g ω}) (Set.Ioc 0 M))
    (h_prod_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 N, μ.real {ω | t < f ω} * μ.real {ω | s < g ω})
      (Set.Ioc 0 M)) :
    |∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)|
      ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) * M * N := by
  -- Finiteness and Lebesgue mass of the two threshold windows.
  have hvolM : (volume : Measure ℝ).real (Set.Ioc (0:ℝ) M) = M := by
    rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hM]
  have hvolN : (volume : Measure ℝ).real (Set.Ioc (0:ℝ) N) = N := by
    rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hN]
  have hfinM : (volume : Measure ℝ) (Set.Ioc (0:ℝ) M) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  have hfinN : (volume : Measure ℝ) (Set.Ioc (0:ℝ) N) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  -- S24: rewrite the covariance as the double survival integral.
  rw [covariance_eq_double_survival_covariance hf_meas hg_meas hf_int hf_nn hf_bdd
        hg_int hg_nn hg_bdd h_joint_outer h_prod_outer]
  -- Inner bound: for every threshold `t`, the `s`-integral over `(0, N]` is
  -- majorised by `α · N`, since S25 bounds the integrand by `α` everywhere.
  have hInner : ∀ t : ℝ,
      ‖∫ s in Set.Ioc 0 N,
          (μ.real {ω | t < f ω ∧ s < g ω}
            - μ.real {ω | t < f ω} * μ.real {ω | s < g ω})‖
        ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) * N := by
    intro t
    have hle : ∀ s ∈ Set.Ioc (0:ℝ) N,
        ‖(μ.real {ω | t < f ω ∧ s < g ω}
            - μ.real {ω | t < f ω} * μ.real {ω | s < g ω})‖
          ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
      intro s _
      rw [Real.norm_eq_abs]
      exact survival_covariance_integrand_le_alpha σPair hf_sig hg_sig t s
    have h := norm_setIntegral_le_of_norm_le_const hfinN hle
    rwa [hvolN] at h
  -- Outer bound: the constant `α · N` bounds the `t`-integral over `(0, M]`.
  have hOuter := norm_setIntegral_le_of_norm_le_const (C :=
      CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) * N)
      hfinM (fun t _ => hInner t)
  rw [hvolM, Real.norm_eq_abs] at hOuter
  exact le_of_le_of_eq hOuter (by ring)

/-- **Signed bounded-variable Davydov estimate** (S27, this session).

Lifts the non-negative bounded estimate `bounded_covariance_le_alpha_mul_rectangle`
(S26) to *signed* bounded variables. For `f` with `m ≤ f ≤ M` (a.e.) measurable
w.r.t. `σPair 0`, and `g` with `n ≤ g ≤ N` (a.e.) measurable w.r.t. `σPair 1`,
$$
  \bigl|\mathrm{Cov}(f, g)\bigr|
    \;=\; \Bigl|\!\int f g \,-\, \bigl(\!\int f\bigr)\bigl(\!\int g\bigr)\Bigr|
    \;\le\; \alpha(\mathcal F, \mathcal G)\cdot (M - m)\cdot (N - n).
$$

**Proof.** Covariance is invariant under adding a constant to either argument
(`covariance_add_const_left`, `covariance_add_const_right`, S19), so
`Cov(f, g) = Cov(f - m, g - n)`. The shifted variables satisfy
`0 ≤ f - m ≤ M - m` and `0 ≤ g - n ≤ N - n`, hence S26 applies with window
widths `M - m`, `N - n`. Product integrabilities feeding the S19 linearity
identities are supplied by `Integrable.bdd_mul`, since each shift is a bounded
measurable function on a probability space.

**Role.** This is precisely the constant-shift reduction the S19 translation
lemmas were introduced to serve, and the form a symmetric truncation
`f ↦ clamp f [-T, T]` reduces to: with `m = -T`, `M = T` the window width is
`2T`, so the truncated Davydov base estimate reads `|Cov| ≤ 4 α T²`. The
remaining `davydov_covariance_inequality` lifts this bounded estimate to general
`L^p` variables via truncation + Hölder in the mixing rate `α^{(p-2)/p}`. -/
theorem signed_bounded_covariance_le_alpha_mul_rectangle
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {f g : Ω → ℝ} {m M n N : ℝ}
    (hmM : m ≤ M) (hnN : n ≤ N)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_sig : Measurable[σPair 0] f) (hg_sig : Measurable[σPair 1] g)
    (hf_int : Integrable f μ) (hf_lb : (fun _ => m) ≤ᵐ[μ] f)
    (hf_ub : f ≤ᵐ[μ] (fun _ => M))
    (hg_int : Integrable g μ) (hg_lb : (fun _ => n) ≤ᵐ[μ] g)
    (hg_ub : g ≤ᵐ[μ] (fun _ => N))
    (h_joint_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 (N - n), μ.real {ω | t < f ω - m ∧ s < g ω - n})
      (Set.Ioc 0 (M - m)))
    (h_prod_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 (N - n),
        μ.real {ω | t < f ω - m} * μ.real {ω | s < g ω - n})
      (Set.Ioc 0 (M - m))) :
    |∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)|
      ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1)
          * (M - m) * (N - n) := by
  -- Window widths are non-negative.
  have hMm : 0 ≤ M - m := sub_nonneg.mpr hmM
  have hNn : 0 ≤ N - n := sub_nonneg.mpr hnN
  -- Regularity of the shifted (non-negative) variables `f - m`, `g - n`.
  have hF_meas : Measurable (fun ω => f ω - m) := hf_meas.sub measurable_const
  have hG_meas : Measurable (fun ω => g ω - n) := hg_meas.sub measurable_const
  have hF_sig : Measurable[σPair 0] (fun ω => f ω - m) := hf_sig.sub measurable_const
  have hG_sig : Measurable[σPair 1] (fun ω => g ω - n) := hg_sig.sub measurable_const
  have hF_int : Integrable (fun ω => f ω - m) μ := hf_int.sub (integrable_const m)
  have hG_int : Integrable (fun ω => g ω - n) μ := hg_int.sub (integrable_const n)
  -- Non-negativity of the shifts.
  have hF_nn : (0 : Ω → ℝ) ≤ᵐ[μ] (fun ω => f ω - m) := by
    filter_upwards [hf_lb] with ω hω
    have : m ≤ f ω := hω
    simp only [Pi.zero_apply]; linarith
  have hG_nn : (0 : Ω → ℝ) ≤ᵐ[μ] (fun ω => g ω - n) := by
    filter_upwards [hg_lb] with ω hω
    have : n ≤ g ω := hω
    simp only [Pi.zero_apply]; linarith
  -- Upper bounds of the shifts.
  have hF_ub : (fun ω => f ω - m) ≤ᵐ[μ] (fun _ => M - m) := by
    filter_upwards [hf_ub] with ω hω
    have : f ω ≤ M := hω
    linarith
  have hG_ub : (fun ω => g ω - n) ≤ᵐ[μ] (fun _ => N - n) := by
    filter_upwards [hg_ub] with ω hω
    have : g ω ≤ N := hω
    linarith
  -- Uniform norm bound on `f - m`, feeding `Integrable.bdd_mul`.
  have hFbound : ∀ᵐ ω ∂μ, ‖f ω - m‖ ≤ M - m := by
    filter_upwards [hf_lb, hf_ub] with ω hlb hub
    have hlb' : m ≤ f ω := hlb
    have hub' : f ω ≤ M := hub
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ f ω - m)]
    linarith
  -- Product integrabilities needed by the S19 translation identities.
  have hFg_int : Integrable (fun ω => (f ω - m) * g ω) μ :=
    hg_int.bdd_mul hF_meas.aestronglyMeasurable hFbound
  have hFG_int : Integrable (fun ω => (f ω - m) * (g ω - n)) μ :=
    hG_int.bdd_mul hF_meas.aestronglyMeasurable hFbound
  -- Covariance is translation-invariant:  Cov(f, g) = Cov(f - m, g - n).
  have eLm : ∀ ω, f ω - m + m = f ω := fun ω => by ring
  have eRn : ∀ ω, g ω - n + n = g ω := fun ω => by ring
  have hcov_eq :
      (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)
        = (∫ ω, (f ω - m) * (g ω - n) ∂μ)
            - (∫ ω, (f ω - m) ∂μ) * (∫ ω, (g ω - n) ∂μ) := by
    have hL := covariance_add_const_left (μ := μ) (f := fun ω => f ω - m) (g := g) m
      hF_int hg_int hFg_int
    have hR := covariance_add_const_right (μ := μ) (f := fun ω => f ω - m)
      (g := fun ω => g ω - n) n hF_int hG_int hFG_int
    simp only [eLm, eRn] at hL hR
    rw [hL, hR]
  rw [hcov_eq]
  exact bounded_covariance_le_alpha_mul_rectangle
    (f := fun ω => f ω - m) (g := fun ω => g ω - n) (M := M - m) (N := N - n)
    σPair hMm hNn hF_meas hG_meas hF_sig hG_sig hF_int hF_nn hF_ub hG_int hG_nn hG_ub
    h_joint_outer h_prod_outer

/-- **L^∞ (symmetric-window) Davydov estimate** (S28, this session).

Specializes the signed bounded estimate
`signed_bounded_covariance_le_alpha_mul_rectangle` (S27) to the *symmetric*
truncation window `[-Bf, Bf] × [-Bg, Bg]` — the canonical `L^∞` form of
Davydov's inequality. For `f` bounded by `Bf` (`|f| ≤ Bf` a.e.) and measurable
w.r.t. `σPair 0`, and `g` bounded by `Bg` measurable w.r.t. `σPair 1`,
$$
  \bigl|\mathrm{Cov}(f, g)\bigr|
    \;=\; \Bigl|\!\int f g \,-\, \bigl(\!\int f\bigr)\bigl(\!\int g\bigr)\Bigr|
    \;\le\; 4 \cdot \alpha(\mathcal F, \mathcal G)\cdot B_f \cdot B_g.
$$

**Proof.** Apply S27 with `m = -Bf`, `M = Bf`, `n = -Bg`, `N = Bg`. The single
essential-sup hypothesis `|f| ≤ Bf` unpacks (`abs_le`) into the two-sided
window `-Bf ≤ f ≤ Bf`, and likewise for `g`. The S27 conclusion
`α · (Bf - (-Bf)) · (Bg - (-Bg))` collapses to `4 · α · Bf · Bg` because each
window width is `2·(sup bound)` (`ring`). The two outer survival-integrability
hypotheses are inherited unchanged from S27 (they feed the S24 layer-cake
representation and are supplied by the caller together with the bound data).

**Role.** This is the exact form the `L^p` density step of
`davydov_covariance_inequality` consumes: after a symmetric truncation
`f ↦ clamp f [-T, T]` the truncated covariance is controlled by `4 α T²`, and
the Hölder tail estimate in the mixing rate `α^{(p-2)/p}` is added on top. It
is the standard textbook statement of Davydov's inequality for *bounded*
variables (Doukhan 1994 §1.2.2, Bradley 2007 Vol I Thm 3.7). -/
theorem linfty_covariance_le_four_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {f g : Ω → ℝ} {Bf Bg : ℝ}
    (hBf : 0 ≤ Bf) (hBg : 0 ≤ Bg)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_sig : Measurable[σPair 0] f) (hg_sig : Measurable[σPair 1] g)
    (hf_int : Integrable f μ) (hf_bd : ∀ᵐ ω ∂μ, |f ω| ≤ Bf)
    (hg_int : Integrable g μ) (hg_bd : ∀ᵐ ω ∂μ, |g ω| ≤ Bg)
    (h_joint_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 (Bg - -Bg), μ.real {ω | t < f ω - -Bf ∧ s < g ω - -Bg})
      (Set.Ioc 0 (Bf - -Bf)))
    (h_prod_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 (Bg - -Bg),
        μ.real {ω | t < f ω - -Bf} * μ.real {ω | s < g ω - -Bg})
      (Set.Ioc 0 (Bf - -Bf))) :
    |∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)|
      ≤ 4 * CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) * Bf * Bg := by
  have hmM : -Bf ≤ Bf := by linarith
  have hnN : -Bg ≤ Bg := by linarith
  -- Unpack the symmetric essential-sup bounds into two-sided windows.
  have hf_lb : (fun _ => -Bf) ≤ᵐ[μ] f := by
    filter_upwards [hf_bd] with ω hω; exact (abs_le.mp hω).1
  have hf_ub : f ≤ᵐ[μ] (fun _ => Bf) := by
    filter_upwards [hf_bd] with ω hω; exact (abs_le.mp hω).2
  have hg_lb : (fun _ => -Bg) ≤ᵐ[μ] g := by
    filter_upwards [hg_bd] with ω hω; exact (abs_le.mp hω).1
  have hg_ub : g ≤ᵐ[μ] (fun _ => Bg) := by
    filter_upwards [hg_bd] with ω hω; exact (abs_le.mp hω).2
  have h := signed_bounded_covariance_le_alpha_mul_rectangle
    σPair (m := -Bf) (M := Bf) (n := -Bg) (N := Bg)
    hmM hnN hf_meas hg_meas hf_sig hg_sig
    hf_int hf_lb hf_ub hg_int hg_lb hg_ub
    h_joint_outer h_prod_outer
  refine le_trans h (le_of_eq ?_)
  ring

/-- **Symmetric-truncation Davydov base estimate** (S28, this session).

The equal-bound special case of `linfty_covariance_le_four_alpha`: when both
variables share the truncation level `T` (`|f| ≤ T`, `|g| ≤ T`), the covariance
of the truncated pair is controlled by `4 · α · T²`. This is verbatim the
constant the `L^p` density step of `davydov_covariance_inequality` pays for the
bounded part after truncating at level `T`; the residual Hölder tail in the
mixing rate is added separately. -/
theorem truncated_covariance_le_four_alpha_sq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {f g : Ω → ℝ} {T : ℝ}
    (hT : 0 ≤ T)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_sig : Measurable[σPair 0] f) (hg_sig : Measurable[σPair 1] g)
    (hf_int : Integrable f μ) (hf_bd : ∀ᵐ ω ∂μ, |f ω| ≤ T)
    (hg_int : Integrable g μ) (hg_bd : ∀ᵐ ω ∂μ, |g ω| ≤ T)
    (h_joint_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 (T - -T), μ.real {ω | t < f ω - -T ∧ s < g ω - -T})
      (Set.Ioc 0 (T - -T)))
    (h_prod_outer : IntegrableOn
      (fun t => ∫ s in Set.Ioc 0 (T - -T),
        μ.real {ω | t < f ω - -T} * μ.real {ω | s < g ω - -T})
      (Set.Ioc 0 (T - -T))) :
    |∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)|
      ≤ 4 * CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) * T ^ 2 := by
  have h := linfty_covariance_le_four_alpha σPair (Bf := T) (Bg := T)
    hT hT hf_meas hg_meas hf_sig hg_sig hf_int hf_bd hg_int hg_bd
    h_joint_outer h_prod_outer
  refine le_trans h (le_of_eq ?_)
  ring

/-- **Davydov's covariance inequality** (Davydov 1968).

For random variables `X, Y : Ω → ℝ` with finite `L^p` norms (`p > 2`), where `X`
is measurable with respect to a σ-algebra `ℱ` and `Y` with respect to `𝒢`, the
covariance is controlled by the α-mixing coefficient between `ℱ` and `𝒢`:
$$
|\mathrm{Cov}(X, Y)| \le 12 \cdot \alpha(\mathcal F, \mathcal G)^{(p-2)/p}
   \cdot \|X\|_{L^p} \cdot \|Y\|_{L^p}.
$$

We accept an arbitrary upper bound `α₀` for the α-mixing coefficient (rather
than the coefficient itself), so the per-term application in
`longrun_variance_absolutely_convergent` can plug in the numerical mixing
bound `H.alpha (k+1)` directly.

The exponent `(p - 2) / p` specializes to `δ / (2 + δ)` when `p = 2 + δ`,
giving the standard Davydov–Ibragimov rate.

**Structural decomposition into named ingredients (S4/S5 deliverables).**
The proof of this L^p Davydov inequality reduces to three named order-theory
ingredients about `alphaMixingCoeff`, plus the L^p density step:

1. **`alphaMixingCoeff_le_one`** (**S5, proven this session**):
   `alphaMixingCoeff μ ℱ 𝒢 ≤ 1` for a probability measure. Pure
   `ConditionallyCompleteLattice ℝ` bound — every term in the defining sup
   is bounded by `1` (via `indicator_cov_le_one`).
2. **`alphaMixingCoeff_nonneg`** (**S5, proven this session**; the parent
   file `CentralLimitTheoremOQ02.lean` line 444 omitted this "due to nested
   ciSup elaboration complexity"): `0 ≤ alphaMixingCoeff μ ℱ 𝒢`, discharged
   by reflective use of `Real.iSup_nonneg` at each layer of the 4-fold
   `⨆`.
3. **`davydov_indicator_bound`** (**S5b, proven this session** — the
   *indicator base case*): for measurable indicators
   `|μ(A ∩ B).toReal - μ(A).toReal · μ(B).toReal| ≤ alphaMixingCoeff μ ℱ 𝒢`.
   This is the defining inequality of `alphaMixingCoeff` packaged for use.
   Proof peels the 4 nested ⨆ layers via `le_ciSup_of_le` (Set Ω layers,
   with `BddAbove` witnesses uniformly derived from `indicator_cov_le_one`)
   and `ciSup_pos` (Prop layers).
4. **L^p density step** (S5c target, ~100 lines): truncate `X` and `Y` to
   bounded random variables, apply indicator decomposition
   `X = ∫ 1_{X > t} dt` + Hölder's inequality with conjugate exponents
   `(p, p/(p-1))`. This reduces the bound to the indicator base case (3).
   References: Doukhan 1994 §1.2.2, Bradley 2007 Vol I Thm 3.7.

The S4-formalized scaffolding consists of `indicator_cov_le_one` (proven,
the `[0, 1]` envelope) and the function-form of σ-algebra parameters
(`σPair : Fin 2 → MeasurableSpace Ω`) which dodges the Lean 4 typeclass
synthesis quirk encountered when both `ℱ : MeasurableSpace Ω` and the
ambient `[MeasurableSpace Ω]` are simultaneously in scope at the call site
(this was the original blocker on the S3 statement — the parent file uses
the same function-form trick at `independent_implies_zero_mixing` and
`AlphaMixingSequence.mixing_bound`). -/
theorem davydov_covariance_inequality
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {α₀ p : ℝ}
    (_hα_nonneg : 0 ≤ α₀)
    (_hp : 2 < p)
    (_hXmem : MemLp X (ENNReal.ofReal p) μ)
    (_hYmem : MemLp Y (ENNReal.ofReal p) μ)
    (σPair : Fin 2 → MeasurableSpace Ω)
    (_hX_meas : Measurable[σPair 0] X)
    (_hY_meas : Measurable[σPair 1] Y)
    (_hα_bound :
      CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) ≤ α₀) :
    |∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)| ≤
      12 * α₀ ^ ((p - 2) / p) *
        (eLpNorm X (ENNReal.ofReal p) μ).toReal *
        (eLpNorm Y (ENNReal.ofReal p) μ).toReal := by
  sorry

/-! ## Part V: Long-run variance absolute convergence (S3 deliverable) -/

/-- **Stationary L^p norm equality** under `IbragimovHypotheses`.

A consequence of marginal stationarity (`X k =ᵈ X 0`) and Mathlib's
`IdentDistrib.eLpNorm_eq`: every shift has the same L^p norm. -/
theorem stationary_eLpNorm_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {δ C r : ℝ}
    (H : IbragimovHypotheses μ X δ C r) (k : ℕ) (p : ENNReal) :
    eLpNorm (X k) p μ = eLpNorm (X 0) p μ :=
  (H.stationary k).eLpNorm_eq p

/-- **Polynomial mixing summability** under `IbragimovHypotheses`.

The `δ/(2+δ)`-th power of the mixing coefficients `α(k+1)` is summable over `k`:
the polynomial decay `α(n) ≤ C n^{-r}` and the sharp threshold `r > (2+δ)/δ`
together give `α(k+1)^{δ/(2+δ)} ≤ C^{δ/(2+δ)} · (k+1)^{-rδ/(2+δ)}`, with the
right-hand side summable by `ibragimov_threshold_summable` after an index shift. -/
theorem polynomial_mixing_summable
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {δ C r : ℝ}
    (H : IbragimovHypotheses μ X δ C r) :
    Summable (fun k : ℕ => H.alpha (k + 1) ^ (δ / (2 + δ))) := by
  have hδ : 0 < δ := H.delta_pos
  have hC_pos : 0 < C := H.poly_rate.1
  have hα_bd : ∀ n : ℕ, 1 ≤ n → H.alpha n ≤ C * (n : ℝ) ^ (-r) := H.poly_rate.2.2
  have h2δ_pos : 0 < 2 + δ := by linarith
  set q : ℝ := δ / (2 + δ) with hq_def
  have hq_pos : 0 < q := div_pos hδ h2δ_pos
  set s : ℝ := r * δ / (2 + δ) with hs_def
  have hs_eq_rq : s = r * q := by rw [hs_def, hq_def]; ring
  set K : ℝ := C ^ q with hK_def
  -- Pointwise bound:  α(k+1)^q ≤ K · ((k+1):ℝ)^{-s}.
  have hbound : ∀ k : ℕ,
      H.alpha (k + 1) ^ q ≤ K * ((k + 1 : ℕ) : ℝ) ^ (-s) := by
    intro k
    have hk1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hα_nn : 0 ≤ H.alpha (k + 1) := H.alpha_nonneg _
    have hα_le : H.alpha (k + 1) ≤ C * ((k + 1 : ℕ) : ℝ) ^ (-r) := hα_bd _ hk1
    have hk1_nat_nn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
    have hkr_nn : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ (-r) := Real.rpow_nonneg hk1_nat_nn _
    -- (1) Monotonicity at exponent q:  α(k+1)^q ≤ (C · (k+1)^{-r})^q
    have step1 :
        H.alpha (k + 1) ^ q ≤ (C * ((k + 1 : ℕ) : ℝ) ^ (-r)) ^ q :=
      Real.rpow_le_rpow hα_nn hα_le (le_of_lt hq_pos)
    -- (2) (C · x^{-r})^q = C^q · x^{-rq} = K · x^{-s}
    have step2 :
        (C * ((k + 1 : ℕ) : ℝ) ^ (-r)) ^ q
          = K * ((k + 1 : ℕ) : ℝ) ^ (-s) := by
      rw [Real.mul_rpow (le_of_lt hC_pos) hkr_nn, ← hK_def]
      congr 1
      rw [← Real.rpow_mul hk1_nat_nn]
      congr 1
      rw [hs_eq_rq]; ring
    linarith [step1, step2.le, step2.symm.le]
  -- Nonnegativity of the LHS sequence
  have hLHS_nn : ∀ k : ℕ, 0 ≤ H.alpha (k + 1) ^ q := fun k =>
    Real.rpow_nonneg (H.alpha_nonneg _) _
  -- Summability of the bounding sequence
  have hsum_threshold :
      Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
    rw [hs_def]
    exact ibragimov_threshold_summable δ r hδ H.rate_admissible
  have hsum_shift :
      Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-s)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-s)) 1).mpr hsum_threshold
  have hsum_K_shift :
      Summable (fun k : ℕ => K * ((k + 1 : ℕ) : ℝ) ^ (-s)) :=
    hsum_shift.mul_left K
  exact Summable.of_nonneg_of_le hLHS_nn hbound hsum_K_shift

/-- **Absolute convergence of the long-run variance covariance series**
under `IbragimovHypotheses`.

The proof chain:
  - **Davydov** ⇒  `|Cov(X 0, X (k+1))| ≤ 12 · α(k+1)^{δ/(2+δ)} ·
    ‖X 0‖_{2+δ} · ‖X (k+1)‖_{2+δ}`.
  - **Stationarity** (via `stationary_eLpNorm_eq`) ⇒  `‖X (k+1)‖_{2+δ} = ‖X 0‖_{2+δ}`.
  - **Mean zero** ⇒  Cov simplifies to the integral itself.
  - **Polynomial mixing summability** ⇒  the per-term upper bound is summable.
  - **Comparison test** (Mathlib `Summable.of_nonneg_of_le`) ⇒  conclusion.

Modulo `davydov_covariance_inequality` (S4 sorry), this is a fully verified
chain. -/
theorem longrun_variance_absolutely_convergent
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {δ C r : ℝ}
    (H : IbragimovHypotheses μ X δ C r) :
    Summable (fun k : ℕ => |∫ ω, X 0 ω * X (k + 1) ω ∂μ|) := by
  -- Setup
  set p : ℝ := 2 + δ with hp_def
  have hδ : 0 < δ := H.delta_pos
  have hp_gt : 2 < p := by rw [hp_def]; linarith
  have h2δ_pos : 0 < 2 + δ := by linarith
  have hexp_eq : (p - 2) / p = δ / (2 + δ) := by rw [hp_def]; ring
  set M : ℝ := (eLpNorm (X 0) (ENNReal.ofReal p) μ).toReal with hM_def
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  set K : ℝ := 12 * M * M with hK_def
  have hK_nn : 0 ≤ K := by
    have h12M : 0 ≤ 12 * M := mul_nonneg (by norm_num) hM_nn
    exact mul_nonneg h12M hM_nn
  -- Per-term Davydov bound
  have hbound : ∀ k : ℕ,
      |∫ ω, X 0 ω * X (k + 1) ω ∂μ| ≤ K * H.alpha (k + 1) ^ (δ / (2 + δ)) := by
    intro k
    have hα_nn : 0 ≤ H.alpha (k + 1) := H.alpha_nonneg _
    have hXmem0 : MemLp (X 0) (ENNReal.ofReal p) μ := H.moment_bound 0
    have hXmemk : MemLp (X (k + 1)) (ENNReal.ofReal p) μ := H.moment_bound (k + 1)
    have hpast0 : Measurable[H.pastSigma 0] (X 0) := H.past_measurable 0
    have hfut_k1 : Measurable[H.futureSigma (k + 1)] (X (k + 1)) :=
      H.future_measurable (k + 1)
    -- σ-algebra pair as Fin 2 → MS Ω (function-form, avoids the parent
    -- file's typeclass-synthesis quirk on direct MeasurableSpace Ω args).
    let σPair : Fin 2 → MeasurableSpace Ω :=
      fun i => if i = 0 then H.pastSigma 0 else H.futureSigma (k + 1)
    have hσP0 : σPair 0 = H.pastSigma 0 := by simp [σPair]
    have hσP1 : σPair 1 = H.futureSigma (k + 1) := by simp [σPair]
    -- α mixing bound at lag k+1
    have hα_bd' :
        CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) ≤
          H.alpha (k + 1) := by
      rw [hσP0, hσP1]
      have h := H.alpha_bound 0 (k + 1)
      simpa using h
    have hpast0' : Measurable[σPair 0] (X 0) := by rw [hσP0]; exact hpast0
    have hfut_k1' : Measurable[σPair 1] (X (k + 1)) := by
      rw [hσP1]; exact hfut_k1
    -- Apply Davydov
    have hDavydov := davydov_covariance_inequality
      (X := X 0) (Y := X (k + 1)) (α₀ := H.alpha (k + 1)) (p := p)
      hα_nn hp_gt hXmem0 hXmemk
      σPair
      hpast0' hfut_k1' hα_bd'
    -- Rewrite (p-2)/p → δ/(2+δ)
    rw [hexp_eq] at hDavydov
    -- Stationary norm equality: ‖X(k+1)‖_p = ‖X 0‖_p
    rw [stationary_eLpNorm_eq H (k + 1) (ENNReal.ofReal p)] at hDavydov
    -- Mean zero kills the (∫X 0)(∫X(k+1)) term
    simp only [H.mean_zero, zero_mul, sub_zero] at hDavydov
    -- Match constant: K · α^q = 12 · M · M · α^q = 12 · α^q · M · M (ring)
    have rhs_eq :
        12 * H.alpha (k + 1) ^ (δ / (2 + δ)) * M * M
          = K * H.alpha (k + 1) ^ (δ / (2 + δ)) := by
      rw [hK_def]; ring
    linarith [hDavydov, rhs_eq.le, rhs_eq.symm.le]
  -- Summability via comparison
  have hLHS_nn : ∀ k : ℕ, 0 ≤ |∫ ω, X 0 ω * X (k + 1) ω ∂μ| := fun _ => abs_nonneg _
  have hsum_α := polynomial_mixing_summable H
  exact Summable.of_nonneg_of_le hLHS_nn hbound (hsum_α.mul_left K)

/-! ## Part VI: Ibragimov's CLT (main theorem statement, S6+ target) -/

/-- **Ibragimov's central limit theorem for polynomial α-mixing sequences.**

Under stationarity, mean zero, uniformly bounded `(2 + δ)`-th moments,
polynomial α-mixing rate `r > (2 + δ) / δ`, and a positive long-run variance
`σ² > 0`, the normalized partial sums `S_n / √n` converge in distribution to
`N(0, σ²)`.

We state convergence via the characteristic-function (Lévy continuity) form:
`φ_{S_n/√n}(t) → exp(-σ² t² / 2)` for every `t : ℝ`. The long-run variance
σ² is supplied as a parameter rather than computed inline.

**Proof outline** (S5+):
1. **S3** — Sharp threshold (done in `ibragimov_threshold_summable`).
2. **S4** — Davydov covariance inequality (currently `davydov_covariance_inequality`
   sorry; this session reduces the longrun-variance lemma to Davydov).
3. **S5** — Long-run variance absolute convergence (this session,
   `longrun_variance_absolutely_convergent`, proven modulo S4).
4. **S6** — Bernstein block decomposition (`p_n, q_n → ∞`, `n / p_n → ∞`).
5. **S7** — Large-block independence approximation via mixing.
6. **S8** — Lindeberg's condition on large blocks.
7. **S9** — Apply Lindeberg–Feller CLT (from the parent file).

The full proof is conjectured to be ~400 lines on top of the
Davydov/Bernstein infrastructure (S4–S6).
-/
theorem mixing_clt_ibragimov
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {δ C r σsq : ℝ}
    (_H : IbragimovHypotheses μ X δ C r)
    (_hσsq_pos : 0 < σsq)
    (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, Complex.exp (Complex.I * (t : ℂ) *
          ((∑ k ∈ Finset.range n, X k ω) / Real.sqrt n : ℂ)) ∂μ)
      atTop
      (𝓝 (Complex.exp (-(σsq : ℂ) * (t : ℂ)^2 / 2))) := by
  sorry

end CentralLimitTheoremOQ02OQ04
