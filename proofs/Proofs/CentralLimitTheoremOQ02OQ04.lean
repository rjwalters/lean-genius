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

**This session: S16 — scaled-indicator covariance bound.**
Added `scaled_indicator_covariance_le_alpha` (PROVEN): promotes the unit
`indicator_covariance_le_alpha` to arbitrary real scalars,
`|Cov(a 1_A, b 1_B)| ≤ |a| |b| α(ℱ, 𝒢)`, by pulling the scalars through the
bilinear covariance (`integral_const_mul` on the joint and marginal integrals)
and `abs_mul`. This is the single-cell building block of the simple-function
step toward `davydov_covariance_inequality`: a sub-σ-measurable simple function
`∑ aᵢ 1_{Aᵢ}` covaried against `∑ bⱼ 1_{Bⱼ}` reduces, by bilinear expansion, to
a finite sum of exactly these scaled-cell bounds. No sorry reduction this
session — purely additive infrastructure.

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
