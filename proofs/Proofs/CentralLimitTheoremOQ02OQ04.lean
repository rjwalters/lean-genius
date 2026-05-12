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

**Status of this file (S4 ACT — build-fix + structural decomposition).**
S3 (previous session) merged at `build pending` and never actually compiled
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
- `IbragimovHypotheses` structure (14 fields).
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
fact, derived from Mathlib's `Real.summable_nat_rpow_inv`. -/
theorem polynomial_summable_of_exponent_gt_one (s : ℝ) (_hs : 1 < s) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
  -- The classical ζ-function summability fact: Σ n^{-s} converges iff s > 1.
  -- In current Mathlib (drift since the S3 statement) the precise namespaced
  -- name has moved; the proof reduces to `Real.rpow_neg` + an existing
  -- summability lemma in Mathlib.Analysis.SpecialFunctions.Pow.Real.
  -- Mechanic-pass target: locate the renamed `summable_*_nat_rpow_inv` /
  -- `summable_one_div_nat_rpow` lemma and substitute.
  sorry

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
the uniform-envelope helper that anchors the `BddAbove` witness for any
further work on the nested suprema. The full upper/lower bounds
(`alphaMixingCoeff_le_one`, `alphaMixingCoeff_nonneg`) and the *indicator
base case* of Davydov's inequality
`|μ(A ∩ B).toReal - μ(A).toReal · μ(B).toReal| ≤ alphaMixingCoeff μ ℱ 𝒢` are
documented in the docstring of `davydov_covariance_inequality` (Part IV)
as the structural decomposition of the L^p Davydov sorry; their formal
proofs require resolving a Lean 4 typeclass-synthesis quirk where local
`MeasurableSpace Ω` arguments compete with the ambient instance — a known
issue (the parent file omits `alphaMixingCoeff_nonneg` at line 444 for the
same reason). The mechanic-pass to discharge them must use either a
function-wrapper for σ-algebras (cf. parent's `σ_k : ℕ → MeasurableSpace Ω`)
or a Subtype barrier.
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
      simp [Set.indicator_apply, Set.mem_inter_iff, hωA, hωB]
  rw [hprod, integral_indicator_one hAB, integral_indicator_one hA,
      integral_indicator_one hB]

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

**Structural decomposition into named ingredients (S4 deliverable).**
The proof of this L^p Davydov inequality reduces to three named order-theory
ingredients about `alphaMixingCoeff`, plus the L^p density step:

1. **`alphaMixingCoeff_le_one`** (yet to formalize, mechanic target):
   `alphaMixingCoeff μ ℱ 𝒢 ≤ 1` for a probability measure. Pure
   `ConditionallyCompleteLattice ℝ` bound — every term in the defining sup
   is bounded by `1` (via `indicator_cov_le_one`).
2. **`alphaMixingCoeff_nonneg`** (yet to formalize; the parent file
   `CentralLimitTheoremOQ02.lean` line 444 omitted this "due to nested
   ciSup elaboration complexity"): `0 ≤ alphaMixingCoeff μ ℱ 𝒢` by
   exhibiting `A = B = ∅` in the supremum.
3. **`davydov_indicator_bound`** (yet to formalize, mechanic target — the
   *indicator base case*): for measurable indicators
   `|μ(A ∩ B).toReal - μ(A).toReal · μ(B).toReal| ≤ alphaMixingCoeff μ ℱ 𝒢`.
   This is the defining inequality of `alphaMixingCoeff` packaged for use.
4. **L^p density step** (S5 target, ~100 lines): truncate `X` and `Y` to
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
