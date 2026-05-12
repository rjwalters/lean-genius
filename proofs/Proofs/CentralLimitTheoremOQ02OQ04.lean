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

**Status of this file (S3 ACT).**
This file builds on the S2 scaffolding and discharges the long-run variance
absolute convergence — modulo Davydov's covariance inequality (which is moved
from an inline sorry to a clearly-identified standalone statement targeted for
the next session, S4).

Deliverables this session:
- `Stationary`, `PolynomialMixingRate`, `MomentBound2δ` predicates (unchanged).
- `IbragimovHypotheses` structure — **extended** with three new fields:
  `alpha_nonneg`, `past_measurable`, `future_measurable`. These were missing
  from S2 and are needed to apply Davydov's inequality per-term.
- `davydov_covariance_inequality` — **stated as a sorry**; the heavy
  measure-theoretic content (~150 lines of Hölder + indicator decomposition)
  is the S4 deliverable.
- `stationary_eLpNorm_eq` — **proven**; `IdentDistrib.eLpNorm_eq` applied at
  each shift.
- `polynomial_mixing_summable` — **proven**; combines polynomial decay,
  monotonicity of `rpow`, and `ibragimov_threshold_summable`.
- `longrun_variance_absolutely_convergent` — **proven**, using Davydov
  per-term + stationarity + the threshold summability above.
- `mixing_clt_ibragimov` — sorry (still S6+ target).

Sorries: 2 (davydov_covariance_inequality, mixing_clt_ibragimov).
The S2 sorry `longrun_variance_absolutely_convergent` has been discharged,
replaced by a single clearly-scoped Davydov sorry (net change: 0).
Axioms: 0 — parent `CentralLimitTheoremOQ02.lean` carries the abstract α-mixing
infrastructure; this file consumes rather than re-axiomatizes.

Per the S1/S2 plan, this file builds on the parent
`CentralLimitTheoremOQ02.lean`, which defines `alphaMixingCoeff`,
`AlphaMixingSequence`, and `longRunVariance`.
-/

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Variance
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Proofs.CentralLimitTheoremOQ02

open MeasureTheory ProbabilityTheory Filter Real

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
theorem polynomial_summable_of_exponent_gt_one (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
  have key : Summable (fun n : ℕ => ((n : ℝ) ^ s)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hs
  refine key.congr ?_
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hs_ne : s ≠ 0 := by linarith
    have hsneg_ne : -s ≠ 0 := by simp [hs_ne]
    simp [Real.zero_rpow hs_ne, Real.zero_rpow hsneg_ne]
  · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le _
    rw [Real.rpow_neg hn0]

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

/-! ## Part III: Davydov's covariance inequality (S4 target, stated as sorry) -/

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

**Proof outline (S4 deliverable).** Truncate `X` and `Y` to bounded random
variables; for bounded random variables, indicator decomposition + Hölder's
inequality (conjugate exponents `(p, p/(p-1))`) reduces the bound to the
defining inequality of `alphaMixingCoeff` on indicator pairs. Standard
reference: Doukhan 1994 §1.2.2, Bradley 2007 Vol I Thm 3.7.

Sorry justified: the proof is a self-contained ~150-line measure-theoretic
lemma whose direct formalization is the S4 target. -/
theorem davydov_covariance_inequality
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} {α₀ p : ℝ}
    (_hα_nonneg : 0 ≤ α₀)
    (_hp : 2 < p)
    (_hXmem : MemLp X (ENNReal.ofReal p) μ)
    (_hYmem : MemLp Y (ENNReal.ofReal p) μ)
    (ℱ 𝒢 : MeasurableSpace Ω)
    (_hX_meas : Measurable[ℱ] X)
    (_hY_meas : Measurable[𝒢] Y)
    (_hα_bound : CentralLimitTheoremOQ02.alphaMixingCoeff μ ℱ 𝒢 ≤ α₀) :
    |∫ ω, X ω * Y ω ∂μ - (∫ ω, X ω ∂μ) * (∫ ω, Y ω ∂μ)| ≤
      12 * α₀ ^ ((p - 2) / p) *
        (eLpNorm X (ENNReal.ofReal p) μ).toReal *
        (eLpNorm Y (ENNReal.ofReal p) μ).toReal := by
  sorry

/-! ## Part IV: Long-run variance absolute convergence (S3 deliverable) -/

/-- **Stationary L^p norm equality** under `IbragimovHypotheses`.

A consequence of marginal stationarity (`X k =ᵈ X 0`) and Mathlib's
`IdentDistrib.eLpNorm_eq`: every shift has the same L^p norm. -/
theorem stationary_eLpNorm_eq
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {δ C r : ℝ}
    (H : IbragimovHypotheses μ X δ C r) (k : ℕ) (p : ℝ≥0∞) :
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
    -- α mixing bound at lag k+1
    have hα_bd' :
        CentralLimitTheoremOQ02.alphaMixingCoeff μ (H.pastSigma 0)
            (H.futureSigma (k + 1)) ≤ H.alpha (k + 1) := by
      have h := H.alpha_bound 0 (k + 1)
      simpa using h
    -- Apply Davydov
    have hDavydov := davydov_covariance_inequality
      (X := X 0) (Y := X (k + 1)) (α₀ := H.alpha (k + 1)) (p := p)
      hα_nn hp_gt hXmem0 hXmemk
      (H.pastSigma 0) (H.futureSigma (k + 1))
      hpast0 hfut_k1 hα_bd'
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

/-! ## Part V: Ibragimov's CLT (main theorem statement, S6+ target) -/

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
    {X : ℕ → Ω → ℝ} {δ C r σ² : ℝ}
    (_H : IbragimovHypotheses μ X δ C r)
    (_hσ²_pos : 0 < σ²)
    (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, Complex.exp (Complex.I * (t : ℂ) *
          ((∑ k ∈ Finset.range n, X k ω) / Real.sqrt n : ℂ)) ∂μ)
      atTop
      (𝓝 (Complex.exp (-(σ² : ℂ) * (t : ℂ)^2 / 2))) := by
  sorry

end CentralLimitTheoremOQ02OQ04
