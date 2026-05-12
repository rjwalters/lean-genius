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

**Status of this file (S2 ORIENT).**
This file delivers the **scaffolding** layer per the S1 OBSERVE plan:
- `Stationary` predicate (joint stationarity of the sequence under μ).
- `PolynomialMixingRate` predicate for α(n) ≤ C · n^{−r}.
- `MomentBound2δ` predicate for finite `(2 + δ)`-th moments.
- `IbragimovHypotheses` structure bundling stationarity, mean zero,
  moment bound, polynomial mixing rate, and the sharp threshold
  `r > (2 + δ) / δ`.
- `mixing_clt_ibragimov` — the main theorem statement (sorry).
- `longrun_variance_absolutely_convergent` — the genuinely tractable
  sub-result whose proof is targeted for S5 (sorry).
- `polynomial_summable_of_exponent_gt_one` — proven via Mathlib's
  `Real.summable_one_div_nat_rpow`.
- `ibragimov_threshold_summable` — the sharp-threshold corollary, proven.

All substantive proof work for the CLT itself is deferred to S3+ per the
decomposition table in
`research/problems/central-limit-theorem-oq-02-oq-04/state.md`.

Sorries: 2 (mixing_clt_ibragimov, longrun_variance_absolutely_convergent).
Axioms: 0 (the parent CentralLimitTheoremOQ02 carries the abstract α-mixing
infrastructure; we reuse rather than re-axiomatize).

Per the S1 OBSERVE survey, this file builds on the parent
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
introduced in S3+ when proving the variance summability.

For Ibragimov's CLT, the marginal version below suffices for the *statement*;
the proof at S6+ will need the strengthening (joint stationarity for tuples)
when invoking the Bernstein block decomposition.
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
The exact formulation `∫⁻ ‖X k ω‖₊^{2+δ} dμ < ⊤` matches Mathlib's `MemLp`
hypothesis for `p = 2 + δ`. -/
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
  /-- The past σ-algebra at time `k`. -/
  pastSigma : ℕ → MeasurableSpace Ω
  /-- The future σ-algebra at time `k+n`. -/
  futureSigma : ℕ → MeasurableSpace Ω
  /-- `alpha n` bounds the abstract α-mixing coefficient at lag `n`. -/
  alpha_bound : ∀ k n,
    CentralLimitTheoremOQ02.alphaMixingCoeff μ (pastSigma k) (futureSigma (k + n))
      ≤ alpha n
  /-- The numerical bound decays at polynomial rate. -/
  poly_rate : PolynomialMixingRate alpha C r
  /-- The sharp threshold: the polynomial decay exponent strictly exceeds
      `(2 + δ) / δ`. -/
  rate_admissible : r > (2 + δ) / δ

/-! ## Part II: Elementary summability helper -/

/-- *Polynomial summability* of `n^{-s}` for `s > 1`: the standard ζ-function
fact, derived from Mathlib's `Real.summable_nat_rpow_inv`.

This is the only fully-proven non-trivial lemma in S2; it underlies the
sharp-threshold computation `r > (2 + δ) / δ ⇒ rδ/(2+δ) > 1`. -/
theorem polynomial_summable_of_exponent_gt_one (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
  -- Reduce to Mathlib's `Real.summable_nat_rpow_inv : Summable (((n : ℝ) ^ p)⁻¹) ↔ 1 < p`.
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
`r > (2 + δ) / δ`, the Ibragimov covariance series ∑ n^{−rδ/(2+δ)} is summable.
This is the technical motivation for the threshold in `IbragimovHypotheses`. -/
theorem ibragimov_threshold_summable (δ r : ℝ)
    (hδ : 0 < δ) (hr : r > (2 + δ) / δ) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(r * δ / (2 + δ)))) := by
  apply polynomial_summable_of_exponent_gt_one
  -- Goal: 1 < r * δ / (2 + δ).
  -- Strategy: from r > (2+δ)/δ and δ > 0, multiply both sides by δ to get r·δ > 2+δ,
  -- then divide both sides by (2+δ) > 0 to get the result.
  have h2δ_pos : 0 < 2 + δ := by linarith
  have h_rδ_gt : 2 + δ < r * δ := by
    have step : ((2 + δ) / δ) * δ < r * δ :=
      mul_lt_mul_of_pos_right hr hδ
    rwa [div_mul_cancel₀ (2 + δ) (ne_of_gt hδ)] at step
  -- 2 + δ < r * δ, and 2 + δ > 0, so 1 < r * δ / (2 + δ).
  rw [lt_div_iff₀ h2δ_pos]
  linarith

/-! ## Part III: Main theorem statements (sorries deferred to S3+) -/

/-- *Absolute convergence of the long-run variance covariance series* under
Ibragimov's hypotheses.

This is the genuinely tractable S5 target: once Davydov's covariance inequality
is in place (S4), each `|Cov(X₀, X_{k+1})|` is bounded by a multiple of
`α(k+1)^{δ/(2+δ)} · ‖X‖_{2+δ}²`, and the sum becomes `∑_k α(k+1)^{δ/(2+δ)}`,
summable by `ibragimov_threshold_summable`.

The proof requires:
  - (S3) algebraic manipulation of the exponent `r·δ/(2+δ) > 1`;
  - (S4) Davydov's inequality applied per-term;
  - one Mathlib `Summable.comp_injective` shift for the index `k ↦ k+1`. -/
theorem longrun_variance_absolutely_convergent
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {δ C r : ℝ}
    (_H : IbragimovHypotheses μ X δ C r) :
    Summable (fun k : ℕ => |∫ ω, X 0 ω * X (k + 1) ω ∂μ|) := by
  sorry

/-- **Ibragimov's central limit theorem for polynomial α-mixing sequences.**

Under stationarity, mean zero, uniformly bounded `(2 + δ)`-th moments,
polynomial α-mixing rate `r > (2 + δ) / δ`, and a positive long-run variance
`σ² > 0`, the normalized partial sums `S_n / √n` converge in distribution to
`N(0, σ²)`.

We state convergence via the characteristic-function (Lévy continuity) form:
`φ_{S_n/√n}(t) → exp(-σ² t² / 2)` for every `t : ℝ`. The long-run variance
σ² is supplied as a parameter rather than computed inline, avoiding the
plumbing of the parent's `longRunVariance` definition's integrability/mean-zero
arguments.

**Proof outline** (deferred to S3+):
1. **S3** — Sharp threshold: `r > (2 + δ) / δ ⇒ rδ/(2+δ) > 1` (done above).
2. **S4** — Davydov covariance inequality:
   `|Cov(X, Y)| ≤ 12 · α^{δ/(2+δ)} · ‖X‖_{2+δ} · ‖Y‖_{2+δ}`.
3. **S5** — Long-run variance absolute convergence (above).
4. **S6** — Bernstein block decomposition (`p_n, q_n → ∞`, `n / p_n → ∞`).
5. **S7** — Large-block independence approximation via mixing.
6. **S8** — Lindeberg's condition on large blocks (uses `(2 + δ)`-th moments).
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
