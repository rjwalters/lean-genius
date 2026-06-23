/-
Central Limit Theorem OQ-02-OQ-02:
Complete the i.i.d. Lindeberg condition via dominated convergence for truncated moments.

CONTEXT: `Proofs/CentralLimitTheoremOQ02.lean` proves the classical CLT follows from the
martingale CLT *modulo* the i.i.d. Lindeberg condition. That step was left as a `sorry`
(line ~537) with the note "requires dominated convergence theorem for truncated moments".
This file supplies the missing analysis.

WHAT IS PROVED (axiom-free, 0 sorry):

1. `truncated_moment_tendsto_zero` — the genuine mathematical content:
   for a measurable `X` with `X²` integrable and any threshold sequence `a n → ∞`,
       ∫ X² · 1{|X| > a n}  →  0.
   This is the Lebesgue dominated convergence theorem applied with the integrable
   dominating function `X²`: for each fixed `ω`, once `a n` exceeds `|X ω|` the
   truncated integrand vanishes, so the integrands tend to `0` pointwise while being
   dominated by `X²`.

2. `iid_satisfies_lindeberg` — the i.i.d. Lindeberg condition, stated *honestly*.
   The Lindeberg sum for the row-scaled array `X_{n,k} = X_k / √n` collapses
       L_n(ε) = ∑_{k<n} ∫ (X_k/√n)² · 1{|X_k/√n| > ε}
              = ∫ X_0² · 1{|X_0| > ε√n}                    →  0   by (1) with a n = ε√n.
   The collapse uses an explicit identical-distribution hypothesis `hIdent` on the
   *truncated* second moments. This mirrors the situation already documented for
   `iid_satisfies_lyapunov` in the parent file: the `IIDSequence` structure only records
   independence and a common *full* second moment (`variance`), NOT identical higher- or
   truncated-moment distributions. The "identically distributed" half of i.i.d. is exactly
   what is needed here, so it is supplied explicitly rather than smuggled in.

This is the complete, machine-checked version of the parent file's line-537 `sorry`.
-/

import Proofs.CentralLimitTheoremOQ02
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open MeasureTheory Filter

namespace CentralLimitTheoremOQ02OQ02

open CentralLimitTheoremOQ02

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Dominated convergence for truncated second moments.**
If `X²` is integrable and the truncation levels `a n → ∞`, then the truncated second
moments `∫ X² · 1{|X| > a n}` tend to `0`.

Proof: apply the Lebesgue dominated convergence theorem with dominating function `X²`.
For each `ω`, once `a n > |X ω|` the indicator is `0`, so the integrands vanish
pointwise; they are bounded by `X²` throughout. -/
theorem truncated_moment_tendsto_zero
    {μ : Measure Ω}
    (X : Ω → ℝ) (hX : Measurable X)
    (hXsq : Integrable (fun ω => (X ω) ^ 2) μ)
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => ∫ ω, (X ω) ^ 2 * (if |X ω| > a n then 1 else 0) ∂μ)
      atTop (nhds 0) := by
  -- Measurability of each truncation set Sₙ = {ω | a n < |X ω|}.
  have hSm : ∀ n, MeasurableSet {ω | a n < |X ω|} := fun n =>
    measurableSet_lt measurable_const hX.abs
  -- Rewrite the product integrand `X² · 1{|X| > a n}` as `indicator Sₙ (X²)`.
  have hindic : (fun n => ∫ ω, (X ω) ^ 2 * (if |X ω| > a n then 1 else 0) ∂μ)
      = fun n => ∫ ω, Set.indicator {ω | a n < |X ω|} (fun ω => (X ω) ^ 2) ω ∂μ := by
    funext n
    congr 1
    funext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq, gt_iff_lt, mul_ite, mul_one, mul_zero]
  rw [hindic]
  -- Dominated convergence: limit function is `0`, dominating function is `X²`.
  have key : Tendsto
      (fun n => ∫ ω, Set.indicator {ω | a n < |X ω|} (fun ω => (X ω) ^ 2) ω ∂μ)
      atTop (nhds (∫ _ω : Ω, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => (X ω) ^ 2) ?_ hXsq ?_ ?_
    · -- each indicator integrand is a.e.-strongly-measurable
      intro n
      exact (aestronglyMeasurable_indicator_iff (hSm n)).mpr
        hXsq.integrableOn.aestronglyMeasurable
    · -- dominated by `X²`
      intro n
      refine Eventually.of_forall (fun ω => ?_)
      calc ‖Set.indicator {ω | a n < |X ω|} (fun ω => (X ω) ^ 2) ω‖
          ≤ ‖(X ω) ^ 2‖ := norm_indicator_le_norm_self _ _
        _ = (X ω) ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    · -- pointwise convergence to `0`
      refine Eventually.of_forall (fun ω => ?_)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [ha.eventually_gt_atTop (|X ω|)] with n hn
      exact (Set.indicator_of_notMem (by simp only [Set.mem_setOf_eq]; exact not_lt.mpr hn.le) _).symm
  simpa using key

/-- **The i.i.d. Lindeberg condition.**

For an `IIDSequence` together with an explicit identical-distribution hypothesis `hIdent`
on the truncated second moments, the row-scaled martingale-difference array `X_k / √n`
satisfies the Lindeberg condition.

`hIdent c k : ∫ X_k² · 1{|X_k| > c} = ∫ X_0² · 1{|X_0| > c}` records the "identically
distributed" content that the `IIDSequence` structure does not encode (it stores only a
common *full* second moment). With it, the Lindeberg sum at level `ε` for row `n ≥ 1`
collapses to `∫ X_0² · 1{|X_0| > ε√n}`, which `→ 0` by `truncated_moment_tendsto_zero`. -/
theorem iid_satisfies_lindeberg
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : IIDSequence Ω μ)
    (hIdent : ∀ (c : ℝ) (k : ℕ),
        ∫ ω, (S.X k ω) ^ 2 * (if |S.X k ω| > c then 1 else 0) ∂μ
      = ∫ ω, (S.X 0 ω) ^ 2 * (if |S.X 0 ω| > c then 1 else 0) ∂μ) :
    S.toMDA.lindebergCondition := by
  intro ε hε
  -- √n tends to ∞, hence so does ε·√n.
  have hsqrt_top : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop := by
    simp_rw [Real.sqrt_eq_rpow]
    exact (Real.tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  -- For each row n ≥ 1 the Lindeberg sum collapses to a single truncated moment of X₀.
  have hred : ∀ n : ℕ, 1 ≤ n →
      S.toMDA.lindebergSum n ε
        = ∫ ω, (S.X 0 ω) ^ 2 * (if |S.X 0 ω| > ε * Real.sqrt n then 1 else 0) ∂μ := by
    intro n hn
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    -- Per-term reduction: ∫ (X_k/√n)²·1{|X_k/√n|>ε} = (∫ X_k²·1{|X_k|>ε√n}) / n.
    have hterm : ∀ k : ℕ,
        (∫ ω, (S.X k ω / Real.sqrt n) ^ 2
              * (if |S.X k ω / Real.sqrt n| > ε then 1 else 0) ∂μ)
          = (∫ ω, (S.X k ω) ^ 2
                * (if |S.X k ω| > ε * Real.sqrt n then 1 else 0) ∂μ) / n := by
      intro k
      rw [← integral_div]
      refine integral_congr_ae (Eventually.of_forall (fun ω => ?_))
      have hcond : (|S.X k ω / Real.sqrt n| > ε)
          ↔ (|S.X k ω| > ε * Real.sqrt n) := by
        rw [gt_iff_lt, gt_iff_lt, abs_div, abs_of_nonneg (Real.sqrt_nonneg _),
          lt_div_iff₀ hsqrt_pos]
      rw [div_pow, Real.sq_sqrt hn_pos.le, if_congr hcond rfl rfl, div_mul_eq_mul_div]
    -- Sum over the row, then apply identical distribution and cancel the 1/n.
    simp only [MartingaleDiffArray.lindebergSum, IIDSequence.toMDA]
    have hsum : ∀ k ∈ Finset.range n,
        (∫ ω, (S.X k ω / Real.sqrt n) ^ 2
              * (if |S.X k ω / Real.sqrt n| > ε then 1 else 0) ∂μ)
          = (∫ ω, (S.X 0 ω) ^ 2
                * (if |S.X 0 ω| > ε * Real.sqrt n then 1 else 0) ∂μ) / n := by
      intro k _
      rw [hterm k, hIdent (ε * Real.sqrt n) k]
    rw [Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_div_assoc', mul_div_cancel_left₀ _ hn_ne]
  -- Conclude: the collapsed sequence tends to 0 by dominated convergence.
  refine Tendsto.congr' ?_
    (truncated_moment_tendsto_zero (S.X 0) (S.measurable 0) (S.sq_integrable 0)
      (fun n => ε * Real.sqrt n) ((tendsto_const_mul_atTop_of_pos hε).mpr hsqrt_top))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hred n hn).symm

end CentralLimitTheoremOQ02OQ02
