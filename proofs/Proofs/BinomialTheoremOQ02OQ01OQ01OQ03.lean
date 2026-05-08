/-
# Multinomial Marginal Central Limit Theorem

**Open Question** (binomial-theorem-oq-02-oq-01-oq-01-oq-03):
"Multinomial marginal CLT in Lean: does (Xᵢ - npᵢ) / √(npᵢ(1-pᵢ)) converge in
distribution to N(0,1) for each coordinate as n → ∞?"

## Status

**Reduction complete.** This file STATES the multinomial marginal CLT
and reduces it to the classical de Moivre–Laplace (binomial) CLT plus the
already-proved marginal-PMF identity from `BinomialTheoremOQ02OQ01OQ02`.
The reduction lemma `multinomialMarginalCDF_eq_binomialCDF` is now fully
proved (Phase-3 deliverable, this file).

The de Moivre–Laplace CLT itself is taken as an axiom: a measure-theoretic
proof from Mathlib's `ProbabilityTheory.iid_central_limit_theorem` is
non-trivial (CDF ↔ measure-weak-convergence bridge) and is left for a
follow-up effort. After this file, the single mathematical assumption
beyond Mathlib is the classical Binomial CLT itself.

## What This File Provides

1. `binomialCDF n p x` — concrete CDF of Binomial(n, p), defined as
   ∑_{j ≤ x} C(n,j) p^j (1-p)^(n-j).
2. `multinomialMarginalCDF s p n i₀ x` — concrete CDF of the marginal X_{i₀}
   of Multinomial(n, p), defined by summing `multinomialProb` over the
   filtered piAntidiag.
3. `standardNormalCDF` — concrete `noncomputable def` integrating
   Mathlib's `ProbabilityTheory.gaussianPDFReal 0 1` over `Set.Iic x`,
   plus the elementary properties `_nonneg`, `_le_one`, `_mono`.
4. `binomial_clt_pointwise` — AXIOM: pointwise convergence of standardized
   binomial CDF to standardNormalCDF.
5. `multinomialMarginalCDF_eq_binomialCDF` — reduction lemma, **proved**:
   the marginal CDF of the multinomial equals the binomial CDF with
   parameter p(i₀). Proof regroups `∑ k ∈ s.piAntidiag n` into fibers
   over `j = k(i₀)` via `Finset.sum_fiberwise_of_maps_to`, then applies
   `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`.
6. `multinomial_marginal_clt` — DERIVED THEOREM (no axiom of its own).
   Combines (4) and (5) via `Filter.Tendsto.congr`.

## Mathematical Content

For (X₁, ..., Xₖ) ~ Multinomial(n, p₁, ..., pₖ), each marginal Xᵢ ~ Binomial(n, pᵢ)
(this was proved in `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`).
The classical de Moivre–Laplace theorem gives:

    P( (X − np) / √(np(1−p)) ≤ x )  →  Φ(x)    as n → ∞

for any x ∈ ℝ, where Φ is the standard normal CDF. Composing these two facts
gives the multinomial marginal CLT.

## Honest Reporting

- Sorries: 0 (Phase-3 reduction-lemma proof discharges the prior sorry).
- Axioms: 1 (`binomial_clt_pointwise`). The Session-2 `standardNormalCDF`
  opaque was replaced in Session 6 with a concrete `noncomputable def`
  using Mathlib's `gaussianPDFReal`.
- Status: axiomatized — not "verified".
- Session 7 (this session) adds two boundary-saturation lemmas
  `binomialCDF_zero` and `binomialCDF_eq_one`, completing the four-corner
  characterization of `binomialCDF` (`_neg` left-tail = 0, `_eq_one`
  right-tail = 1, `_zero_le` lower bound, `_le_one` upper bound). These
  feed the Phase-4 Portmanteau bridge that aims to discharge
  `binomial_clt_pointwise`.

The contribution of this file is the *full reduction* of the multinomial
marginal CLT to the classical Binomial CLT, leaving only the latter as
an explicit named assumption.

## Why CDF formulation

Mathlib's CLT (`ProbabilityTheory.iid_central_limit_theorem`) is stated in
terms of measure-weak-convergence of the law of standardized sums to the
Gaussian measure. Our statement is in CDF form to (a) avoid the heavy
measure-theory setup for a marginal-only result, (b) match the classical
"de Moivre–Laplace" presentation, and (c) keep the reduction to the
already-proved marginal-PMF identity transparent.

## Dependencies

- `BinomialTheoremOQ02OQ01OQ02` — `multinomialProb`, `multinomial_marginal_pmf`
- Mathlib — `Real.sqrt`, `Filter.Tendsto`, `nhds`
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ01OQ02

namespace BinomialTheoremOQ02OQ01OQ01OQ03

open Finset BigOperators

/-! ## CDF definitions -/

/-- The CDF of Binomial(n, p) at `x`:
    `binomialCDF n p x = ∑_{j ≤ x, 0 ≤ j ≤ n} C(n, j) · p^j · (1 - p)^(n - j)`.

    No constraints on `p` are enforced at the definition level; the axiom
    `binomial_clt_pointwise` requires `0 < p < 1`. -/
noncomputable def binomialCDF (n : ℕ) (p : ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    if (j : ℝ) ≤ x then
      (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j)
    else 0

/-- The marginal CDF of coordinate `i₀` for X ~ Multinomial(n, p). -/
noncomputable def multinomialMarginalCDF
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (i₀ : α) (x : ℝ) : ℝ :=
  ∑ k ∈ s.piAntidiag n,
    if ((k i₀ : ℕ) : ℝ) ≤ x then
      BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k
    else 0

/-! ## Standard normal CDF -/

/-- The standard normal CDF,
    `Φ(x) = ∫_{-∞}^x (1/√(2π)) · exp(-t²/2) dt`.

    Defined concretely as the Lebesgue integral of Mathlib's
    `ProbabilityTheory.gaussianPDFReal 0 1` over `Set.Iic x`. Replaces
    the Session-2 `opaque standardNormalCDF` marker; this removes that
    declaration from the file's assumption count. -/
noncomputable def standardNormalCDF (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, ProbabilityTheory.gaussianPDFReal 0 1 t

/-- The standard normal CDF is non-negative — the integral of a
    non-negative density over a measurable set is non-negative. -/
theorem standardNormalCDF_nonneg (x : ℝ) : 0 ≤ standardNormalCDF x := by
  unfold standardNormalCDF
  exact MeasureTheory.setIntegral_nonneg_of_ae
    (Filter.Eventually.of_forall (ProbabilityTheory.gaussianPDFReal_nonneg 0 1))

/-- The standard normal CDF is at most `1` — the integral over `(−∞, x]`
    is bounded above by the total integral, which equals `1` by
    `ProbabilityTheory.integral_gaussianPDFReal_eq_one`. -/
theorem standardNormalCDF_le_one (x : ℝ) : standardNormalCDF x ≤ 1 := by
  have h_total : ∫ t, ProbabilityTheory.gaussianPDFReal 0 1 t = 1 :=
    ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero
  unfold standardNormalCDF
  rw [← h_total]
  exact MeasureTheory.setIntegral_le_integral
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1)
    (Filter.Eventually.of_forall (ProbabilityTheory.gaussianPDFReal_nonneg 0 1))

/-- The standard normal CDF is monotone in `x` — the integrand is
    non-negative and `Set.Iic x ⊆ Set.Iic y` whenever `x ≤ y`. -/
theorem standardNormalCDF_mono : Monotone standardNormalCDF := by
  intro x y hxy
  unfold standardNormalCDF
  exact MeasureTheory.setIntegral_mono_set
    ((ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn)
    (Filter.Eventually.of_forall (ProbabilityTheory.gaussianPDFReal_nonneg 0 1))
    (Set.Iic_subset_Iic.mpr hxy).eventuallyLE

/-- The standard normal CDF, evaluated at `x`, equals the constant
    `standardNormalCDF 0` plus the (interval-)integral of the standard normal
    PDF from `0` to `x`. This bridge lemma is the input to the continuity
    proof: the LHS is a `setIntegral` over `Iic x`; the RHS is decomposed as a
    constant plus an `intervalIntegral` whose primitive form is continuous via
    `MeasureTheory.Integrable.continuous_primitive`.

    Proof: both `∫ Iic x` and `∫ Iic 0` are limits of `∫ a..x` and `∫ a..0`
    as `a → -∞` (`MeasureTheory.intervalIntegral_tendsto_integral_Iic`). For
    each `a`, the adjacent-intervals identity
    `∫ a..x = ∫ a..0 + ∫ 0..x` holds. Taking limits and using `tendsto_nhds_unique`
    closes the equation. -/
private lemma standardNormalCDF_eq_zero_plus_intervalIntegral (x : ℝ) :
    standardNormalCDF x = standardNormalCDF 0
      + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
  have hf_int : MeasureTheory.Integrable (ProbabilityTheory.gaussianPDFReal 0 1) :=
    ProbabilityTheory.integrable_gaussianPDFReal 0 1
  -- The function `y ↦ ∫ t in y..x, f t` tends to `standardNormalCDF x` at `atBot`.
  have h_lim_x : Filter.Tendsto
      (fun y : ℝ => ∫ t in y..x, ProbabilityTheory.gaussianPDFReal 0 1 t)
      Filter.atBot (nhds (standardNormalCDF x)) := by
    unfold standardNormalCDF
    exact MeasureTheory.intervalIntegral_tendsto_integral_Iic x
      hf_int.integrableOn Filter.tendsto_id
  -- The function `y ↦ ∫ t in y..0, f t` tends to `standardNormalCDF 0` at `atBot`.
  have h_lim_0 : Filter.Tendsto
      (fun y : ℝ => ∫ t in y..(0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 t)
      Filter.atBot (nhds (standardNormalCDF 0)) := by
    unfold standardNormalCDF
    exact MeasureTheory.intervalIntegral_tendsto_integral_Iic 0
      hf_int.integrableOn Filter.tendsto_id
  -- Adjacent-intervals identity: rewrite `∫ y..x` as `∫ y..0 + ∫ 0..x`.
  have hfn_eq : (fun y : ℝ => ∫ t in y..x, ProbabilityTheory.gaussianPDFReal 0 1 t) =
      fun y : ℝ => (∫ t in y..(0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 t)
        + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
    funext y
    have hab : IntervalIntegrable
        (ProbabilityTheory.gaussianPDFReal 0 1) MeasureTheory.volume y 0 :=
      hf_int.intervalIntegrable
    have hbc : IntervalIntegrable
        (ProbabilityTheory.gaussianPDFReal 0 1) MeasureTheory.volume 0 x :=
      hf_int.intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals hab hbc).symm
  rw [hfn_eq] at h_lim_x
  -- The rewritten LHS is a sum-of-tendsto: the first summand → standardNormalCDF 0,
  -- and the second is constant. So the limit is standardNormalCDF 0 + ∫ 0..x.
  have h_lim_rhs : Filter.Tendsto
      (fun y : ℝ => (∫ t in y..(0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 t)
        + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t)
      Filter.atBot
      (nhds (standardNormalCDF 0
        + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t)) :=
    h_lim_0.add_const _
  exact tendsto_nhds_unique h_lim_x h_lim_rhs

/-- **The standard normal CDF is continuous on `ℝ`.**

    Strategy: rewrite `standardNormalCDF` as `standardNormalCDF 0 +
    intervalIntegral 0..x` (`standardNormalCDF_eq_zero_plus_intervalIntegral`),
    then apply `MeasureTheory.Integrable.continuous_primitive` to the
    interval-primitive piece. The `NoAtoms volume` instance on `ℝ` is the
    measure-theoretic input that makes the primitive continuous.

    On the **Portmanteau-bridge critical path** for Phase-4 axiom elimination:
    Portmanteau converts measure-weak-convergence into pointwise convergence
    of CDFs at every continuity point of the limit CDF. Since `Φ` is
    continuous everywhere, every `x ∈ ℝ` is a continuity point, so the
    convergence is universal. Combined with the four `binomialCDF_*` lemmas
    (Sessions 4–5) and the three `standardNormalCDF_{nonneg,le_one,mono}`
    lemmas (Session 6), this completes the structural-properties library
    for the Phase-4 Portmanteau bridge that next session will build to
    discharge `binomial_clt_pointwise`. -/
theorem standardNormalCDF_continuous : Continuous standardNormalCDF := by
  have hfeq : standardNormalCDF = fun x : ℝ => standardNormalCDF 0
      + ∫ t in (0 : ℝ)..x, ProbabilityTheory.gaussianPDFReal 0 1 t := by
    funext x
    exact standardNormalCDF_eq_zero_plus_intervalIntegral x
  rw [hfeq]
  exact continuous_const.add
    ((ProbabilityTheory.integrable_gaussianPDFReal 0 1).continuous_primitive 0)

/-! ## Axiom: classical de Moivre–Laplace (binomial CLT) -/

/-- **AXIOM** (de Moivre–Laplace, 1733/1812): the standardized binomial CDF
    converges pointwise to the standard normal CDF as `n → ∞`.

    For `0 < p < 1` and any `x : ℝ`,
    `binomialCDF n p (np + x √(np(1−p)))  →  Φ(x)`.

    Mathematical justification: classical, see e.g. Feller, *Introduction to
    Probability Theory*, Vol. I (1968), Ch. VII §3. The Mathlib path is via
    `ProbabilityTheory.iid_central_limit_theorem` plus a CDF-bridge; recorded
    as an axiom here (Phase-3 target). -/
axiom binomial_clt_pointwise
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        binomialCDF n p ((n : ℝ) * p + x * Real.sqrt ((n : ℝ) * p * (1 - p))))
      Filter.atTop (nhds (standardNormalCDF x))

/-! ## Reduction lemma -/

/-- For any composition `k ∈ s.piAntidiag n`, every coordinate is at most `n`. -/
private lemma piAntidiag_apply_le {α : Type*} [DecidableEq α]
    (s : Finset α) (n : ℕ) (i₀ : α) :
    ∀ k ∈ s.piAntidiag n, k i₀ ≤ n := by
  intro k hk
  rw [Finset.mem_piAntidiag] at hk
  obtain ⟨hksum, hksup⟩ := hk
  by_cases h : i₀ ∈ s
  · -- i₀ ∈ s: bound by the sum.
    have hle : k i₀ ≤ ∑ i ∈ s, k i :=
      Finset.single_le_sum (s := s) (f := k) (fun i _ => Nat.zero_le _) h
    omega
  · -- i₀ ∉ s: support condition forces k i₀ = 0.
    by_contra hne
    push_neg at hne
    have h1 : k i₀ ≠ 0 := by omega
    exact h (hksup i₀ h1)

/-- **Reduction lemma**: the marginal CDF of the multinomial equals the
    binomial CDF with parameter `p(i₀)`.

    Proof: regroup `∑ k ∈ s.piAntidiag n` into fibers over the value
    `j = k i₀` for `j ∈ {0, ..., n}` via `Finset.sum_fiberwise_of_maps_to`;
    on each fiber, the `if`-guard `((k i₀ : ℕ) : ℝ) ≤ x` simplifies to
    `(j : ℝ) ≤ x` (since `k i₀ = j` is the fiber predicate), which is
    constant in `k` and so factors out; the inner fiber-sum then collapses
    to `C(n, j) · p(i₀)^j · (1 − p(i₀))^(n − j)` by
    `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf` (Sublemma A). -/
theorem multinomialMarginalCDF_eq_binomialCDF
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (x : ℝ) :
    multinomialMarginalCDF s p n i₀ x = binomialCDF n (p i₀) x := by
  unfold multinomialMarginalCDF binomialCDF
  -- Fibre-decompose the multinomial sum along `j := k i₀ ∈ Finset.range (n+1)`.
  have hmaps : ∀ k ∈ s.piAntidiag n, k i₀ ∈ Finset.range (n + 1) := by
    intro k hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact piAntidiag_apply_le s n i₀ k hk
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (g := fun k =>
          if ((k i₀ : ℕ) : ℝ) ≤ x
          then BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k
          else 0)]
  -- Now compare term-by-term across the outer index `j ∈ Finset.range (n+1)`.
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  by_cases hcond : (j : ℝ) ≤ x
  · -- True branch: inner indicator collapses, then apply Sublemma A.
    rw [if_pos hcond]
    have h_inner :
        ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
            (if ((k i₀ : ℕ) : ℝ) ≤ x
             then BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k
             else 0)
        = ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
            BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [hk.2, if_pos hcond]
    rw [h_inner]
    exact BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf
            s p n hp i₀ hi₀ j hj
  · -- False branch: every term in the fibre is 0.
    rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hk.2, if_neg hcond]

/-! ## Structural properties of `binomialCDF` (Phase-4 prep) -/

/-- For `x < 0`, `binomialCDF n p x = 0`. Every `j ∈ {0, …, n}` satisfies
    `(j : ℝ) ≥ 0 > x`, so the if-guard is false in every term. -/
theorem binomialCDF_neg (n : ℕ) (p : ℝ) {x : ℝ} (hx : x < 0) :
    binomialCDF n p x = 0 := by
  unfold binomialCDF
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (not_le.mpr (lt_of_lt_of_le hx (Nat.cast_nonneg j)))]

/-- `binomialCDF n p` is monotone in `x`, when `0 ≤ p ≤ 1`.

    Each summand is either `0` or the binomial PMF
    `C(n, j) · p^j · (1 − p)^(n − j)`, which is non-negative under the
    standing hypothesis `0 ≤ p ≤ 1`. As `x` increases, more if-guards
    become true, so each summand is non-decreasing.

    Useful for the Phase-4 Portmanteau bridge: continuous monotone CDFs
    characterize weak convergence on `ℝ`. -/
theorem binomialCDF_mono (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Monotone (binomialCDF n p) := by
  intro x y hxy
  unfold binomialCDF
  apply Finset.sum_le_sum
  intro j _
  by_cases hjx : (j : ℝ) ≤ x
  · rw [if_pos hjx, if_pos (le_trans hjx hxy)]
  · rw [if_neg hjx]
    by_cases hjy : (j : ℝ) ≤ y
    · rw [if_pos hjy]
      have h1mp : 0 ≤ 1 - p := by linarith
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
        (pow_nonneg h1mp _)
    · rw [if_neg hjy]

/-- For `0 ≤ p ≤ 1`, every value of `binomialCDF n p` is non-negative.

    Each summand is either `0` (if-guard false) or the binomial PMF
    `C(n, j) · p^j · (1 − p)^(n − j)`, which is non-negative since
    `Nat.choose n j ≥ 0`, `p ≥ 0`, and `1 − p ≥ 0`. The sum of
    non-negative terms is non-negative.

    Useful for the Phase-4 Portmanteau bridge: weak-convergence
    arguments for measures often pull back to non-negativity of CDFs. -/
theorem binomialCDF_zero_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ℝ) : 0 ≤ binomialCDF n p x := by
  have h1mp : 0 ≤ 1 - p := by linarith
  unfold binomialCDF
  apply Finset.sum_nonneg
  intro j _
  split_ifs with hjx
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
      (pow_nonneg h1mp _)
  · exact le_refl 0

/-- For `0 ≤ p ≤ 1`, every value of `binomialCDF n p` is at most `1`.

    Proof: the full unrestricted sum
    `∑_{j=0}^{n} C(n, j) · p^j · (1 − p)^(n − j) = (p + (1 − p))^n = 1`
    by the binomial theorem (`add_pow`). The CDF replaces some summands
    with `0`; under the hypothesis `0 ≤ p ≤ 1` each summand is
    non-negative, so dropping terms only decreases the total.

    Useful for the Phase-4 Portmanteau bridge: weak-convergence is
    typically formulated for sub-probability measures, and bounded
    CDFs on `[0, 1]` characterize the standard normal in the limit. -/
theorem binomialCDF_le_one (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ℝ) : binomialCDF n p x ≤ 1 := by
  have h1mp : 0 ≤ 1 - p := by linarith
  -- Step 1: rewrite `1` as the binomial expansion of `(p + (1 − p))^n`.
  have hexp : ∑ j ∈ Finset.range (n + 1),
      (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j) = 1 := by
    have hadd := add_pow p (1 - p) n
    have hp_eq : p + (1 - p) = (1 : ℝ) := by ring
    rw [hp_eq, one_pow] at hadd
    -- hadd : (1 : ℝ) = ∑ k, p^k * (1 − p)^(n−k) * (Nat.choose n k : ℝ)
    rw [← hadd]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  -- Step 2: replace `1` on the RHS with the equivalent sum.
  rw [← hexp]
  -- Step 3: term-by-term comparison.
  unfold binomialCDF
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hjx
  · exact le_refl _
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
      (pow_nonneg h1mp _)

/-- At `x = 0`, only the `j = 0` term contributes to `binomialCDF n p`;
    every other `j ∈ {1, …, n}` has `(j : ℝ) ≥ 1 > 0`, failing the
    if-guard. The surviving term simplifies to
    `C(n, 0) · p^0 · (1 − p)^(n − 0) = (1 − p)^n`.

    Useful for the Phase-4 Portmanteau bridge: the boundary value at
    `x = 0` (i.e., the probability of zero successes) is the only
    closed-form value of the CDF, and it appears in the standardised
    threshold `np + x √(np(1−p))` when `x = -√(np/(1-p))`. -/
theorem binomialCDF_zero (n : ℕ) (p : ℝ) :
    binomialCDF n p 0 = (1 - p) ^ n := by
  unfold binomialCDF
  -- Reduce the sum to its single non-zero term `j = 0`.
  rw [Finset.sum_eq_single 0]
  · -- j = 0: if-guard `(0 : ℝ) ≤ 0` holds; the term is `1 · 1 · (1 − p)^n`.
    simp [Nat.choose_zero_right]
  · -- For `j ≠ 0` in the range, if-guard `(j : ℝ) ≤ 0` is false.
    intro j _ hjne
    have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
    have hj_not_le : ¬ (j : ℝ) ≤ 0 := by
      push_neg
      exact_mod_cast hjpos
    rw [if_neg hj_not_le]
  · -- `0 ∈ Finset.range (n+1)` is automatic.
    intro h
    exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ _)) h

/-- For `0 ≤ p ≤ 1` and any `x` with `(n : ℝ) ≤ x`, every if-guard
    `(j : ℝ) ≤ x` is satisfied (since `j ∈ {0, …, n}` gives
    `(j : ℝ) ≤ (n : ℝ) ≤ x`). The sum then equals the full binomial
    expansion `(p + (1 − p))^n = 1`.

    Useful for the Phase-4 Portmanteau bridge: the right-tail
    saturation `binomialCDF n p x = 1` for `x ≥ n` mirrors
    `Φ(x) → 1` as `x → ∞` for the standard normal. The companion
    `binomialCDF_neg` gives the matching left-tail saturation. -/
theorem binomialCDF_eq_one (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {x : ℝ} (hx : (n : ℝ) ≤ x) : binomialCDF n p x = 1 := by
  unfold binomialCDF
  -- All if-guards collapse to the true branch.
  have h_simp : ∀ j ∈ Finset.range (n + 1),
      (if (j : ℝ) ≤ x then (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j) else 0)
      = (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    have hjx : (j : ℝ) ≤ x := le_trans (by exact_mod_cast hj) hx
    rw [if_pos hjx]
  rw [Finset.sum_congr rfl h_simp]
  -- Apply the binomial theorem to identify with `(p + (1 − p))^n = 1`.
  have hadd := add_pow p (1 - p) n
  have hp_eq : p + (1 - p) = (1 : ℝ) := by ring
  rw [hp_eq, one_pow] at hadd
  rw [← hadd]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **Right-tail asymptote of `binomialCDF`.** As `x → +∞`, the binomial
    CDF tends to `1` (under `0 ≤ p ≤ 1`).

    Proof: by `binomialCDF_eq_one`, `binomialCDF n p x = 1` for every
    `x` with `(n : ℝ) ≤ x`; the predicate `(n : ℝ) ≤ x` holds eventually
    along `Filter.atTop` (`Filter.eventually_ge_atTop`), so the function
    is *eventually constant equal to `1`* and the limit is `1`.

    Companion to `standardNormalCDF_tendsto_one_atTop`: paired right-tail
    saturation feeding the Phase-4 Portmanteau bridge. -/
theorem binomialCDF_tendsto_one_atTop (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Filter.Tendsto (binomialCDF n p) Filter.atTop (nhds 1) := by
  have h : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (n : ℝ)] with x hx
  exact (binomialCDF_eq_one n hp0 hp1 hx).symm

/-- **Left-tail asymptote of `binomialCDF`.** As `x → -∞`, the binomial
    CDF tends to `0`.

    Proof: by `binomialCDF_neg`, `binomialCDF n p x = 0` for every `x < 0`;
    the predicate `x < 0` holds eventually along `Filter.atBot`
    (`Filter.eventually_lt_atBot`), so the function is *eventually constant
    equal to `0`* and the limit is `0`. No constraints on `p` are needed:
    `binomialCDF_neg` already holds for arbitrary `p`.

    The matching `standardNormalCDF_tendsto_zero_atBot` (Φ's left-tail
    saturation) is the next structural-CDF prerequisite for the
    Phase-4 Portmanteau bridge. -/
theorem binomialCDF_tendsto_zero_atBot (n : ℕ) (p : ℝ) :
    Filter.Tendsto (binomialCDF n p) Filter.atBot (nhds 0) := by
  have h : Filter.Tendsto (fun _ : ℝ => (0 : ℝ)) Filter.atBot (nhds 0) :=
    tendsto_const_nhds
  refine h.congr' ?_
  filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with x hx
  exact (binomialCDF_neg n p hx).symm

/-! ## Main theorem: multinomial marginal CLT (derived) -/

/-- **Multinomial marginal CLT** (DERIVED THEOREM, no separate axiom):
    for X ~ Multinomial(n, p), each non-degenerate marginal `Xᵢ` has the
    standardized CDF converging pointwise to `Φ(x)`.

    Proof: combine the de Moivre–Laplace axiom (`binomial_clt_pointwise`)
    with the reduction lemma (`multinomialMarginalCDF_eq_binomialCDF`)
    via `Filter.Tendsto.congr`. -/
theorem multinomial_marginal_clt
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (hp0 : 0 < p i₀) (hp1 : p i₀ < 1) (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        multinomialMarginalCDF s p n i₀
          ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀))))
      Filter.atTop (nhds (standardNormalCDF x)) := by
  have key : ∀ n : ℕ,
      multinomialMarginalCDF s p n i₀
        ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀))) =
      binomialCDF n (p i₀)
        ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀))) := by
    intro n
    exact multinomialMarginalCDF_eq_binomialCDF s p n hp i₀ hi₀ _
  exact (binomial_clt_pointwise (p i₀) hp0 hp1 x).congr (fun n => (key n).symm)

end BinomialTheoremOQ02OQ01OQ01OQ03
