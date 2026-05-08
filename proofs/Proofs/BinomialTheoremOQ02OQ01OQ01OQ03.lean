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
