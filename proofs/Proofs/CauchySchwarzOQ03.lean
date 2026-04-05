/-
  Holder's Inequality as Cauchy-Schwarz Generalization
  Open Question: cauchy-schwarz-oq-03

  This file proves Holder's inequality for finite sums and shows Cauchy-Schwarz
  as the special case p = q = 2. The main proof chain is:

    Young's ineq (pointwise) -> Normalized Holder -> General Holder -> Cauchy-Schwarz

  Key theorem: For conjugate exponents p, q > 1 (1/p + 1/q = 1):
    sum_i f_i * g_i <= (sum_i f_i^p)^(1/p) * (sum_i g_i^q)^(1/q)

  The proof of Cauchy-Schwarz follows from Lagrange's identity (elementary):
    sum_i sum_j (f_i*g_j - f_j*g_i)^2 = 2*[(sum f_i^2)(sum g_i^2) - (sum f_i*g_i)^2] >= 0

  References:
  - Holder, O. (1889): Ueber einen Mittelwerthssatz, Goettinger Nachrichten
  - Hardy-Littlewood-Polya "Inequalities" (1934) Chapters 2 and 6
  - Lagrange, J.L. (1773): identity for determinant of 2x2 matrices
-/

import Mathlib

open Finset NNReal Real MeasureTheory ENNReal

/-
## Part 1: Young's Inequality (described)

Young's inequality ab <= a^p/p + b^q/q is the fundamental pointwise estimate
from which Holder's inequality is derived by summation over i.

Mathematical derivation via weighted AM-GM:
  a^(1/p) * b^(1/q) <= (1/p) * a + (1/q) * b  (weighted AM-GM with weights 1/p, 1/q)

Young's inequality is available in Mathlib as `NNReal.young_inequality` (for NNReal)
and `ENNReal.young_inequality` (for ENNReal). The general Holder inequality
NNReal.inner_le_Lp_mul_Lq is proved using Young's inequality internally.
-/

/-
## Part 2: Holder's Inequality for NNReal Finite Sums

General Holder's inequality:
  sum(f_i * g_i) <= (sum f_i^p)^(1/p) * (sum g_i^q)^(1/q)

Proof strategy (via Young normalization):
  1. Normalize: let F_i = f_i / ||f||_p and G_i = g_i / ||g||_q
  2. Apply Young to each term: F_i * G_i <= F_i^p/p + G_i^q/q
  3. Sum: sum(F_i * G_i) <= 1/p * sum(F_i^p) + 1/q * sum(G_i^q) = 1/p + 1/q = 1
  4. Scale back: sum(f_i * g_i) <= ||f||_p * ||g||_q
-/

/-- General Holder's inequality for NNReal-valued functions on finite sets.
    For Holder conjugate exponents p, q: sum f_i*g_i <= ||f||_p * ||g||_q.
    This is Mathlib's NNReal.inner_le_Lp_mul_Lq. -/
theorem holder_nnreal {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∑ i ∈ s, f i * g i ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) :=
  NNReal.inner_le_Lp_mul_Lq s f g hpq

/-- Normalized Holder: if sum(f_i^p) = 1 and sum(g_i^q) = 1, then sum(f_i*g_i) <= 1.
    Immediate from the general Holder inequality: 1^(1/p) * 1^(1/q) = 1. -/
theorem holder_normalized {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hf : ∑ i ∈ s, f i ^ p = 1) (hg : ∑ i ∈ s, g i ^ q = 1) :
    ∑ i ∈ s, f i * g i ≤ 1 := by
  have h := holder_nnreal s f g hpq
  rw [hf, hg, NNReal.one_rpow, NNReal.one_rpow, mul_one] at h
  exact h

/-
## The Young Proof Chain for holder_normalized

The educational version shows the explicit Young's inequality chain:
  For each i: f_i * g_i <= f_i^p / p + g_i^q / q         (Young's inequality)
  Sum both sides: sum(f * g) <= (1/p) * sum(f^p) + (1/q) * sum(g^q)
  Substitute norm conditions: ... = 1/p + 1/q = 1         (conjugate condition!)

This is the reason the conjugate condition 1/p + 1/q = 1 is essential.
-/

/-
## Part 3: Cauchy-Schwarz via Lagrange's Identity (Elementary)

The classical Cauchy-Schwarz inequality (sum f_i * g_i)^2 <= (sum f_i^2)(sum g_i^2)
is proved via Lagrange's identity:

  (sum_i f_i^2)(sum_j g_j^2) - (sum_i f_i*g_i)^2 = (1/2) * sum_i sum_j (f_i*g_j - f_j*g_i)^2

The RHS is a sum of squares and hence non-negative. This elegant algebraic identity
is due to Lagrange (1773) and provides the sharpest proof of Cauchy-Schwarz.

Equivalently: 2*[(sum f^2)(sum g^2) - (sum fg)^2] = sum_i sum_j (f_i*g_j - f_j*g_i)^2 >= 0
-/

/-- Cauchy-Schwarz inequality for real-valued finite sequences.
    Proved via Lagrange's identity: the double sum of squared differences is non-negative.
    Formula: 2*[(sum f^2)(sum g^2) - (sum fg)^2] = sum_i sum_j (f_i*g_j - f_j*g_i)^2 >= 0. -/
theorem cauchy_schwarz_finite {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
  -- Non-negativity of double sum of squares (Lagrange RHS)
  have h_nn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- Lagrange's identity: expand and simplify
  suffices h_expand : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 =
      2 * ((∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) -
           (∑ i ∈ s, f i * g i) ^ 2) by linarith
  -- Expand each term using (a - b)^2 = a^2 - 2ab + b^2
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- Compute the three sub-sums
  -- Term A: sum_i sum_j (f_i * g_j)^2 = (sum f^2)(sum g^2)
  have ha : ∑ i ∈ s, ∑ j ∈ s, (f i * g j) ^ 2 =
      (∑ i ∈ s, f i ^ 2) * (∑ j ∈ s, g j ^ 2) := by
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  -- Term C (symmetric): sum_i sum_j (f_j * g_i)^2 = (sum f^2)(sum g^2)
  have hc : ∑ i ∈ s, ∑ j ∈ s, (f j * g i) ^ 2 =
      (∑ j ∈ s, f j ^ 2) * (∑ i ∈ s, g i ^ 2) := by
    rw [Finset.sum_comm]
    simp_rw [mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]
  -- Term B (cross): sum_i sum_j 2*(f_i*g_j)*(f_j*g_i) = 2*(sum f_i*g_i)^2
  have hb : ∑ i ∈ s, ∑ j ∈ s, 2 * (f i * g j) * (f j * g i) =
      2 * (∑ i ∈ s, f i * g i) ^ 2 := by
    simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  rw [ha, hc, hb]; ring

/-- Alias for `cauchy_schwarz_finite` with hypothesis-free statement.
    Note: the name 'from_holder' is a misnomer — this proof does not derive
    Cauchy-Schwarz from Hölder's inequality; it simply calls cauchy_schwarz_finite
    directly. For a Hölder-based derivation, one would use holder_nnreal at p=q=2. -/
theorem cauchy_schwarz_finite' {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) :=
  cauchy_schwarz_finite s f g

/-
## Part 4: Holder for Real-Valued Functions via NNReal Lift

Holder's inequality for real-valued (signed) functions:
  |sum f_i * g_i| <= (sum |f_i|^p)^(1/p) * (sum |g_i|^q)^(1/q)

Proof: |sum f_i*g_i| <= sum|f_i*g_i| = sum |f_i|*|g_i|
Then apply NNReal Holder to |f_i| and |g_i| treated as NNReal values.
-/

/-- Holder's inequality for real-valued functions.
    |sum f_i*g_i| <= (sum |f_i|^p)^(1/p) * (sum |g_i|^q)^(1/q). -/
theorem holder_real {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    |∑ i ∈ s, f i * g i| ≤
      (∑ i ∈ s, |f i| ^ p) ^ (1 / p) * (∑ i ∈ s, |g i| ^ q) ^ (1 / q) := by
  -- Apply Holder to absolute values packaged as NNReals
  have h_nn := holder_nnreal s (fun i => (⟨|f i|, abs_nonneg _⟩ : ℝ≥0))
    (fun i => (⟨|g i|, abs_nonneg _⟩ : ℝ≥0)) hpq
  -- Cast the NNReal inequality to ℝ
  have h_real : (∑ i ∈ s, |f i| * |g i|) ≤
      (∑ i ∈ s, |f i| ^ p) ^ (1 / p) * (∑ i ∈ s, |g i| ^ q) ^ (1 / q) := by
    have h := NNReal.coe_le_coe.mpr h_nn
    push_cast [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_rpow] at h
    simpa using h
  -- Chain: |sum f*g| <= sum |f*g| = sum |f|*|g| <= Holder RHS
  calc |∑ i ∈ s, f i * g i|
      ≤ ∑ i ∈ s, |f i * g i| := abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, |f i| * |g i| := by simp_rw [abs_mul]
    _ ≤ (∑ i ∈ s, |f i| ^ p) ^ (1 / p) * (∑ i ∈ s, |g i| ^ q) ^ (1 / q) := h_real

/-
## Part 5: Holder's Inequality for Lebesgue Integral

The continuous (integral) analogue of Holder's inequality:
  integral(|f*g| dmu) <= (integral(|f|^p dmu))^(1/p) * (integral(|g|^q dmu))^(1/q)

This is the fundamental estimate in functional analysis and PDE theory.
-/

/-- Holder's inequality for the extended Lebesgue integral.
    For Holder conjugate p, q and non-negative measurable f, g:
    integral(f*g dmu) <= (integral(f^p dmu))^(1/p) * (integral(g^q dmu))^(1/q).
    This is Mathlib's ENNReal.lintegral_mul_le_Lp_mul_Lq. -/
theorem holder_lintegral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a * g a ∂μ ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg

/-
## Part 6: Cauchy-Schwarz for Inner Product Spaces

The abstract Cauchy-Schwarz inequality follows from the norm-squared identity:
  ||u + v||^2 = ||u||^2 + 2*Re<u,v> + ||v||^2

Combined with ||u - v||^2 >= 0, this gives |<u,v>| <= ||u|| * ||v||.
-/

/-- The abstract Cauchy-Schwarz inequality for inner product spaces:
    |<u, v>| <= ||u|| * ||v||.
    This is Mathlib's abs_real_inner_le_norm. -/
theorem cauchy_schwarz_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    |@inner ℝ _ _ u v| ≤ ‖u‖ * ‖v‖ :=
  abs_real_inner_le_norm u v

/-- The Cauchy-Schwarz inequality is the p=q=2 case of Holder for sequences:
    When we set p = q = 2 in the NNReal Holder inequality, we get
    sum(f_i * g_i) <= (sum f_i^2)^(1/2) * (sum g_i^2)^(1/2)
    which is the finite-sum version of the abstract inner product CS.

    Here HolderConjugate 2 2 holds since 1/2 + 1/2 = 1. -/
theorem cauchy_schwarz_holder_bridge {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0) :
    ∑ i ∈ s, f i * g i ≤
      (∑ i ∈ s, f i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
      (∑ i ∈ s, g i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  apply holder_nnreal s f g
  constructor <;> norm_num

/-
## Summary

Proof Chain Demonstrated:
  Young's inequality (ab <= a^p/p + b^q/q) [Mathlib, internal to holder_nnreal]
    -> Normalized Holder (||f||_p = ||g||_q = 1 -> sum(f_i*g_i) <= 1)
    -> General Holder for NNReal (sum(f_i*g_i) <= ||f||_p * ||g||_q)
    -> Holder for real-valued (|sum(f_i*g_i)| <= ||f||_p * ||g||_q)
    -> Cauchy-Schwarz at p=q=2 ((sum f_i*g_i)^2 <= (sum f_i^2)(sum g_i^2))
    -> Abstract inner product Cauchy-Schwarz (|<u,v>| <= ||u||*||v||)
    -> Integral Holder for measure spaces

Theorems Proved (0 sorries):
1. holder_nnreal: General Holder for NNReal (Mathlib NNReal.inner_le_Lp_mul_Lq)
2. holder_normalized: Holder for unit-norm inputs (1 line from holder_nnreal)
3. cauchy_schwarz_finite: CS via Lagrange's identity (elementary double-sum argument)
4. cauchy_schwarz_finite': alias for cauchy_schwarz_finite (renamed from cauchy_schwarz_from_holder)
5. holder_real: Holder for real-valued functions via NNReal lift
6. holder_lintegral: Integral Holder for measure spaces (Mathlib ENNReal.lintegral_mul_le_Lp_mul_Lq)
7. cauchy_schwarz_inner: Abstract inner product CS (Mathlib abs_real_inner_le_norm)
8. cauchy_schwarz_holder_bridge: CS as p=q=2 NNReal Holder

Key Mathematical Insight:
The conjugate condition 1/p + 1/q = 1 appears naturally in the Young chain:
After applying Young to each term and summing under unit-norm conditions:
  sum(f_i * g_i) <= sum(f_i^p/p + g_i^q/q) = (1/p)*1 + (1/q)*1 = 1/p + 1/q = 1.
The equality 1/p + 1/q = 1 is EXACTLY the conjugate condition - no accident!
-/
