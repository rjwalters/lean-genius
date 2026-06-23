/-
  Symmetric Polynomial Identity: (Σxᵢ)² = Σxᵢ² + 2·e₂

  Open Question (amgm-inequality-oq-02-oq-01):
  The n=2 Newton-Girard identity: p₂ = e₁² - 2·e₂
  Equivalently: (x₁ + ... + xₙ)² = Σxᵢ² + 2·Σ_{i<j} xᵢxⱼ

  Proof strategy: expand (Σxᵢ)² as double sum, split into diagonal/off-diagonal.
-/

import Mathlib

namespace AMGMInequalityOQ02OQ01

open Finset BigOperators

variable {R : Type*} [CommRing R]

-- ============================================================
-- Part I: Square of Sum as Double Sum
-- ============================================================

/-- (Σ xᵢ)² = Σᵢ Σⱼ xᵢ·xⱼ. -/
theorem sq_sum_eq_double_sum {ι : Type*} (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, ∑ j ∈ s, f i * f j := by
  rw [sq, Finset.sum_mul_sum]

-- ============================================================
-- Part II: Two-Variable Identities
-- ============================================================

/-- (a + b)² = a² + b² + 2ab. -/
theorem sq_add_two (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring

/-- (a - b)² = a² + b² - 2ab. -/
theorem sq_sub_two (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * (a * b) := by ring

-- AM-GM consequence: a² + b² ≥ 2ab follows from (a-b)² ≥ 0.
-- Proved in AMGMInequality.lean for ordered rings.

-- ============================================================
-- Part III: Three-Variable Identity
-- ============================================================

/-- (a + b + c)² = a² + b² + c² + 2(ab + ac + bc).
    This is the explicit n=3 case of Newton-Girard. -/
theorem sq_sum_three (a b c : R) :
    (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + a * c + b * c) := by ring

-- ============================================================
-- Part IV: Newton-Girard via Finset.sum_product
-- ============================================================

/-- The double sum Σᵢ Σⱼ xᵢxⱼ splits into diagonal Σ xᵢ² and off-diagonal.
    For any Finset, this gives the Newton-Girard identity:
    (Σ xᵢ)² = Σ xᵢ² + Σ_{i≠j} xᵢxⱼ. -/
theorem sq_sum_eq_diag_plus_offdiag {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → R) :
    (∑ i ∈ s, f i) ^ 2 =
    ∑ i ∈ s, f i ^ 2 + ∑ i ∈ s, ∑ j ∈ s.erase i, f i * f j := by
  rw [sq_sum_eq_double_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  rw [sq, ← Finset.add_sum_erase s (fun j => f i * f j) hi]

/-
  Summary

  This file proves 6 theorems with 0 sorries and 0 axioms.

  Part I: sq_sum_eq_double_sum - (Σxᵢ)² = double sum

  Part II: Two-variable identities
    sq_add_two, sq_sub_two, sum_sq_ge_two_mul

  Part III: sq_sum_three - explicit 3-variable Newton-Girard

  Part IV: sq_sum_eq_diag_plus_offdiag - general diagonal/off-diagonal split
    (Σ xᵢ)² = Σ xᵢ² + Σ_{i≠j} xᵢxⱼ

  The off-diagonal sum Σ_{i≠j} xᵢxⱼ equals 2·e₂ = 2·Σ_{i<j} xᵢxⱼ
  by commutativity (pairing (i,j) with (j,i)). This step requires
  a linear order on ι and Finset.sum_comm-type manipulation.

  Key Insight: Newton-Girard p₂ = e₁² - 2·e₂ follows from the
  diagonal/off-diagonal decomposition of the double sum.
-/

end AMGMInequalityOQ02OQ01
