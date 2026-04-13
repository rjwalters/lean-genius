/-
# Eisenstein Irreducibility Criterion for Cube Root 3

**Open Question (OQ-02)**: Can the Eisenstein criterion be used to give a focused
proof that X³ - 3 is irreducible over ℤ, and hence that ∛3 is irrational?

**Answer**: Yes. This file gives a self-contained proof:

1. **X³ - 3 irreducible over ℤ** (Eisenstein at p = 3):
   - P = (3) is a prime ideal
   - Leading coefficient 1 ∉ (3)
   - Non-leading coefficients -3, 0, 0 all lie in (3)
   - Constant term -3 ∉ (9) = (3)² (since 9 ∤ 3)
   - X³ - 3 is monic hence primitive

2. **X³ - 3 irreducible over ℚ** (Gauss's lemma)

3. **∛3 is irrational** (roots of irreducible degree-3 poly over ℚ)

**Note**: This is a focused standalone proof. The general theorem
`NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime` subsumes this as a
special case, but the explicit Eisenstein proof for X³ - 3 is instructive.

Tags: irrationality, algebra, number-theory, eisenstein, galois-theory
-/

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Real.Irrational
import Mathlib.Tactic

open Polynomial

namespace CubeRoot3IrrationalOQ02

-- ============================================================
-- PART I: Eisenstein at p = 3 — Irreducibility over ℤ
-- ============================================================

/-- X³ - 3 is irreducible over ℤ.

    **Proof (Eisenstein at p = 3)**:
    - P = (3) is a prime ideal in ℤ
    - leadingCoeff = 1 ∉ (3)
    - coeff 2 = 0 ∈ (3), coeff 1 = 0 ∈ (3), coeff 0 = -3 ∈ (3)
    - coeff 0 = -3 ∉ (9): 9 ∤ 3 since |3| < 9
    - X³ - 3 is monic hence primitive -/
theorem X_cubed_sub_3_irreducible_int :
    Irreducible (X ^ 3 - C (3 : ℤ) : ℤ[X]) := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(3 : ℤ)})
  · -- (3) is a prime ideal in ℤ
    rw [Ideal.span_singleton_prime (by norm_num : (3 : ℤ) ≠ 0)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · -- leadingCoeff 1 ∉ (3)
    rw [leadingCoeff_X_pow_sub_C (by norm_num : (0 : ℕ) < 3)]
    rw [Ideal.mem_span_singleton]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num) |>.not_dvd_one
  · -- All non-leading coefficients lie in (3)
    intro k hk
    rw [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 3) (3 : ℤ)] at hk
    have hkn : k < 3 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow, coeff_C]
    have hk3 : ¬(k = 3) := by omega
    simp only [if_neg hk3, zero_sub, dvd_neg]
    by_cases hk0 : k = 0 <;> simp [hk0]
  · -- degree > 0
    rw [degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 3) (3 : ℤ)]
    norm_num
  · -- coeff 0 = -3 ∉ (3)² = (9): 9 ∤ 3
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [coeff_sub, coeff_X_pow, show ¬(0 = 3) from by norm_num,
               ite_false, zero_sub, dvd_neg]
    -- Goal: ¬ (3 : ℤ)^2 ∣ (3 : ℤ)
    intro h
    have hle := Int.le_of_dvd (by norm_num : (0 : ℤ) < 3) h
    norm_num at hle
  · -- X³ - 3 is monic hence primitive
    exact (monic_X_pow_sub_C (3 : ℤ) (by norm_num : 3 ≠ 0)).isPrimitive

-- ============================================================
-- PART II: Transfer to ℚ via Gauss's Lemma
-- ============================================================

/-- X³ - 3 is irreducible over ℚ.
    Proved by Gauss's lemma: primitive irreducible over ℤ → irreducible over ℚ. -/
theorem X_cubed_sub_3_irreducible_rat :
    Irreducible (X ^ 3 - C (3 : ℚ) : ℚ[X]) := by
  have hprim : (X ^ 3 - C (3 : ℤ) : ℤ[X]).IsPrimitive :=
    (monic_X_pow_sub_C (3 : ℤ) (by norm_num : 3 ≠ 0)).isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    X_cubed_sub_3_irreducible_int
  convert hirr using 1
  ext k
  simp [coeff_sub, coeff_X_pow]

-- ============================================================
-- PART III: Irrationality of ∛3
-- ============================================================

/-- An irreducible polynomial over ℚ with degree ≥ 2 has no rational root. -/
private lemma irreducible_no_rational_root {p : ℚ[X]} (hirr : Irreducible p)
    (hdeg : 2 ≤ p.natDegree) (r : ℚ) : ¬ p.IsRoot r := by
  intro hroot
  obtain ⟨q, hpq⟩ := dvd_iff_isRoot.mpr hroot
  rcases hirr.isUnit_or_isUnit hpq with hu | hu
  · exact (irreducible_X_sub_C r).1 hu
  · have hne1 := X_sub_C_ne_zero r
    have hne2 : q ≠ 0 := right_ne_zero_of_mul (hpq ▸ hirr.ne_zero)
    have hd : p.natDegree = 1 + q.natDegree := by
      rw [hpq, natDegree_mul hne1 hne2, natDegree_X_sub_C]
    have hq0 : q.natDegree = 0 := by
      rcases Polynomial.isUnit_iff.mp hu with ⟨c, _, rfl⟩; exact natDegree_C c
    omega

/-- ∛3 (as 3^(1/3)) is irrational.

    **Proof**:
    1. X³ - 3 is irreducible over ℚ (by Eisenstein at p=3 + Gauss's lemma)
    2. X³ - 3 has degree 3 ≥ 2
    3. 3^(1/3) is a root of X³ - 3: (3^(1/3))³ = 3
    4. By irreducibility, no rational is a root of X³ - 3
    5. Hence 3^(1/3) ∉ ℚ, i.e., 3^(1/3) is irrational -/
theorem irrational_cbrt3 : Irrational ((3 : ℝ) ^ ((1 : ℝ) / 3)) := by
  -- (3^(1/3))^3 = 3 in ℝ (used to show it's a root of X³ - 3)
  have hcubed : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 3)) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  -- 3^(1/3) is a root of X³ - 3 over ℝ
  have hroot_real : Polynomial.aeval ((3 : ℝ) ^ ((1 : ℝ) / 3))
      (X ^ 3 - C (3 : ℚ) : ℚ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_ofNat]
    linarith [hcubed]
  -- X³ - 3 has degree 3 ≥ 2
  have hdeg : 2 ≤ (X ^ 3 - C (3 : ℚ) : ℚ[X]).natDegree := by
    have h : (C (3 : ℚ)).natDegree < (X ^ 3 : ℚ[X]).natDegree := by simp
    rw [natDegree_sub_eq_left_of_natDegree_lt h, natDegree_pow, natDegree_X, mul_one]
  -- Assume 3^(1/3) = r : ℚ and derive contradiction
  intro ⟨r, hr⟩
  -- r is a root of X³ - 3 over ℚ
  have heval : Polynomial.aeval r (X ^ 3 - C (3 : ℚ) : ℚ[X]) = 0 := by
    apply_fun (algebraMap ℚ ℝ) using (algebraMap ℚ ℝ).injective
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply,
        show (algebraMap ℚ ℝ) r = (3 : ℝ) ^ ((1 : ℝ) / 3) from hr]
    exact hroot_real
  -- Contradicts: X³ - 3 irreducible of degree ≥ 2 has no rational root
  exact irreducible_no_rational_root X_cubed_sub_3_irreducible_rat hdeg r heval

-- ============================================================
-- PART IV: Summary
-- ============================================================

#check X_cubed_sub_3_irreducible_int
#check X_cubed_sub_3_irreducible_rat
#check irrational_cbrt3

end CubeRoot3IrrationalOQ02
