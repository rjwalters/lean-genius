import Mathlib

open Polynomial IntermediateField

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of √2 over ℚ

## Main Result

The minimal polynomial of the real number √2 over the rational field ℚ is X² - 2.

Equivalently:
- X² - 2 is the unique monic irreducible polynomial in ℚ[X] having √2 as a root
- The algebraic degree [ℚ(√2) : ℚ] = 2
- √2 is not rational (its minimal polynomial has degree 2 > 1)

## Proof Strategy

1. **Eisenstein irreducibility**: X² - 2 is irreducible over ℤ (Eisenstein at p = 2:
   2 | 2 but 4 ∤ 2, and 2 ∤ 1). Transfer to ℚ via Gauss's lemma.

2. **Root witness**: (√2)² = 2, so aeval (√2) (X² - 2) = 0.

3. **Minimal polynomial characterization**: A monic irreducible polynomial with α as
   a root is the minimal polynomial. Apply `minpoly.eq_of_irreducible_of_monic`.

## Connection to Gallery

This proof is a specialization of the general nth-root minimal polynomial theorem
in `Sqrt2IrrationalOQ03` and `CubeRoot2IrrationalOQ03`. Setting n = 2, m = 2, p = 2
recovers this specific result.

## Status: 0 sorries, 0 axioms
-/

namespace Sqrt2Minpoly

/-! ## Part I: Irreducibility of X² - 2 over ℚ via Eisenstein -/

/-- X² - 2 is irreducible over ℤ by the Eisenstein criterion at p = 2.
    Since 2 | 2 (constant term) but 4 ∤ 2, and 2 ∤ 1 (leading coeff), Eisenstein applies. -/
private theorem irred_X_sq_sub_two_int : Irreducible (X ^ 2 - C (2 : ℤ) : ℤ[X]) := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(2 : ℤ)})
  · -- (2) is a prime ideal in ℤ
    rw [Ideal.span_singleton_prime (show (2 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_two
  · -- Leading coefficient 1 ∉ (2)
    rw [leadingCoeff_X_pow_sub_C (show (0 : ℕ) < 2 from by norm_num),
        Ideal.mem_span_singleton]
    norm_num
  · -- All lower coefficients ∈ (2)
    intro k hk
    rw [degree_X_pow_sub_C (show (0 : ℕ) < 2 from by norm_num) (2 : ℤ)] at hk
    have hk2 : k < 2 := WithBot.coe_lt_coe.mp hk
    interval_cases k <;>
      simp [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow]
  · -- Degree is positive
    rw [degree_X_pow_sub_C (show (0 : ℕ) < 2 from by norm_num) (2 : ℤ)]
    norm_cast
  · -- Constant term not in (2)² = (4)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [coeff_sub, coeff_X_pow, coeff_C, show ¬(0 = 2) from by norm_num,
               ite_false, zero_sub, dvd_neg]
    norm_num
  · -- X² - 2 is primitive over ℤ
    exact (monic_X_pow_sub_C (2 : ℤ) (show 2 ≠ 0 from by norm_num)).isPrimitive

/-- X² - 2 is irreducible over ℚ.
    Transfer the ℤ irreducibility to ℚ using Gauss's lemma. -/
theorem irred_X_sq_sub_two : Irreducible (X ^ 2 - C (2 : ℚ) : ℚ[X]) := by
  have hprim : (X ^ 2 - C (2 : ℤ) : ℤ[X]).IsPrimitive :=
    (monic_X_pow_sub_C (2 : ℤ) (show 2 ≠ 0 from by norm_num)).isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    irred_X_sq_sub_two_int
  rwa [show Polynomial.map (Int.castRingHom ℚ) (X ^ 2 - C (2 : ℤ)) = X ^ 2 - C (2 : ℚ) from
    by simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, map_ofNat]] at hirr

/-! ## Part II: Root Witness and Integrality -/

/-- √2 satisfies the polynomial equation t² - 2 = 0.
    This follows from the fundamental identity (√2)² = 2. -/
theorem aeval_sqrt_two_eq_zero :
    Polynomial.aeval (Real.sqrt 2) (X ^ 2 - C (2 : ℚ) : ℚ[X]) = 0 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [map_sub, map_pow, aeval_X, map_ofNat]
  linarith

/-- √2 is algebraic over ℚ: X² - 2 ∈ ℚ[X] is a monic polynomial with √2 as a root. -/
theorem sqrt_two_isIntegral : IsIntegral ℚ (Real.sqrt 2) :=
  ⟨X ^ 2 - C 2, monic_X_pow_sub_C 2 (show 2 ≠ 0 from by norm_num), aeval_sqrt_two_eq_zero⟩

/-! ## Part III: The Minimal Polynomial -/

/-- **Main Theorem**: The minimal polynomial of √2 over ℚ is X² - 2.

    Three ingredients establish this:
    1. X² - 2 is irreducible over ℚ (Eisenstein criterion at p = 2)
    2. √2 is a root: (√2)² - 2 = 0
    3. X² - 2 is monic

    By `minpoly.eq_of_irreducible_of_monic`, a monic irreducible polynomial with α as
    a root must equal minpoly K α. -/
theorem minpoly_sqrt_two : minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2 :=
  (minpoly.eq_of_irreducible_of_monic
    irred_X_sq_sub_two
    aeval_sqrt_two_eq_zero
    (monic_X_pow_sub_C 2 (show 2 ≠ 0 from by norm_num))).symm

/-! ## Part IV: Consequences -/

/-- The minimal polynomial of √2 has degree 2.
    Equivalently, √2 has algebraic degree 2 over ℚ. -/
theorem sqrt_two_minpoly_natDegree : (minpoly ℚ (Real.sqrt 2)).natDegree = 2 := by
  rw [minpoly_sqrt_two]
  have h : (C (2 : ℚ) : ℚ[X]).natDegree < (X ^ 2 : ℚ[X]).natDegree := by
    simp [natDegree_pow, natDegree_X]
  rw [natDegree_sub_eq_left_of_natDegree_lt h, natDegree_pow, natDegree_X, mul_one]

/-- **Field Extension Degree**: [ℚ(√2) : ℚ] = 2.

    The quadratic extension ℚ(√2)/ℚ has degree equal to the degree of the minimal
    polynomial of √2, which is 2. This shows ℚ(√2) is a proper quadratic extension. -/
theorem adjoin_sqrt_two_finrank : Module.finrank ℚ ℚ⟮Real.sqrt 2⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank sqrt_two_isIntegral]
  exact sqrt_two_minpoly_natDegree

/-- **Irrationality**: √2 is irrational.
    The minimal polynomial argument provides perspective: minpoly has degree 2,
    so √2 cannot be rational (rationals have minimal polynomials of degree 1 or 0). -/
theorem sqrt_two_irrational : Irrational (Real.sqrt 2) := irrational_sqrt_two

/-- **Not in ℚ**: √2 has no rational representation.
    The degree-2 minimal polynomial certifies that √2 ∉ ℚ. -/
theorem sqrt_two_not_rational : ∀ q : ℚ, (q : ℝ) ≠ Real.sqrt 2 := by
  intro q hq
  exact irrational_sqrt_two ⟨q, hq⟩

end Sqrt2Minpoly
