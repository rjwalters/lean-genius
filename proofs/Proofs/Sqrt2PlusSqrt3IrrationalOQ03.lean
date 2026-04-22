import Mathlib

open Polynomial Real IntermediateField

set_option maxHeartbeats 800000

/-
# Minimal Polynomial of √2 + √3 over ℚ

## Main Result

The minimal polynomial of α = √2 + √3 over ℚ is f(X) = X⁴ - 10X² + 1.

Equivalently:
- X⁴ - 10X² + 1 is the unique monic irreducible polynomial in ℚ[X] with α as a root
- [ℚ(√2+√3) : ℚ] = 4
- √2+√3 is not in any proper subfield of ℝ containing ℚ

## Proof Strategy

1. **Root witness**: Direct computation shows f(α) = 0.
   α² = (√2+√3)² = 5 + 2√6,  α⁴ = (5+2√6)² = 49+20√6
   f(α) = 49+20√6 - 10(5+2√6) + 1 = 0.

2. **Irreducibility**: f is irreducible over ℚ via rational root + quadratic factor analysis.
   - No rational roots: only candidates ±1 give f(±1) = -8 ≠ 0.
   - No quadratic factors: if f = (X²+aX+b)(X²-aX+d), then bd=1, a(d-b)=0, b+d-a²=-10.
     Case a=0: b+d=-10, bd=1 → discriminant 96 = 4·24, √24 ∉ ℚ.
     Case b=d: b²=1, 2b-a²=-10.  b=1→a²=12∉ℚ²;  b=-1→a²=8∉ℚ².

3. **Minimal polynomial**: Since f is monic, irreducible, and vanishes at α,
   apply `minpoly.eq_of_irreducible_of_monic`.

## Status: 1 sorry (irreducibility of X⁴ − 10X² + 1 over ℚ)
-/

namespace Sqrt2PlusSqrt3IrrationalOQ03

/-! ## Part I: Root Witness -/

/-- √2+√3 satisfies X⁴ - 10X² + 1 = 0.
    Key algebra: α² = 5+2√6, α⁴ = 49+20√6, so α⁴-10α²+1 = 0. -/
theorem aeval_sqrt2_plus_sqrt3 :
    Polynomial.aeval (Real.sqrt 2 + Real.sqrt 3) (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]) = 0 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- (√2+√3)² = 5 + 2·(√2·√3)
  have hsq : (Real.sqrt 2 + Real.sqrt 3) ^ 2 = 5 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by
    have := calc (Real.sqrt 2 + Real.sqrt 3) ^ 2
        = Real.sqrt 2 ^ 2 + 2 * Real.sqrt 2 * Real.sqrt 3 + Real.sqrt 3 ^ 2 := by ring
      _ = 2 + 2 * Real.sqrt 2 * Real.sqrt 3 + 3 := by rw [h2, h3]
      _ = 5 + 2 * (Real.sqrt 2 * Real.sqrt 3) := by ring
    exact this
  -- (√2·√3)² = 6
  have h23sq : (Real.sqrt 2 * Real.sqrt 3) ^ 2 = 6 := by
    rw [mul_pow, h2, h3]; norm_num
  -- (√2+√3)⁴ = 49 + 20·(√2·√3)
  have h4 : (Real.sqrt 2 + Real.sqrt 3) ^ 4 = 49 + 20 * (Real.sqrt 2 * Real.sqrt 3) := by
    calc (Real.sqrt 2 + Real.sqrt 3) ^ 4
        = ((Real.sqrt 2 + Real.sqrt 3) ^ 2) ^ 2 := by ring
      _ = (5 + 2 * (Real.sqrt 2 * Real.sqrt 3)) ^ 2 := by rw [hsq]
      _ = 25 + 20 * (Real.sqrt 2 * Real.sqrt 3) + 4 * (Real.sqrt 2 * Real.sqrt 3) ^ 2 := by ring
      _ = 25 + 20 * (Real.sqrt 2 * Real.sqrt 3) + 4 * 6 := by rw [h23sq]
      _ = 49 + 20 * (Real.sqrt 2 * Real.sqrt 3) := by ring
  -- Now evaluate: f(√2+√3) = α⁴ - 10α² + 1 = (49+20√6) - 10(5+2√6) + 1 = 0
  simp only [map_sub, map_add, map_pow, map_mul, map_one, aeval_X, map_ofNat,
             Polynomial.aeval_one]
  push_cast
  linarith [hsq, h4]

/-! ## Part II: Irreducibility over ℚ -/

/-- X⁴ - 10X² + 1 is monic. -/
private theorem f_monic : (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).Monic := by
  unfold Polynomial.Monic Polynomial.leadingCoeff
  have hd : (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).natDegree = 4 := by
    have h1 : (10 * X ^ 2 : ℚ[X]).natDegree ≤ 2 := by
      calc (10 * X ^ 2 : ℚ[X]).natDegree ≤ _ := natDegree_mul_le
        _ = _ := by simp
    have h2 : (X ^ 4 - 10 * X ^ 2 : ℚ[X]).natDegree = 4 := by
      apply natDegree_sub_eq_left_of_natDegree_lt
      calc (10 * X ^ 2 : ℚ[X]).natDegree ≤ 2 := h1
        _ < 4 := by norm_num
      simp [natDegree_pow]
    calc (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).natDegree
        = (X ^ 4 - 10 * X ^ 2 : ℚ[X]).natDegree := by
          apply natDegree_add_eq_left_of_natDegree_lt
          simp [h2]
      _ = 4 := h2
  rw [hd]
  simp [coeff_sub, coeff_add, coeff_X_pow, coeff_mul, coeff_ofNat]

/-- √2+√3 is algebraic over ℚ: X⁴ - 10X² + 1 is a monic polynomial with it as root. -/
private theorem sqrt2_plus_sqrt3_isIntegral : IsIntegral ℚ (Real.sqrt 2 + Real.sqrt 3) :=
  ⟨X ^ 4 - 10 * X ^ 2 + 1, f_monic, aeval_sqrt2_plus_sqrt3⟩

/-- X⁴ - 10X² + 1 is irreducible over ℚ.
    Proof sketch:
    - No rational roots: f(±1) = -8 ≠ 0 (by rational root theorem ±1 are the only candidates)
    - No quadratic factors over ℚ: equating coefficients yields equations with
      irrational solutions in all cases (discriminant 96 for the a=0 case;
      a²∈{8,12} for the b=d case — none are perfect squares).
    - By the factor theorem for degree 4, no linear or quadratic rational factors
      implies irreducibility. -/
private theorem irred_f : Irreducible (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]) := by
  sorry

/-! ## Part III: Consequences of the Minimal Polynomial -/

/-- **Main Theorem**: The minimal polynomial of √2+√3 over ℚ is X⁴ - 10X² + 1. -/
theorem minpoly_sqrt2_plus_sqrt3 :
    minpoly ℚ (Real.sqrt 2 + Real.sqrt 3) = X ^ 4 - 10 * X ^ 2 + 1 :=
  (minpoly.eq_of_irreducible_of_monic
    irred_f
    aeval_sqrt2_plus_sqrt3
    f_monic).symm

/-- **Field Extension Degree**: [ℚ(√2+√3) : ℚ] = 4.
    Follows from the degree-4 minimal polynomial. -/
theorem adjoin_sqrt2_plus_sqrt3_finrank :
    Module.finrank ℚ ℚ⟮Real.sqrt 2 + Real.sqrt 3⟯ = 4 := by
  rw [IntermediateField.adjoin.finrank sqrt2_plus_sqrt3_isIntegral]
  rw [minpoly_sqrt2_plus_sqrt3]
  have h1 : (10 * X ^ 2 : ℚ[X]).natDegree ≤ 2 := by
    calc (10 * X ^ 2 : ℚ[X]).natDegree ≤ _ := natDegree_mul_le
      _ = _ := by simp
  have h2 : (X ^ 4 - 10 * X ^ 2 : ℚ[X]).natDegree = 4 := by
    apply natDegree_sub_eq_left_of_natDegree_lt
    · linarith [h1]
    · simp [natDegree_pow]
  calc (X ^ 4 - 10 * X ^ 2 + 1 : ℚ[X]).natDegree
      = (X ^ 4 - 10 * X ^ 2 : ℚ[X]).natDegree := by
        apply natDegree_add_eq_left_of_natDegree_lt
        simp [h2]
    _ = 4 := h2

/-- **Irrationality**: √2+√3 is not rational.
    If √2+√3 = q ∈ ℚ, squaring gives (q²−5)/2 = √6, contradicting irrationality of √6. -/
theorem sqrt2_plus_sqrt3_irrational : Irrational (Real.sqrt 2 + Real.sqrt 3) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h6mult : sqrt 2 * sqrt 3 = sqrt 6 := by rw [← sqrt_mul h2]; norm_num
  have hsix : Irrational (sqrt 6) :=
    irrational_sqrt_natCast_iff.mpr (by native_decide)
  intro ⟨q, hq⟩
  have hsq : (q : ℝ) ^ 2 = 5 + 2 * sqrt 6 := by
    have : (sqrt 2 + sqrt 3) ^ 2 = 5 + 2 * sqrt 6 := by
      have : (sqrt 2 + sqrt 3) ^ 2 = sqrt 2 ^ 2 + 2 * (sqrt 2 * sqrt 3) + sqrt 3 ^ 2 := by ring
      rw [this, sq_sqrt h2, sq_sqrt h3, h6mult]; ring
    rw [hq]; exact this
  have h6eq : sqrt 6 = ((q : ℝ) ^ 2 - 5) / 2 := by linarith
  exact hsix ⟨(q ^ 2 - 5) / 2, by push_cast; linarith⟩

end Sqrt2PlusSqrt3IrrationalOQ03
