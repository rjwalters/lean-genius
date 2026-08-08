import Proofs.Erdos85CyclotomicResultantNorm

/-!
# Parametric cyclotomic resultant norm bridge

The original resultant development specialized its integral quadratic to
the scalar `13`.  The saturated degree-124 terminal needs the identical
construction at `123`.  This file exposes the shared construction at an
arbitrary integral scalar.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- Integral quadratic whose value at `z` is
`z * (a - (z + z⁻¹))`. -/
def cyclotomicQuadraticIntAt (a : ℤ) : Polynomial ℤ :=
  Polynomial.C a * Polynomial.X - Polynomial.X ^ 2 - 1

/-- Rational form of `cyclotomicQuadraticIntAt`. -/
def cyclotomicQuadraticAt (a : ℤ) : Polynomial ℚ :=
  Polynomial.C (a : ℚ) * Polynomial.X - Polynomial.X ^ 2 - 1

/-- Integral cyclotomic resultant at scalar `a`. -/
def cyclotomicResultantAt (a : ℤ) (n : ℕ) : ℤ :=
  (Polynomial.cyclotomic n ℤ).resultant
    (cyclotomicQuadraticIntAt a)
    (Polynomial.cyclotomic n ℤ).natDegree
    (cyclotomicQuadraticIntAt a).natDegree

theorem cyclotomicQuadraticIntAt_natDegree (a : ℤ) :
    (cyclotomicQuadraticIntAt a).natDegree = 2 := by
  unfold cyclotomicQuadraticIntAt
  compute_degree!

theorem cyclotomicQuadraticIntAt_map (a : ℤ) :
    (cyclotomicQuadraticIntAt a).map (Int.castRingHom ℚ) =
      cyclotomicQuadraticAt a := by
  simp [cyclotomicQuadraticIntAt, cyclotomicQuadraticAt]

/-- The rational resultant is the cast of the integral resultant. -/
theorem cyclotomicResultantAt_rat_eq_intCast (a : ℤ) (n : ℕ) :
    (Polynomial.cyclotomic n ℚ).resultant
        (cyclotomicQuadraticAt a)
        (Polynomial.cyclotomic n ℚ).natDegree
        (cyclotomicQuadraticAt a).natDegree =
      (cyclotomicResultantAt a n : ℚ) := by
  rw [← Polynomial.map_cyclotomic_int,
    ← cyclotomicQuadraticIntAt_map]
  rw [Polynomial.natDegree_map_eq_of_injective
      Int.cast_injective (Polynomial.cyclotomic n ℤ),
    Polynomial.natDegree_map_eq_of_injective
      Int.cast_injective (cyclotomicQuadraticIntAt a)]
  simpa [cyclotomicResultantAt] using
    Polynomial.resultant_map_map
      (Polynomial.cyclotomic n ℤ) (cyclotomicQuadraticIntAt a)
      (Polynomial.cyclotomic n ℤ).natDegree
      (cyclotomicQuadraticIntAt a).natDegree (Int.castRingHom ℚ)

/-- Cyclotomic factorization turns the product of the conductor resultants
into one resultant against `X^n - 1`. -/
theorem prod_cyclotomicResultantAt_eq_X_pow_sub_one_resultant
    (a : ℤ) {n : ℕ} (hn : 0 < n) :
    ∏ k ∈ n.divisors, cyclotomicResultantAt a k =
      (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant
        (cyclotomicQuadraticIntAt a)
        (Polynomial.X ^ n - 1 : Polynomial ℤ).natDegree
        (cyclotomicQuadraticIntAt a).natDegree := by
  rw [← Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ]
  rw [Polynomial.resultant_prod_left]
  · simp [cyclotomicResultantAt]
  · simp only [(Polynomial.cyclotomic.monic _ ℤ).leadingCoeff,
      Finset.prod_const_one]
    norm_num
  · exact le_rfl

theorem cyclotomicQuadraticAt_aeval
    (a : ℤ) {L : Type*} [Field L] [CharZero L] {z : L} (hz : z ≠ 0) :
    Polynomial.aeval z (cyclotomicQuadraticAt a) =
      z * ((a : L) - (z + z⁻¹)) := by
  simp only [cyclotomicQuadraticAt, map_sub, map_mul, map_pow, map_one,
    aeval_C, aeval_X]
  simp only [map_intCast]
  field_simp [hz]
  ring

/-- **Parametric direct resultant bridge.**  For a primitive root of order
at least three, the square of the real-trace minimal-polynomial value at an
integral scalar `a` is the corresponding integral cyclotomic resultant. -/
theorem primitiveTrace_minpoly_eval_intCast_sq_eq_cyclotomicResultantAt
    (a : ℤ) {L : Type*} [Field L] [CharZero L]
    {n : ℕ} {z : L} (hz : IsPrimitiveRoot z n) (hn : 3 ≤ n)
    [IsCyclotomicExtension {n} ℚ L] :
    (minpoly ℚ (z + z⁻¹)).eval (a : ℚ) *
        (minpoly ℚ (z + z⁻¹)).eval (a : ℚ) =
      (cyclotomicResultantAt a n : ℚ) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hn)
  letI : NeZero n := ⟨hn0⟩
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  have hnormZ : Algebra.norm ℚ z = 1 :=
    hz.norm_eq_one (by omega) hirr
  have hresultant :=
    norm_aeval_primitiveRoot_eq_cyclotomic_resultant
      hz hn0 (cyclotomicQuadraticAt a)
  rw [cyclotomicQuadraticAt_aeval a (hz.ne_zero hn0),
    map_mul, hnormZ, one_mul] at hresultant
  have hnormTrace := norm_rat_sub_primitiveTrace_eq_minpoly_eval_sq
    hz hn (a : ℚ)
  have hnormTrace' :
      Algebra.norm ℚ ((a : L) - (z + z⁻¹)) =
        (minpoly ℚ (z + z⁻¹)).eval (a : ℚ) *
          (minpoly ℚ (z + z⁻¹)).eval (a : ℚ) := by
    simpa using hnormTrace
  rw [cyclotomicResultantAt_rat_eq_intCast] at hresultant
  exact hnormTrace'.symm.trans hresultant

/-- Scalar-123 specialization used by the saturated hard-sector terminal. -/
theorem primitiveTrace_minpoly_eval_oneTwentyThree_sq_eq_resultant
    {L : Type*} [Field L] [CharZero L]
    {n : ℕ} {z : L} (hz : IsPrimitiveRoot z n) (hn : 3 ≤ n)
    [IsCyclotomicExtension {n} ℚ L] :
    (minpoly ℚ (z + z⁻¹)).eval 123 *
        (minpoly ℚ (z + z⁻¹)).eval 123 =
      (cyclotomicResultantAt 123 n : ℚ) := by
  simpa using
    primitiveTrace_minpoly_eval_intCast_sq_eq_cyclotomicResultantAt
      123 hz hn

end

end Erdos85
