import Proofs.Erdos85CyclotomicResultantNorm

/-!
# A uniform Galois-packet norm for the frequency scalar

The frequency argument naturally produces

`c - (ζ + ζ⁻¹)`.

Instead of treating one embedding at a time, its full Galois packet is the
resultant of the cyclotomic polynomial with `cX - X² - 1`.  For a primitive
root of order at least three this full norm is the square of the norm from
the maximal real subfield.  This file packages that identity uniformly in
the integer parameter `c`; the earlier executable certificates instantiate
the same construction separately at fixed degrees.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- The integral quadratic whose value at a nonzero `z`, after rational
base change, is `z * (c - (z + z⁻¹))`. -/
def frequencyNormQuadraticInt (c : ℤ) : Polynomial ℤ :=
  Polynomial.C c * Polynomial.X - Polynomial.X ^ 2 - 1

/-- Rational base change of the uniform frequency-norm quadratic. -/
def frequencyNormQuadratic (c : ℤ) : Polynomial ℚ :=
  (frequencyNormQuadraticInt c).map (Int.castRingHom ℚ)

/-- The integral resultant representing the full primitive Galois packet. -/
def frequencyPacketResultant (n : ℕ) (c : ℤ) : ℤ :=
  (Polynomial.cyclotomic n ℤ).resultant
    (frequencyNormQuadraticInt c)
    (Polynomial.cyclotomic n ℤ).natDegree
    (frequencyNormQuadraticInt c).natDegree

theorem frequencyPacketResultant_rat_eq_intCast (n : ℕ) (c : ℤ) :
    (Polynomial.cyclotomic n ℚ).resultant
        (frequencyNormQuadratic c)
        (Polynomial.cyclotomic n ℚ).natDegree
        (frequencyNormQuadratic c).natDegree =
      (frequencyPacketResultant n c : ℚ) := by
  unfold frequencyNormQuadratic
  rw [← Polynomial.map_cyclotomic_int]
  rw [Polynomial.natDegree_map_eq_of_injective
      Int.cast_injective (Polynomial.cyclotomic n ℤ),
    Polynomial.natDegree_map_eq_of_injective
      Int.cast_injective (frequencyNormQuadraticInt c)]
  simp only [frequencyPacketResultant]
  exact
    Polynomial.resultant_map_map
      (Polynomial.cyclotomic n ℤ) (frequencyNormQuadraticInt c)
      (Polynomial.cyclotomic n ℤ).natDegree
      (frequencyNormQuadraticInt c).natDegree (Int.castRingHom ℚ)

theorem frequencyNormQuadratic_aeval
    {L : Type*} [Field L] [CharZero L] {z : L} (c : ℤ) (hz : z ≠ 0) :
    Polynomial.aeval z (frequencyNormQuadratic c) =
      z * ((c : L) - (z + z⁻¹)) := by
  simp [frequencyNormQuadratic, frequencyNormQuadraticInt,
    Polynomial.aeval_def]
  have hconst : Polynomial.eval₂ (algebraMap ℚ L) z
      (c : Polynomial ℚ) = (c : L) := by
    rw [← Polynomial.C_eq_intCast c, Polynomial.eval₂_C]
    exact map_intCast (algebraMap ℚ L) c
  rw [hconst]
  field_simp [hz]
  ring_nf

/-- **Uniform Galois-packet identity.**  The integral packet resultant is
the square of the real cyclotomic norm of the frequency scalar. -/
theorem primitiveTrace_minpoly_eval_int_sq_eq_frequencyPacketResultant
    {L : Type*} [Field L] [CharZero L]
    {n : ℕ} {z : L} (hz : IsPrimitiveRoot z n) (hn : 3 ≤ n)
    [IsCyclotomicExtension {n} ℚ L] (c : ℤ) :
    (minpoly ℚ (z + z⁻¹)).eval (c : ℚ) *
        (minpoly ℚ (z + z⁻¹)).eval (c : ℚ) =
      (frequencyPacketResultant n c : ℚ) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hn)
  letI : NeZero n := ⟨hn0⟩
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  have hnormZ : Algebra.norm ℚ z = 1 :=
    hz.norm_eq_one (by omega) hirr
  have hresultant :=
    norm_aeval_primitiveRoot_eq_cyclotomic_resultant
      hz hn0 (frequencyNormQuadratic c)
  rw [frequencyNormQuadratic_aeval c (hz.ne_zero hn0),
    map_mul, hnormZ, one_mul] at hresultant
  have hnormTrace := norm_rat_sub_primitiveTrace_eq_minpoly_eval_sq
    hz hn (c : ℚ)
  have hnormTrace' :
      Algebra.norm ℚ (((c : ℚ) : L) - (z + z⁻¹)) =
        (minpoly ℚ (z + z⁻¹)).eval (c : ℚ) *
          (minpoly ℚ (z + z⁻¹)).eval (c : ℚ) := by
    simpa using hnormTrace
  have hcast : (((c : ℚ) : L)) = (c : L) := by norm_cast
  rw [hcast] at hnormTrace'
  rw [← frequencyPacketResultant_rat_eq_intCast n c]
  exact hnormTrace'.symm.trans hresultant

end

end Erdos85
