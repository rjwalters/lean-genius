import Proofs.Erdos85RealCyclotomicFullNorm
import Proofs.Erdos85DegreeFourteenNormCertificate
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Cyclotomic norms as executable resultants

This file gives a direct alternative to multiplicative Möbius inversion.
The norm of a polynomial evaluated at a primitive root is the resultant of
that polynomial with the corresponding cyclotomic polynomial.  The latter
is a fully executable integer expression in the bounded degree-fourteen
range.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- The norm of `q(ζ)` in a cyclotomic extension is the resultant of the
cyclotomic polynomial with `q`. -/
theorem norm_aeval_primitiveRoot_eq_cyclotomic_resultant
    {L : Type*} [Field L] [CharZero L]
    {n : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0)
    [IsCyclotomicExtension {n} ℚ L] (q : Polynomial ℚ) :
    Algebra.norm ℚ (Polynomial.aeval ζ q) =
      (Polynomial.cyclotomic n ℚ).resultant q
        (Polynomial.cyclotomic n ℚ).natDegree q.natDegree := by
  letI : NeZero n := ⟨hn⟩
  let E := AlgebraicClosure L
  letI := IsCyclotomicExtension.finiteDimensional {n} ℚ L
  letI := IsCyclotomicExtension.isGalois {n} ℚ L
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  apply (algebraMap ℚ E).injective
  rw [Algebra.norm_eq_prod_embeddings]
  rw [← Polynomial.resultant_map_map]
  rw [map_cyclotomic]
  have hζE : IsPrimitiveRoot (algebraMap L E ζ) n :=
    hζ.map_of_injective (algebraMap L E).injective
  have hdegCyclotomic : (Polynomial.cyclotomic n E).natDegree =
      (Polynomial.cyclotomic n ℚ).natDegree := by
    rw [Polynomial.natDegree_cyclotomic, Polynomial.natDegree_cyclotomic]
  have hdegQ : (q.map (algebraMap ℚ E)).natDegree = q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ E).injective q
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζE]
  rw [← hdegCyclotomic, ← hdegQ]
  rw [show (Polynomial.cyclotomic n E).natDegree =
      (∏ μ ∈ primitiveRoots n E, (Polynomial.X - Polynomial.C μ)).natDegree by
    rw [← Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζE]]
  rw [Polynomial.resultant_prod_left]
  · have hlinear (z : E) :
        (Polynomial.X - Polynomial.C z).resultant
            (q.map (algebraMap ℚ E))
            (Polynomial.X - Polynomial.C z).natDegree
            (q.map (algebraMap ℚ E)).natDegree =
          (q.map (algebraMap ℚ E)).eval z := by
      simpa using Polynomial.resultant_X_sub_C_left
        (q.map (algebraMap ℚ E)) (q.map (algebraMap ℚ E)).natDegree z le_rfl
    simp_rw [hlinear]
    rw [← @Finset.prod_attach E E, ← Finset.univ_eq_attach]
    refine Fintype.prod_equiv (hζ.embeddingsEquivPrimitiveRoots E hirr)
      (fun σ : L →ₐ[ℚ] E ↦ σ (Polynomial.aeval ζ q))
      (fun z : primitiveRoots n E ↦ (q.map (algebraMap ℚ E)).eval z.1) ?_
    intro σ
    simp [Polynomial.aeval_def]
  · simp
  · exact le_rfl

/-- Integral quadratic used in the resultant construction. -/
def degreeFourteenCyclotomicQuadraticInt : Polynomial ℤ :=
  Polynomial.C 13 * Polynomial.X - Polynomial.X ^ 2 - 1

/-- The quadratic whose value at `z` is
`z * (13 - (z + z⁻¹))`. -/
def degreeFourteenCyclotomicQuadratic : Polynomial ℚ :=
  degreeFourteenCyclotomicQuadraticInt.map (Int.castRingHom ℚ)

/-- Direct executable resultant replacing the Möbius quotient. -/
def degreeFourteenCyclotomicResultant (n : ℕ) : ℤ :=
  (Polynomial.cyclotomic n ℤ).resultant
    degreeFourteenCyclotomicQuadraticInt
    (Polynomial.cyclotomic n ℤ).natDegree
    degreeFourteenCyclotomicQuadraticInt.natDegree

theorem degreeFourteenCyclotomicQuadraticInt_map :
    degreeFourteenCyclotomicQuadraticInt.map (Int.castRingHom ℚ) =
      degreeFourteenCyclotomicQuadratic := by
  rfl

/-- The rational resultant in the norm theorem is the cast of the integral
resultant.  This isolates the remaining task as a purely integral product
factorization, with no field-extension API left. -/
theorem degreeFourteenCyclotomicResultant_rat_eq_intCast (n : ℕ) :
    (Polynomial.cyclotomic n ℚ).resultant
        degreeFourteenCyclotomicQuadratic
        (Polynomial.cyclotomic n ℚ).natDegree
        degreeFourteenCyclotomicQuadratic.natDegree =
      (degreeFourteenCyclotomicResultant n : ℚ) := by
  rw [← Polynomial.map_cyclotomic_int,
    ← degreeFourteenCyclotomicQuadraticInt_map]
  rw [Polynomial.natDegree_map_eq_of_injective
      Int.cast_injective (Polynomial.cyclotomic n ℤ),
    Polynomial.natDegree_map_eq_of_injective
      Int.cast_injective degreeFourteenCyclotomicQuadraticInt]
  simpa [degreeFourteenCyclotomicResultant] using
    Polynomial.resultant_map_map
      (Polynomial.cyclotomic n ℤ) degreeFourteenCyclotomicQuadraticInt
      (Polynomial.cyclotomic n ℤ).natDegree
      degreeFourteenCyclotomicQuadraticInt.natDegree (Int.castRingHom ℚ)

/-- Cyclotomic factorization turns the product of the conductor resultants
into one resultant against `X^n-1`.  This is the algebraic half of the
strong-induction comparison with the executable candidate product. -/
theorem prod_degreeFourteenCyclotomicResultant_eq_X_pow_sub_one_resultant
    {n : ℕ} (hn : 0 < n) :
    ∏ k ∈ n.divisors, degreeFourteenCyclotomicResultant k =
      (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant
        degreeFourteenCyclotomicQuadraticInt
        (Polynomial.X ^ n - 1 : Polynomial ℤ).natDegree
        degreeFourteenCyclotomicQuadraticInt.natDegree := by
  rw [← Polynomial.prod_cyclotomic_eq_X_pow_sub_one hn ℤ]
  rw [Polynomial.resultant_prod_left]
  · simp [degreeFourteenCyclotomicResultant]
  · simp only [(Polynomial.cyclotomic.monic _ ℤ).leadingCoeff,
      Finset.prod_const_one]
    norm_num
  · exact le_rfl

theorem degreeFourteenCyclotomicQuadratic_aeval
    {L : Type*} [Field L] [CharZero L] {z : L} (hz : z ≠ 0) :
    Polynomial.aeval z degreeFourteenCyclotomicQuadratic =
      z * ((13 : L) - (z + z⁻¹)) := by
  simp [degreeFourteenCyclotomicQuadratic,
    degreeFourteenCyclotomicQuadraticInt, Polynomial.aeval_def,
    Polynomial.eval₂_map]
  norm_num
  field_simp [hz]
  ring

/-- **Direct resultant bridge.**  For a primitive root of order at least
three, the square of the real-trace minimal-polynomial value at `13` is the
executable cyclotomic resultant with the quadratic above. -/
theorem primitiveTrace_minpoly_eval_thirteen_sq_eq_cyclotomic_resultant
    {L : Type*} [Field L] [CharZero L]
    {n : ℕ} {z : L} (hz : IsPrimitiveRoot z n) (hn : 3 ≤ n)
    [IsCyclotomicExtension {n} ℚ L] :
    (minpoly ℚ (z + z⁻¹)).eval 13 *
        (minpoly ℚ (z + z⁻¹)).eval 13 =
      (Polynomial.cyclotomic n ℚ).resultant
        degreeFourteenCyclotomicQuadratic
        (Polynomial.cyclotomic n ℚ).natDegree
        degreeFourteenCyclotomicQuadratic.natDegree := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hn)
  letI : NeZero n := ⟨hn0⟩
  have hirr : Irreducible (Polynomial.cyclotomic n ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)
  have hnormZ : Algebra.norm ℚ z = 1 :=
    hz.norm_eq_one (by omega) hirr
  have hresultant :=
    norm_aeval_primitiveRoot_eq_cyclotomic_resultant
      hz hn0 degreeFourteenCyclotomicQuadratic
  rw [degreeFourteenCyclotomicQuadratic_aeval (hz.ne_zero hn0),
    map_mul, hnormZ, one_mul] at hresultant
  have hnormTrace := norm_rat_sub_primitiveTrace_eq_minpoly_eval_sq
    hz hn (13 : ℚ)
  have hnormTrace' :
      Algebra.norm ℚ ((13 : L) - (z + z⁻¹)) =
        (minpoly ℚ (z + z⁻¹)).eval 13 *
          (minpoly ℚ (z + z⁻¹)).eval 13 := by
    simpa using hnormTrace
  exact hnormTrace'.symm.trans hresultant

end

end Erdos85
