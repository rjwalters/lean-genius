/-
  Similar Matrices Have Identical Minimal Polynomials
  (cayley-hamilton-minpoly-oq-02)

  Open Question: Can we formalize the theorem that similar matrices have
  identical minimal polynomials in Lean 4 using Mathlib?

  Answer: YES. This file provides a complete formal proof.

  Key result: If B = P⁻¹AP for some invertible matrix P (as a unit in
  Matrix n n K), then minpoly K A = minpoly K B.

  Proof strategy:
  1. Define the inner conjugation automorphism as a K-algebra endomorphism
  2. Use Polynomial.aeval_algHom_apply to commute aeval with conjugation
  3. Apply minpoly.unique to identify the minimal polynomials

  Note: We use P.val (resp. P⁻¹.val) to coerce units to their
  underlying matrices, since ↑P⁻¹ parses as (↑P)⁻¹ in Lean 4.
  Note: ring tactic requires CommSemiring and fails for Matrix n n K
  (non-commutative for n ≥ 2); we use simp [mul_assoc] instead.
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic

namespace MinpolySimilar

variable {K : Type*} [Field K] {n : Type*} [DecidableEq n] [Fintype n]

/-
  Part I: Conjugation as an algebra endomorphism
-/

/-- The inner automorphism of Matrix n n K given by conjugation by P.
    The map A ↦ P⁻¹AP is a K-algebra endomorphism. -/
noncomputable def conjAlgHom (P : (Matrix n n K)ˣ) :
    Matrix n n K →ₐ[K] Matrix n n K where
  toFun := fun A => P⁻¹.val * A * P.val
  map_one' := by
    rw [mul_one, Units.inv_mul]
  map_mul' := fun A B => by
    have h : P.val * P⁻¹.val = 1 := Units.mul_inv P
    have key : (P⁻¹.val * A * P.val) * (P⁻¹.val * B * P.val)
        = P⁻¹.val * A * (P.val * P⁻¹.val) * B * P.val := by
      simp only [mul_assoc]
    rw [key, h, mul_one]
    simp only [mul_assoc]
  map_zero' := by simp
  map_add' := fun A B => by
    simp [mul_add, add_mul]
  commutes' := fun c => by
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm]
    rw [mul_one, Units.inv_mul]

/-- Polynomial evaluation commutes with conjugation:
    aeval(P⁻¹AP)(p) = P⁻¹ · aeval(A)(p) · P -/
lemma aeval_conj (A : Matrix n n K) (P : (Matrix n n K)ˣ) (p : Polynomial K) :
    Polynomial.aeval (P⁻¹.val * A * P.val) p =
      P⁻¹.val * Polynomial.aeval A p * P.val := by
  have h : Polynomial.aeval (P⁻¹.val * A * P.val) p =
      (conjAlgHom P) (Polynomial.aeval A p) := by
    rw [← Polynomial.aeval_algHom_apply (conjAlgHom P) A p]
    rfl
  rw [h]
  rfl

/-- Conjugation by an invertible matrix preserves zero:
    P⁻¹ M P = 0 ↔ M = 0 -/
lemma conj_eq_zero_iff (M : Matrix n n K) (P : (Matrix n n K)ˣ) :
    P⁻¹.val * M * P.val = 0 ↔ M = 0 := by
  constructor
  · intro h
    calc M = 1 * M * 1 := by simp only [one_mul, mul_one]
      _ = (P.val * P⁻¹.val) * M * (P.val * P⁻¹.val) := by rw [Units.mul_inv]
      _ = P.val * (P⁻¹.val * M * P.val) * P⁻¹.val := by simp only [mul_assoc]
      _ = P.val * 0 * P⁻¹.val := by rw [h]
      _ = 0 := by simp only [mul_zero, zero_mul]
  · intro h; rw [h]; simp

/-
  Part II: Main theorem
-/

/-- **Main Theorem**: If B = P⁻¹AP for invertible P, then A and B have
    the same minimal polynomial over K.

    This answers the formalization question affirmatively. -/
theorem minpoly_similar (A : Matrix n n K) (P : (Matrix n n K)ˣ) :
    minpoly K A = minpoly K (P⁻¹.val * A * P.val) := by
  apply minpoly.unique K (P⁻¹.val * A * P.val)
  · -- minpoly(A) is monic
    exact minpoly.monic (Matrix.isIntegral A)
  · -- minpoly(A) annihilates P⁻¹AP
    rw [aeval_conj, minpoly.aeval, mul_zero, zero_mul]
  · -- minpoly(A) is minimal for P⁻¹AP
    intro q hq_monic hq_aeval
    rw [aeval_conj] at hq_aeval
    have hA_zero : Polynomial.aeval A q = 0 :=
      (conj_eq_zero_iff _ P).mp hq_aeval
    exact minpoly.min K A hq_monic hA_zero

/-
  Part III: Corollaries
-/

/-- Similar matrices have the same minimal polynomial (symmetric form). -/
theorem minpoly_similar_symm (A : Matrix n n K) (P : (Matrix n n K)ˣ) :
    minpoly K (P⁻¹.val * A * P.val) = minpoly K A :=
  (minpoly_similar A P).symm

/-- A direct reformulation using matrix similarity. -/
theorem minpoly_of_similar {A B : Matrix n n K}
    (P : (Matrix n n K)ˣ) (hB : B = P⁻¹.val * A * P.val) :
    minpoly K A = minpoly K B := hB ▸ minpoly_similar A P

/-- Conjugation by the inverse: minpoly(PAP⁻¹) = minpoly(A). -/
theorem minpoly_conj_inv (A : Matrix n n K) (P : (Matrix n n K)ˣ) :
    minpoly K (P.val * A * P⁻¹.val) = minpoly K A := by
  have h : P.val = (P⁻¹)⁻¹.val := (congr_arg Units.val (inv_inv P)).symm
  rw [h]; exact (minpoly_similar A P⁻¹).symm

/-
  Part IV: Relationship to characteristic polynomial
-/

/-- The minimal polynomial divides the characteristic polynomial. -/
theorem minpoly_dvd_charpoly (A : Matrix n n K) :
    minpoly K A ∣ A.charpoly :=
  Matrix.minpoly_dvd_charpoly A

end MinpolySimilar
