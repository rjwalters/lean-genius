import Proofs.Erdos85PolarityDeletion
import Mathlib.FieldTheory.ChevalleyWarning

/-!
# Absolute points of finite-field orthogonal polarities

Chevalley--Warning supplies a nonzero zero of the ternary quadratic form
`X₀² + X₁² + X₂²` over every finite field.  Projectivizing that vector removes
the hypothesis from the one-point deletion construction.
-/

open SimpleGraph Finset MvPolynomial
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

universe u

variable (K : Type u) [Field K] [Finite K] [DecidableEq K]

private noncomputable abbrev P := ℙ K (Fin 3 → K)
private noncomputable abbrev q := Nat.card K

private noncomputable def isotropicPolynomial : MvPolynomial (Fin 3) K :=
  ∑ i : Fin 3, X i ^ 2

private theorem isotropicPolynomial_totalDegree_lt :
    (isotropicPolynomial K).totalDegree < Fintype.card (Fin 3) := by
  have hle : (isotropicPolynomial K).totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro i hi
    simp [totalDegree_X_pow]
  simpa using lt_of_le_of_lt hle (by decide : 2 < Fintype.card (Fin 3))

private theorem eval_isotropicPolynomial (v : Fin 3 → K) :
    eval v (isotropicPolynomial K) = v ⬝ᵥ v := by
  simp [isotropicPolynomial, dotProduct, pow_two]

/-- Every finite field has a nonzero isotropic vector in dimension three. -/
theorem exists_nonzero_self_dot_zero :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ v ⬝ᵥ v = 0 := by
  classical
  letI := Fintype.ofFinite K
  let S := {v : Fin 3 → K // eval v (isotropicPolynomial K) = 0}
  have hdvd : ringChar K ∣ Fintype.card S :=
    char_dvd_card_solutions (K := K) (ringChar K)
      (isotropicPolynomial_totalDegree_lt K)
  by_contra h
  have hzero : ∀ v : Fin 3 → K, v ⬝ᵥ v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    exact h ⟨v, hv0, hv⟩
  have huniq : ∀ z : S, z = ⟨0, by simp [isotropicPolynomial]⟩ := by
    intro z
    apply Subtype.ext
    exact hzero z.1 (by simpa [eval_isotropicPolynomial] using z.2)
  have hcard : Fintype.card S = 1 := Fintype.card_eq_one_iff.mpr
    ⟨⟨0, by simp [isotropicPolynomial]⟩, huniq⟩
  rw [hcard] at hdvd
  exact (CharP.ringChar_ne_one (R := K)) (Nat.dvd_one.mp hdvd)

/-- Every finite-field orthogonal projective plane has an absolute point. -/
theorem exists_selfOrthogonal :
    ∃ x : P K, Projectivization.orthogonal x x := by
  obtain ⟨v, hv, hdot⟩ := exists_nonzero_self_dot_zero K
  exact ⟨Projectivization.mk K v hv,
    (Projectivization.orthogonal_mk hv hv).2 hdot⟩

/-- Unconditional witness one vertex below the projective-plane order. -/
theorem c4FreeMinDegreeWitness_projectivePlane_pred :
    C4FreeMinDegreeWitness ((q K + 1) * q K) (q K) := by
  obtain ⟨x, hx⟩ := exists_selfOrthogonal K
  exact c4FreeMinDegreeWitness_card_mul_add x hx

/-- The second infinite exact family: `f(q²+q)=q+1`. -/
theorem minDegreeForC4_projectivePlane_pred :
    minDegreeForC4 ((q K + 1) * q K) = q K + 1 := by
  obtain ⟨x, hx⟩ := exists_selfOrthogonal K
  exact minDegreeForC4_card_mul_add x hx

end Erdos85.Polarity
