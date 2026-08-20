import Proofs.Erdos85EdgeIndexedServiceSquaredEquation

/-! # Cubic edge-indexed service equation

The squared service equation can be multiplied once more by the exterior
adjacency matrix.  Regularity then removes every all-ones term and yields an
exact endpoint-weighted cubic-walk identity.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Cubic refinement of the edge-indexed service equation.  If the internal
shore is `h`-regular and the exterior edge graph is `c`-regular, then
`I C³ = (h² - hc + c²)J - H³I`. -/
theorem edgeIndexedService_cubicEquation_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (h c : ℕ) (hHreg : ∀ x, H.degree x = h)
    (hCreg : ∀ a, Cedge.degree a = c) :
    edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ ^ 3 =
      (((h : ℂ) ^ 2 - (h : ℂ) * c + (c : ℂ) ^ 2) •
          edgeIndexedOnesMatrix R) -
        H.adjMatrix ℂ ^ 3 * edgeEndpointIncidenceMatrix R := by
  let A := H.adjMatrix ℂ
  let I := edgeEndpointIncidenceMatrix R
  let C := Cedge.adjMatrix ℂ
  let J : Matrix V R.edgeFinset ℂ := edgeIndexedOnesMatrix R
  have hs : A * I + I * C = J := by
    unfold EdgeIndexedServiceEquation at hservice
    change H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R +
      edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ = J
    change H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R +
      edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ = fun _ _ ↦ 1
    exact hservice
  have hAJ : A * J = (h : ℂ) • J := by
    simpa [A, J] using
      (adjMatrix_mul_edgeIndexedOnesMatrix_of_regular H R h hHreg)
  have hJC : J * C = (c : ℂ) • J := by
    simpa [C, J] using
      (edgeIndexedOnesMatrix_mul_adjMatrix_of_regular R Cedge c hCreg)
  have hsq : A * A * I - I * C * C = ((h : ℂ) - c) • J := by
    simpa [A, I, C, J] using
      (edgeIndexedService_squaredEquation_of_regular H R Cedge hservice
        h c hHreg hCreg)
  have hA2J : A * A * J = ((h : ℂ) ^ 2) • J := by
    rw [Matrix.mul_assoc, hAJ, Matrix.mul_smul, hAJ]
    ext x a
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hsqC := congrArg (fun M : Matrix V R.edgeFinset ℂ ↦ M * C) hsq
  have hC3 : C ^ 3 = C * C * C := by
    simp [pow_succ, Matrix.mul_assoc]
  change I * C ^ 3 =
    (((h : ℂ) ^ 2 - (h : ℂ) * c + (c : ℂ) ^ 2) • J) - A ^ 3 * I
  calc
    I * C ^ 3 = A * A * I * C - (((h : ℂ) - c) • J) * C := by
      rw [hC3]
      rw [← hsqC]
      simp only [Matrix.sub_mul, Matrix.mul_assoc]
      noncomm_ring
    _ = A * A * (J - A * I) - (((h : ℂ) - c) • J) * C := by
      have hIC : I * C = J - A * I := by
        rw [← hs]
        noncomm_ring
      rw [Matrix.mul_assoc (A * A) I C, hIC]
    _ = A * A * J - A ^ 3 * I - (((h : ℂ) - c) • J) * C := by
      rw [Matrix.mul_sub]
      congr 2
      simp [pow_succ, Matrix.mul_assoc]
    _ = ((h : ℂ) ^ 2) • J - A ^ 3 * I -
          (((h : ℂ) - c) * c) • J := by
      rw [hA2J, Matrix.smul_mul, hJC]
      ext x a
      simp [mul_assoc]
    _ = (((h : ℂ) ^ 2 - (h : ℂ) * c + (c : ℂ) ^ 2) • J) -
          A ^ 3 * I := by
      ext x a
      simp [J, edgeIndexedOnesMatrix]
      ring

/-- In the order-64 service model the shore has degree two and the exterior
edge graph degree six, so every endpoint-weighted cubic row sum is governed
by the constant `28`. -/
theorem edgeIndexedService_cubicEquation_two_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6) :
    edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ ^ 3 =
      (28 : ℂ) • edgeIndexedOnesMatrix R -
        H.adjMatrix ℂ ^ 3 * edgeEndpointIncidenceMatrix R := by
  convert edgeIndexedService_cubicEquation_of_regular H R Cedge hservice
    2 6 hHreg hCreg using 1 <;> norm_num

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_cubicEquation_two_six
