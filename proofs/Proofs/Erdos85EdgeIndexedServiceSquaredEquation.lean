import Proofs.Erdos85EdgeIndexedServiceEigenvectorTransfer

/-! # Squared edge-indexed service equation -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Rectangular all-ones matrix in exterior-edge coordinates. -/
def edgeIndexedOnesMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] :
    Matrix V R.edgeFinset ℂ := fun _ _ ↦ 1

theorem adjMatrix_mul_edgeIndexedOnesMatrix_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (d : ℕ) (hreg : ∀ x, H.degree x = d) :
    H.adjMatrix ℂ * edgeIndexedOnesMatrix R =
      (d : ℂ) • edgeIndexedOnesMatrix R := by
  classical
  ext x a
  simp only [Matrix.mul_apply, Matrix.smul_apply, edgeIndexedOnesMatrix,
    mul_one, smul_eq_mul]
  trans (((Finset.univ.filter fun y ↦ H.Adj x y).card : ℕ) : ℂ)
  · rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro y _
    simp [SimpleGraph.adjMatrix_apply]
  · have hfilt : Finset.univ.filter (fun y ↦ H.Adj x y) =
        H.neighborFinset x := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt, ← SimpleGraph.degree, hreg]

theorem edgeIndexedOnesMatrix_mul_adjMatrix_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (d : ℕ) (hreg : ∀ a, Cedge.degree a = d) :
    edgeIndexedOnesMatrix R * Cedge.adjMatrix ℂ =
      (d : ℂ) • edgeIndexedOnesMatrix R := by
  classical
  ext x a
  simp only [Matrix.mul_apply, Matrix.smul_apply, edgeIndexedOnesMatrix,
    one_mul, smul_eq_mul]
  trans (((Finset.univ.filter fun b ↦ Cedge.Adj a b).card : ℕ) : ℂ)
  · rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro b _
    simp [SimpleGraph.adjMatrix_apply, Cedge.adj_comm]
  · have hfilt : Finset.univ.filter (fun b ↦ Cedge.Adj a b) =
        Cedge.neighborFinset a := by
      ext b
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt, ← SimpleGraph.degree, hreg]
    simp

/-- Squaring the two sides of the service intertwiner eliminates the mixed
term.  If `H J = h J` and `J C = c J`, then
`H² I - I C² = (h-c)J`.  For the order-64 service model, `h=2` and `c=6`. -/
theorem edgeIndexedService_squaredEquation
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (h c : ℂ)
    (hHJ : H.adjMatrix ℂ * edgeIndexedOnesMatrix R =
      h • edgeIndexedOnesMatrix R)
    (hJC : edgeIndexedOnesMatrix R * Cedge.adjMatrix ℂ =
      c • edgeIndexedOnesMatrix R) :
    H.adjMatrix ℂ * H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R -
        edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ *
          Cedge.adjMatrix ℂ =
      (h - c) • edgeIndexedOnesMatrix R := by
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
  have hleft := congrArg (fun M : Matrix V R.edgeFinset ℂ ↦ A * M) hs
  have hright := congrArg (fun M : Matrix V R.edgeFinset ℂ ↦ M * C) hs
  have hleft' : A * A * I + A * I * C = h • J := by
    calc
      _ = A * J := by
        simpa [Matrix.mul_add, Matrix.mul_assoc] using hleft
      _ = h • J := by simpa [A, J] using hHJ
  have hright' : A * I * C + I * C * C = c • J := by
    calc
      _ = J * C := by
        simpa [Matrix.add_mul, Matrix.mul_assoc] using hright
      _ = c • J := by simpa [C, J] using hJC
  change A * A * I - I * C * C = (h - c) • J
  calc
    A * A * I - I * C * C =
        (A * A * I + A * I * C) - (A * I * C + I * C * C) := by
          noncomm_ring
    _ = h • J - c • J := by rw [hleft', hright']
    _ = (h - c) • J := by
      ext x a
      simp [J, edgeIndexedOnesMatrix]

/-- Regular specialization used by the order-64 edge-service model. -/
theorem edgeIndexedService_squaredEquation_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (h c : ℕ) (hHreg : ∀ x, H.degree x = h)
    (hCreg : ∀ a, Cedge.degree a = c) :
    H.adjMatrix ℂ * H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R -
        edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ *
          Cedge.adjMatrix ℂ =
      ((h : ℂ) - c) • edgeIndexedOnesMatrix R := by
  exact edgeIndexedService_squaredEquation H R Cedge hservice h c
    (adjMatrix_mul_edgeIndexedOnesMatrix_of_regular H R h hHreg)
    (edgeIndexedOnesMatrix_mul_adjMatrix_of_regular R Cedge c hCreg)

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_squaredEquation
