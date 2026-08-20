import Proofs.Erdos85EdgeIndexedServiceNoCommonNeighbor

/-! # Finite census form of the edge-service two-walk law -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem adjMatrix_sq_apply_eq_card_common_complex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (G.adjMatrix ℂ * G.adjMatrix ℂ) x y =
      ((G.neighborFinset x ∩ G.neighborFinset y).card : ℂ) := by
  rw [G.adjMatrix_mul_apply]
  simp only [SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  have hfilt : (G.neighborFinset x).filter (fun z ↦ G.Adj z y) =
      G.neighborFinset x ∩ G.neighborFinset y := by
    ext z
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [hfilt]

/-- Common-service-neighbor mass over all exterior edges incident to `u`. -/
def incidentServiceTwoWalkMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) : ℕ :=
  ∑ b : R.edgeFinset, if u ∈ b.1.toFinset then
    (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).card else 0

/-- Internal two-walk mass from `u` to the two endpoints of `a`. -/
def internalEndpointTwoWalkMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : V) (a : R.edgeFinset) : ℕ :=
  ∑ v : V, if v ∈ a.1.toFinset then
    (H.neighborFinset u ∩ H.neighborFinset v).card else 0

theorem edgeIncidence_mul_service_sq_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) :
    (edgeEndpointIncidenceMatrix R * Cedge.adjMatrix ℂ *
        Cedge.adjMatrix ℂ) u a =
      (incidentServiceTwoWalkMass R Cedge u a : ℂ) := by
  classical
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [incidentServiceTwoWalkMass, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [adjMatrix_sq_apply_eq_card_common_complex Cedge b a]
  by_cases hu : u ∈ b.1.toFinset <;>
    simp [edgeEndpointIncidenceMatrix, hu]

theorem internalSq_mul_edgeIncidence_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : V) (a : R.edgeFinset) :
    (H.adjMatrix ℂ * H.adjMatrix ℂ * edgeEndpointIncidenceMatrix R) u a =
      (internalEndpointTwoWalkMass H R u a : ℂ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [internalEndpointTwoWalkMass, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [adjMatrix_sq_apply_eq_card_common_complex H u v]
  by_cases hv : v ∈ a.1.toFinset <;>
    simp [edgeEndpointIncidenceMatrix, hv]

/-- Exact natural-number census behind `H²I - IC² = -4J`. -/
theorem edgeIndexedService_twoWalkCensus
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : V) (a : R.edgeFinset) :
    incidentServiceTwoWalkMass R Cedge u a =
      internalEndpointTwoWalkMass H R u a + 4 := by
  have h := edgeIndexedService_twoWalkLaw
    H R Cedge hservice hHreg hCreg u a
  rw [edgeIncidence_mul_service_sq_apply,
    internalSq_mul_edgeIncidence_apply] at h
  exact_mod_cast congrArg Complex.re h

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_twoWalkCensus
