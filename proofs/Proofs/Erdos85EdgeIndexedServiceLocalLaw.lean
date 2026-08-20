import Proofs.Erdos85EdgeIndexedServiceEquation

/-! # Entrywise local law of the edge-indexed service equation -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def internalEndpointNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : V) (a : R.edgeFinset) : Finset V :=
  a.1.toFinset.filter fun v ↦ H.Adj u v

def incidentServiceNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) : Finset R.edgeFinset :=
  (Cedge.neighborFinset a).filter fun b ↦ u ∈ b.1.toFinset

/-- Entrywise form of `H I + I C = J`: exactly one of an internal endpoint
service and an incident neighboring service edge occurs. -/
theorem edgeIndexedService_localLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge) :
    ∀ (u : V) (a : R.edgeFinset),
      (internalEndpointNeighborFinset H R u a).card +
        (incidentServiceNeighborFinset R Cedge u a).card = 1 := by
  classical
  intro u a
  have he := congrFun (congrFun hservice u) a
  unfold EdgeIndexedServiceEquation at he
  simp only [Matrix.add_apply, Matrix.mul_apply] at he
  have hfirst :
      ∑ v, H.adjMatrix ℂ u v * edgeEndpointIncidenceMatrix R v a =
        ((internalEndpointNeighborFinset H R u a).card : ℂ) := by
    calc
      _ = ∑ v : V, if v ∈ a.1.toFinset ∧ H.Adj u v then (1 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hm : v ∈ a.1.toFinset <;> by_cases ha : H.Adj u v <;>
          simp [edgeEndpointIncidenceMatrix, SimpleGraph.adjMatrix_apply, hm, ha]
      _ = (((Finset.univ : Finset V).filter fun v ↦
          v ∈ a.1.toFinset ∧ H.Adj u v).card : ℂ) := by
        simpa using (Finset.sum_boole (R := ℂ)
          (fun v : V ↦ v ∈ a.1.toFinset ∧ H.Adj u v) Finset.univ)
      _ = _ := by
        congr 1
        apply congrArg Finset.card
        ext v
        simp [internalEndpointNeighborFinset, and_comm]
  have hsecond :
      ∑ b, edgeEndpointIncidenceMatrix R u b * Cedge.adjMatrix ℂ b a =
        ((incidentServiceNeighborFinset R Cedge u a).card : ℂ) := by
    calc
      _ = ∑ b : R.edgeFinset,
          if Cedge.Adj a b ∧ u ∈ b.1.toFinset then (1 : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hm : u ∈ b.1.toFinset <;> by_cases ha : Cedge.Adj a b <;>
          simp [edgeEndpointIncidenceMatrix, SimpleGraph.adjMatrix_apply,
            hm, ha, Cedge.adj_comm]
      _ = (((Finset.univ : Finset R.edgeFinset).filter fun b ↦
          Cedge.Adj a b ∧ u ∈ b.1.toFinset).card : ℂ) := by
        simpa using (Finset.sum_boole (R := ℂ)
          (fun b : R.edgeFinset ↦ Cedge.Adj a b ∧ u ∈ b.1.toFinset)
          Finset.univ)
      _ = _ := by
        congr 1
        apply congrArg Finset.card
        ext b
        simp [incidentServiceNeighborFinset]
  rw [hfirst, hsecond] at he
  exact_mod_cast congrArg Complex.re he

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_localLaw
