import Proofs.Erdos85Polarity

/-!
# Degree and cardinality of the finite-field polarity graph
-/

open SimpleGraph Finset
open scoped LinearAlgebra.Projectivization

namespace Erdos85.Polarity

variable {K : Type*} [Field K] [Finite K] [DecidableEq K]

noncomputable def incidentFinset (x : ℙ K (Fin 3 → K)) :
    Finset (ℙ K (Fin 3 → K)) := by
  classical
  exact Finset.univ.filter (fun y ↦ y ∈ x)

theorem card_incidentFinset (x : ℙ K (Fin 3 → K)) :
    (incidentFinset x).card = Configuration.ProjectivePlane.order
      (ℙ K (Fin 3 → K)) (ℙ K (Fin 3 → K)) + 1 := by
  classical
  rw [← Configuration.ProjectivePlane.pointCount_eq (ℙ K (Fin 3 → K)) x]
  rw [Configuration.pointCount, Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype (fun y : ℙ K (Fin 3 → K) ↦ y ∈ x)).symm

theorem neighborFinset_eq_erase_incidentFinset (x : ℙ K (Fin 3 → K)) :
    (graph K).neighborFinset x = (incidentFinset x).erase x := by
  classical
  ext y
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, incidentFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [graph_adj_iff, Configuration.ofField.mem_iff]
  constructor
  · rintro ⟨hxy, horth⟩
    exact ⟨hxy.symm, Projectivization.orthogonal_comm.mp horth⟩
  · rintro ⟨hyx, horth⟩
    exact ⟨hyx.symm, Projectivization.orthogonal_comm.mpr horth⟩

theorem order_le_degree (x : ℙ K (Fin 3 → K)) :
    Configuration.ProjectivePlane.order (ℙ K (Fin 3 → K))
      (ℙ K (Fin 3 → K)) ≤ (graph K).degree x := by
  classical
  rw [SimpleGraph.degree, neighborFinset_eq_erase_incidentFinset]
  by_cases hx : x ∈ incidentFinset x
  · rw [Finset.card_erase_of_mem hx, card_incidentFinset]
    omega
  · simp only [Finset.erase_eq_self.mpr hx, card_incidentFinset]
    omega

theorem order_le_minDegree :
    Configuration.ProjectivePlane.order (ℙ K (Fin 3 → K))
      (ℙ K (Fin 3 → K)) ≤ (graph K).minDegree := by
  classical
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  exact order_le_degree

end Erdos85.Polarity
