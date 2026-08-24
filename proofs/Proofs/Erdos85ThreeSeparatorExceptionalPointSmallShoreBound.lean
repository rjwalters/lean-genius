import Proofs.Erdos85ThreeSeparatorPositiveSpikeSmallSideLocation

/-!
# Uniform exclusion of the exceptional point from the small shore

If the exceptional point `c` lies in `X`, component separation and (B18)
put `c` and its entire defect neighborhood in `K ∩ (X ∪ W)`.  This set
already has at least `q` points, whereas (B16) gives the upper bound
`3a + 4`.  This is (B19).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A vertex of defect degree `q-1`, together with itself, contributes `q`
distinct points to every finset containing both it and its neighborhood. -/
theorem degree_pred_center_insert_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (c : V) (q : ℕ)
    (hq : 1 ≤ q)
    (hdegree : D.degree c = q - 1) :
    (insert c (D.neighborFinset c)).card = q := by
  rw [Finset.card_insert_of_notMem (by simp), D.card_neighborFinset_eq_degree,
    hdegree]
  omega

/-- Graph-facing core of (B19): K-containment of the exceptional defect
neighborhood and component separation force `q ≤ 3a+4`. -/
theorem exceptionalPoint_mem_smallShore_forces_q_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (X W K : Finset V) (c : V) (q a rX : ℕ)
    (hq : 1 ≤ q)
    (hcX : c ∈ X)
    (hcK : c ∈ K)
    (hdegree : D.degree c = q - 1)
    (hneighborsK : D.neighborFinset c ⊆ K)
    (hneighborsSmall : D.neighborFinset c ⊆ X ∪ W)
    (hsmall : (K ∩ (X ∪ W)).card + rX = 3 * a + 4) :
    q ≤ 3 * a + 4 := by
  have hsubset : insert c (D.neighborFinset c) ⊆ K ∩ (X ∪ W) := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact Finset.mem_inter.mpr ⟨hcK, Finset.mem_union_left W hcX⟩
    · exact Finset.mem_inter.mpr ⟨hneighborsK hv, hneighborsSmall hv⟩
  have hqsmall : q ≤ (K ∩ (X ∪ W)).card := by
    rw [← degree_pred_center_insert_card D c q hq hdegree]
    exact Finset.card_le_card hsubset
  omega

/-- Contrapositive location form of (B19). -/
theorem exceptionalPoint_not_mem_smallShore_of_parameter_range
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (X W K : Finset V) (c : V) (q a rX : ℕ)
    (hq : 1 ≤ q)
    (hcK : c ∈ K)
    (hdegree : D.degree c = q - 1)
    (hneighborsK : D.neighborFinset c ⊆ K)
    (hneighborsSmall : D.neighborFinset c ⊆ X ∪ W)
    (hsmall : (K ∩ (X ∪ W)).card + rX = 3 * a + 4)
    (hrange : 3 * a + 4 < q) :
    c ∉ X := by
  intro hcX
  have := exceptionalPoint_mem_smallShore_forces_q_le
    D X W K c q a rX hq hcX hcK hdegree hneighborsK hneighborsSmall hsmall
  omega

end

end Erdos85

#print axioms Erdos85.degree_pred_center_insert_card
#print axioms Erdos85.exceptionalPoint_mem_smallShore_forces_q_le
#print axioms Erdos85.exceptionalPoint_not_mem_smallShore_of_parameter_range
