import Proofs.Erdos85TwoSeparatorCutRigidity

/-! # Sharp two-separator poles are nonadjacent -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If the incidences from two separator poles into each of two disjoint
shores both exhaust the regular degree, the poles cannot be adjacent. -/
theorem not_adj_of_twoPole_shoreIncidences_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ v, D.degree v = r)
    (S T : Finset V) (x y : V)
    (hST : Disjoint S T)
    (hxS : x ∉ S) (hyS : y ∉ S) (hxT : x ∉ T) (hyT : y ∉ T)
    (hSinc : (D.neighborFinset x ∩ S).card +
      (D.neighborFinset y ∩ S).card = r)
    (hTinc : (D.neighborFinset x ∩ T).card +
      (D.neighborFinset y ∩ T).card = r) :
    ¬ D.Adj x y := by
  intro hxy
  have pole_capacity (u v : V) (hvS : v ∉ S) (hvT : v ∉ T)
      (huv : D.Adj u v) :
      (D.neighborFinset u ∩ S).card +
        (D.neighborFinset u ∩ T).card + 1 ≤ r := by
    have hdisj : Disjoint (D.neighborFinset u ∩ S)
        (D.neighborFinset u ∩ T) :=
      hST.mono Finset.inter_subset_right Finset.inter_subset_right
    have hvNot : v ∉ (D.neighborFinset u ∩ S) ∪
        (D.neighborFinset u ∩ T) := by
      intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hvS (Finset.mem_inter.mp hv).2
      · exact hvT (Finset.mem_inter.mp hv).2
    have hsub : insert v ((D.neighborFinset u ∩ S) ∪
        (D.neighborFinset u ∩ T)) ⊆ D.neighborFinset u := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_union] at hz
      rcases hz with rfl | hz
      · exact (SimpleGraph.mem_neighborFinset D u _).mpr huv
      · rcases hz with hz | hz <;> exact (Finset.mem_inter.mp hz).1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hvNot,
      Finset.card_union_of_disjoint hdisj,
      D.card_neighborFinset_eq_degree, hreg u] at hc
    omega
  have hxcap := pole_capacity x y hyS hyT hxy
  have hycap := pole_capacity y x hxS hxT ((D.adj_comm x y).mp hxy)
  omega

#print axioms not_adj_of_twoPole_shoreIncidences_eq_degree

end

end Erdos85
