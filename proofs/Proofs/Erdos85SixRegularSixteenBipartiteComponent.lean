import Proofs.Erdos85ComponentLocalObstruction
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# A bipartite component fills a six-regular graph of order sixteen

A bipartite six-regular component contains the disjoint neighborhoods of the
two endpoints of any edge, hence at least twelve vertices.  Every other
six-regular component contains a vertex and its six neighbors, hence at least
seven.  Since `12 + 7 > 16`, no second component exists.
-/

open SimpleGraph

namespace Erdos85

/-- A six-regular graph on sixteen vertices is connected as soon as one of
its connected components is bipartite. -/
theorem connected_of_sixRegular_sixteen_of_bipartiteComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x, G.degree x = 6)
    (c : G.ConnectedComponent)
    (hbip : (G.induce c.supp).IsBipartite) :
    G.Connected := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let H := G.induce c.supp
  have hconnH : H.Connected := c.connected_toSimpleGraph
  have hregH : ∀ x, H.degree x = 6 := by
    intro x
    rw [degree_induce_connectedComponent_supp G c x, hreg]
  let x : c.supp := Classical.choice hconnH.nonempty
  have hxcard : (H.neighborFinset x).card = 6 := by
    rw [H.card_neighborFinset_eq_degree, hregH]
  obtain ⟨y, hy⟩ := (H.neighborFinset x).nonempty_of_ne_empty (by
    intro hempty
    rw [hempty, Finset.card_empty] at hxcard
    omega)
  have hxy : H.Adj x y := (H.mem_neighborFinset x y).mp hy
  obtain ⟨S, T, hST⟩ :=
    SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp hbip
  have hdisj : Disjoint (H.neighborFinset x) (H.neighborFinset y) := by
    rw [Finset.disjoint_left]
    intro z hzx hzy
    have hxz : H.Adj x z := (H.mem_neighborFinset x z).mp hzx
    have hyz : H.Adj y z := (H.mem_neighborFinset y z).mp hzy
    rcases hST.mem_of_adj hxy with ⟨hxS, hyT⟩ | ⟨hxT, hyS⟩
    · have hzT := hST.mem_of_mem_adj hxS hxz
      have hzS := hST.mem_of_mem_adj' hyT hyz.symm
      exact Set.disjoint_left.mp hST.disjoint hzS hzT
    · have hzS := hST.mem_of_mem_adj' hxT hxz.symm
      have hzT := hST.mem_of_mem_adj hyS hyz
      exact Set.disjoint_left.mp hST.disjoint hzS hzT
  have hc12 : 12 ≤ c.supp.ncard := by
    have hunion : (H.neighborFinset x ∪ H.neighborFinset y).card = 12 := by
      rw [Finset.card_union_of_disjoint hdisj,
        H.card_neighborFinset_eq_degree, H.card_neighborFinset_eq_degree,
        hregH, hregH]
    have hle := Finset.card_le_card
      (show H.neighborFinset x ∪ H.neighborFinset y ⊆ Finset.univ from
        Finset.subset_univ _)
    rw [hunion, Finset.card_univ] at hle
    simpa [Nat.card_eq_fintype_card, Set.ncard_eq_toFinset_card'] using hle
  have hsupp : c.supp = Set.univ := by
    by_contra hne
    have hex : ∃ z, z ∉ c.supp := by
      by_contra hno
      apply hne
      apply Set.eq_univ_of_forall
      intro z
      by_contra hz
      exact hno ⟨z, hz⟩
    obtain ⟨z, hz⟩ := hex
    let Z : Finset V := insert z (G.neighborFinset z)
    have hznot : z ∉ G.neighborFinset z := by simp
    have hZcard : Z.card = 7 := by
      simp only [Z, Finset.card_insert_of_notMem hznot,
        G.card_neighborFinset_eq_degree, hreg]
    have hZout : Z ⊆ Finset.univ \ c.supp.toFinset := by
      intro u hu
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ u, ?_⟩
      simp only [Set.mem_toFinset]
      intro huc
      have huz : u = z ∨ u ∈ G.neighborFinset z :=
        Finset.mem_insert.mp hu
      rcases huz with rfl | huz
      · exact hz huc
      · have hadj : G.Adj z u := (G.mem_neighborFinset z u).mp huz
        exact hz ((ConnectedComponent.mem_supp_congr_adj c hadj).mpr huc)
    have hout7 : 7 ≤ (Finset.univ \ c.supp.toFinset).card := by
      rw [← hZcard]
      exact Finset.card_le_card hZout
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcard] at hout7
    have hc12' : 12 ≤ c.supp.toFinset.card := by
      simpa [Set.ncard_eq_toFinset_card'] using hc12
    omega
  apply SimpleGraph.Connected.mk
  intro u v
  apply c.reachable_of_mem_supp
  · rw [hsupp]
    trivial
  · rw [hsupp]
    trivial

end Erdos85

#print axioms Erdos85.connected_of_sixRegular_sixteen_of_bipartiteComponent
