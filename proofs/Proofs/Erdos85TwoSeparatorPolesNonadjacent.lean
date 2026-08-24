import Proofs.Erdos85TwoSeparatorCutRigidity
import Proofs.Erdos85BranchDeficitSymmetry

/-! # Sharp two-separator poles are nonadjacent -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If `R,Q,{x,y}` cover the vertices and no edge joins `R` to `Q`, the
cut of `R` is exactly its total incidence with the two poles. -/
theorem finsetGraphCutSize_eq_twoPole_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (R Q : Finset V) (x y : V) (hxy : x ≠ y)
    (hcover : R ∪ Q ∪ ({x, y} : Finset V) = Finset.univ)
    (hxR : x ∉ R) (hyR : y ∉ R)
    (hcross : ∀ a ∈ R, ∀ b ∈ Q, ¬ D.Adj a b) :
    finsetGraphCutSize D R =
      (D.neighborFinset x ∩ R).card + (D.neighborFinset y ∩ R).card := by
  have hpoint : ∀ a ∈ R, D.neighborFinset a \ R =
      D.neighborFinset a ∩ ({x, y} : Finset V) := by
    intro a ha
    ext z
    constructor
    · intro hz
      have hzN := (Finset.mem_sdiff.mp hz).1
      have hznotR := (Finset.mem_sdiff.mp hz).2
      have hzU : z ∈ R ∪ Q ∪ ({x, y} : Finset V) := by
        rw [hcover]
        simp
      rcases Finset.mem_union.mp hzU with hzRQ | hzPole
      · rcases Finset.mem_union.mp hzRQ with hzR | hzQ
        · exact (hznotR hzR).elim
        · exact (hcross a ha z hzQ
            ((SimpleGraph.mem_neighborFinset D a z).mp hzN)).elim
      · exact Finset.mem_inter.mpr ⟨hzN, hzPole⟩
    · intro hz
      have hzN := (Finset.mem_inter.mp hz).1
      have hzPole := (Finset.mem_inter.mp hz).2
      refine Finset.mem_sdiff.mpr ⟨hzN, ?_⟩
      intro hzR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzPole
      rcases hzPole with rfl | rfl
      · exact hxR hzR
      · exact hyR hzR
  calc
    finsetGraphCutSize D R =
        ∑ a ∈ R, (D.neighborFinset a ∩ ({x, y} : Finset V)).card := by
      unfold finsetGraphCutSize
      apply Finset.sum_congr rfl
      intro a ha
      rw [hpoint a ha]
    _ = ∑ w ∈ ({x, y} : Finset V),
        (D.neighborFinset w ∩ R).card :=
      sum_card_neighbor_inter_comm D R ({x, y} : Finset V)
    _ = (D.neighborFinset x ∩ R).card +
        (D.neighborFinset y ∩ R).card := by simp [hxy]

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

/-- Graph-facing sharp-separator wrapper: two degree-sized shore cuts across
the same pair of poles force the poles to be nonadjacent. -/
theorem not_adj_of_twoSeparator_both_cuts_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] {r : ℕ}
    (hreg : ∀ v, D.degree v = r)
    (S T : Finset V) (x y : V) (hxy : x ≠ y)
    (hcover : S ∪ T ∪ ({x, y} : Finset V) = Finset.univ)
    (hST : Disjoint S T)
    (hxS : x ∉ S) (hyS : y ∉ S) (hxT : x ∉ T) (hyT : y ∉ T)
    (hno : ∀ s ∈ S, ∀ t ∈ T, ¬ D.Adj s t)
    (hcutS : finsetGraphCutSize D S = r)
    (hcutT : finsetGraphCutSize D T = r) : ¬ D.Adj x y := by
  have hSinc := finsetGraphCutSize_eq_twoPole_incidence
    D S T x y hxy hcover hxS hyS hno
  have hcover' : T ∪ S ∪ ({x, y} : Finset V) = Finset.univ := by
    rw [Finset.union_comm T S]
    exact hcover
  have hno' : ∀ t ∈ T, ∀ s ∈ S, ¬ D.Adj t s := by
    intro t ht s hs hts
    exact hno s hs t ht ((D.adj_comm t s).mp hts)
  have hTinc := finsetGraphCutSize_eq_twoPole_incidence
    D T S x y hxy hcover' hxT hyT hno'
  apply not_adj_of_twoPole_shoreIncidences_eq_degree
    D hreg S T x y hST hxS hyS hxT hyT
  · rw [← hSinc, hcutS]
  · rw [← hTinc, hcutT]

#print axioms not_adj_of_twoPole_shoreIncidences_eq_degree
#print axioms finsetGraphCutSize_eq_twoPole_incidence
#print axioms not_adj_of_twoSeparator_both_cuts_eq_degree

end

end Erdos85
