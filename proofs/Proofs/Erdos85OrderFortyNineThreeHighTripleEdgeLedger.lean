import Proofs.Erdos85OrderFortyNineThreeHighTripleFarVertex
import Proofs.Erdos85SquareOrderTwoHighTerminal

/-! Actual edge ledger e(U)=17+e(R) for the triple-profile partition. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem internal_mass
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (B : Finset (Fin 49)) :
    (∑ x ∈ B, (G.neighborFinset x ∩ B).card) =
      2 * (G.induce (↑B : Set (Fin 49))).edgeFinset.card := by
  classical
  have hs : (∑ x ∈ B, (G.neighborFinset x ∩ B).card) =
      ∑ x : (↑B : Set (Fin 49)), (G.induce (↑B : Set (Fin 49))).degree x := by
    simp only [degree_induce_finset_eq_card_inter]
    exact Finset.sum_subtype B (fun _ => Iff.rfl) _
  rw [hs, SimpleGraph.sum_degrees_eq_twice_card_edges]

theorem threeHigh_triple_union_secondary_edge_ledger
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    let U := threeHighTripleSpecialUnion G z
    let R := threeHighTripleEmptySet G \ insert u U
    (G.induce (↑U : Set (Fin 49))).edgeFinset.card =
      17 + (G.induce (↑R : Set (Fin 49))).edgeFinset.card ∧
    (∑ x ∈ U, (G.neighborFinset x ∩ R).card) +
      2 * (G.induce (↑R : Set (Fin 49))).edgeFinset.card = 26 := by
  classical
  let E := threeHighTripleEmptySet G
  let U := threeHighTripleSpecialUnion G z
  let R := E \ insert u U
  change (G.induce (↑U : Set (Fin 49))).edgeFinset.card =
    17 + (G.induce (↑R : Set (Fin 49))).edgeFinset.card ∧
    (∑ x ∈ U, (G.neighborFinset x ∩ R).card) +
    2 * (G.induce (↑R : Set (Fin 49))).edgeFinset.card = 26
  have hp := threeHigh_triple_secondary_partition G hfree hmin hHigh hone z hz hu huz
  have hU : U.card = 15 := hp.1
  have hR : R.card = 8 := hp.2.2.1
  have huU : u ∉ U := hp.2.1
  have hUE : U ⊆ E := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_inter.mp hxs).2
  have hRE : R ⊆ E := Finset.sdiff_subset
  have huR : u ∉ R := by
    intro hm
    exact (Finset.mem_sdiff.mp hm).2 (Finset.mem_insert_self _ _)
  have hd4 (x : Fin 49) (hx : x ∈ E) (hxu : x ≠ u) :
      (G.neighborFinset x ∩ E).card = 4 := by
    have hx0 := (Finset.mem_filter.mp hx).2
    have hx7 : G.degree x = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) x with h | h
      · exact h
      · exact ((Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2
          (by simp [orderFortyNineHighVertices, h])).elim
    have hxz : ¬ G.Adj x z := by
      intro ha
      have hc := threeHigh_triple_root_empty_neighbor_count G hfree hmin hHigh hone z hz
      change (G.neighborFinset z ∩ E).card = 1 at hc
      exact hxu (Finset.card_le_one.mp hc.le x
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z x).mpr ha.symm, hx⟩) u
        (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z u).mpr huz.symm, hu⟩))
    have hh := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hx7
    simpa [E, threeHighTripleEmptySet, hx0, hxz] using hh
  have hmassU : (∑ x ∈ U, (G.neighborFinset x ∩ E).card) = 60 := by
    calc
      _ = ∑ _x ∈ U, 4 := Finset.sum_congr rfl (fun x hx =>
        hd4 x (hUE hx) (by intro h; subst x; exact huU hx))
      _ = 60 := by simp [hU]
  have hmassR : (∑ x ∈ R, (G.neighborFinset x ∩ E).card) = 32 := by
    calc
      _ = ∑ _x ∈ R, 4 := Finset.sum_congr rfl (fun x hx =>
        hd4 x (hRE hx) (by intro h; subst x; exact huR hx))
      _ = 32 := by simp [hR]
  have hpart : E = insert u (U ∪ R) := by
    ext x
    simp only [R, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hxu : x = u
      · exact Or.inl hxu
      · by_cases hxU : x ∈ U
        · exact Or.inr (Or.inl hxU)
        · exact Or.inr (Or.inr ⟨hx, by simp [hxu, hxU]⟩)
    · rintro (rfl | hxU | hxR)
      · exact hu
      · exact hUE hxU
      · exact hxR.1
  have huUR : u ∉ U ∪ R := by simpa only [Finset.mem_union, not_or] using And.intro huU huR
  have hUR : Disjoint U R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_insert_of_mem hx)
  have hsplit (W : Finset (Fin 49)) :
      (∑ x ∈ W, (G.neighborFinset x ∩ E).card) =
      (G.neighborFinset u ∩ W).card +
      (∑ x ∈ U, (G.neighborFinset x ∩ W).card) +
      ∑ x ∈ R, (G.neighborFinset x ∩ W).card := by
    rw [sum_card_neighbor_inter_comm G W E]
    conv_lhs => rw [hpart, Finset.sum_insert huUR, Finset.sum_union hUR]
    omega
  have huUzero : (G.neighborFinset u ∩ U).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact threeHigh_triple_root_empty_no_special_union_edge G hfree hmin hHigh hone z hz hu huz
      (Finset.mem_inter.mp hx).2 ((G.mem_neighborFinset u x).mp (Finset.mem_inter.mp hx).1)
  have huReq : G.neighborFinset u ∩ R = G.neighborFinset u ∩ E := by
    apply Finset.Subset.antisymm
    · exact Finset.inter_subset_inter_left hRE
    · intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hp.2.2.2.1 hx⟩
  have huRsix : (G.neighborFinset u ∩ R).card = 6 := by
    rw [huReq]
    exact hp.2.2.2.2.1
  have heU := hsplit U
  have heR := hsplit R
  rw [hmassU, huUzero, Nat.zero_add, internal_mass G U,
    ← sum_card_neighbor_inter_comm G U R] at heU
  rw [hmassR, huRsix, internal_mass G R] at heR
  omega

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_union_secondary_edge_ledger
