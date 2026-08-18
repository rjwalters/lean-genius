import Proofs.Erdos85OrderSixtyFourPairPartition

/-! # The two-regular own-pair correction -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For an exterior pair in a two-regular induced block, deleting the pair
from the union of its two internal neighbourhoods and then subtracting two
gives zero for an internal edge and two for an internal nonedge.  The latter
case uses C4-freeness: an exterior pair cannot simultaneously have an internal
common neighbour. -/
theorem exteriorPair_twoRegular_neighborUnion_sdiff_card_sub_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : Set V)
    [DecidablePred (· ∈ s)]
    (hdeg : ∀ x : s, (G.induce s).degree x = 2)
    (z z' : s) (hzz' : z ≠ z')
    (hE : (exteriorPairGraph G s).Adj z z') :
    ((((G.induce s).neighborFinset z ∪
        (G.induce s).neighborFinset z') \ {z, z'}).card - 2) =
      if (G.induce s).Adj z z' then 0 else 2 := by
  let H := G.induce s
  let A := H.neighborFinset z ∪ H.neighborFinset z'
  let P : Finset s := {z, z'}
  have hzcard : (H.neighborFinset z).card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hdeg]
  have hz'card : (H.neighborFinset z').card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hdeg]
  have hAcard_le : A.card ≤ 4 := by
    calc
      A.card ≤ (H.neighborFinset z).card +
          (H.neighborFinset z').card := Finset.card_union_le _ _
      _ = 4 := by omega
  by_cases hadj : H.Adj z z'
  · rw [if_pos hadj]
    have hPsub : P ⊆ A := by
      intro x hx
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_union_right _
          ((H.mem_neighborFinset _ _).mpr hadj.symm)
      · exact Finset.mem_union_left _
          ((H.mem_neighborFinset _ _).mpr hadj)
    have hPcard : P.card = 2 := by simp [P, hzz']
    have hsdiff : (A \ P).card = A.card - P.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hPsub]
    change (A \ P).card - 2 = 0
    omega
  · rw [if_neg hadj]
    have hinter : H.neighborFinset z ∩ H.neighborFinset z' = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hI : ∃ x : s, H.Adj z x ∧ H.Adj z' x := by
        refine ⟨x, ?_, ?_⟩
        · exact (H.mem_neighborFinset z x).mp (Finset.mem_inter.mp hx).1
        · exact (H.mem_neighborFinset z' x).mp (Finset.mem_inter.mp hx).2
      exact (not_internalCommon_and_exteriorPair G hfree s z z' hzz')
        ⟨hI, hE⟩
    have hAcard : A.card = 4 := by
      have hdisjN : Disjoint (H.neighborFinset z) (H.neighborFinset z') :=
        Finset.disjoint_iff_inter_eq_empty.mpr hinter
      change A.card = 4
      rw [Finset.card_union_of_disjoint hdisjN, hzcard, hz'card]
    have hdisj : Disjoint A P := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxP
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hxP
      rcases hxP with rfl | rfl
      · simp only [A, Finset.mem_union, H.mem_neighborFinset] at hxA
        rcases hxA with hloop | hback
        · exact H.irrefl hloop
        · exact hadj hback.symm
      · simp only [A, Finset.mem_union, H.mem_neighborFinset] at hxA
        rcases hxA with hforw | hloop
        · exact hadj hforw
        · exact H.irrefl hloop
    have hinterPA : P ∩ A = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdisj.symm
    change (A \ P).card - 2 = 2
    rw [Finset.card_sdiff, hinterPA, Finset.card_empty, Nat.sub_zero, hAcard]

#print axioms Erdos85.exteriorPair_twoRegular_neighborUnion_sdiff_card_sub_two

end

end Erdos85
