import Proofs.Erdos85SevenRegularNearTwinNeighborhoods

/-! # Codegree-five near-twin-lite neighborhoods

The near-twin-free order-sixty-four component models still frequently contain
nonedges sharing five of their seven defect neighbors.  Such a pair has two
private neighbors on each side and a four-element symmetric difference.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Seven-regular vertices with five common neighbors have exactly two
private neighbors on each side. -/
theorem sevenRegular_codegreeFive_sdiff_cards
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ z, H.degree z = 7) {x y : V}
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 5) :
    (H.neighborFinset x \ H.neighborFinset y).card = 2 ∧
      (H.neighborFinset y \ H.neighborFinset x).card = 2 := by
  have hx := Finset.card_sdiff_add_card_inter
    (H.neighborFinset x) (H.neighborFinset y)
  have hy := Finset.card_sdiff_add_card_inter
    (H.neighborFinset y) (H.neighborFinset x)
  rw [H.card_neighborFinset_eq_degree, hreg x, hcommon] at hx
  rw [H.card_neighborFinset_eq_degree, hreg y,
    Finset.inter_comm, hcommon] at hy
  omega

/-- The two neighborhoods have symmetric difference four. -/
theorem sevenRegular_codegreeFive_symmDiff_card_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ z, H.degree z = 7) {x y : V}
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 5) :
    ((H.neighborFinset x \ H.neighborFinset y) ∪
      (H.neighborFinset y \ H.neighborFinset x)).card = 4 := by
  have hcards := sevenRegular_codegreeFive_sdiff_cards H hreg hcommon
  rw [Finset.card_union_of_disjoint]
  · omega
  · rw [Finset.disjoint_left]
    intro z hzx hzy
    exact (Finset.mem_sdiff.mp hzx).2 (Finset.mem_sdiff.mp hzy).1

/-- Exact normal form with two private-neighbor pairs. -/
theorem sevenRegular_codegreeFive_neighborFinset_normalForm
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hreg : ∀ z, H.degree z = 7) {x y : V}
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 5) :
    ∃ A B : Finset V,
      A.card = 2 ∧ B.card = 2 ∧ Disjoint A B ∧
      H.neighborFinset x = A ∪
        (H.neighborFinset x ∩ H.neighborFinset y) ∧
      H.neighborFinset y = B ∪
        (H.neighborFinset x ∩ H.neighborFinset y) := by
  let A := H.neighborFinset x \ H.neighborFinset y
  let B := H.neighborFinset y \ H.neighborFinset x
  have hcards := sevenRegular_codegreeFive_sdiff_cards H hreg hcommon
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    exact (Finset.mem_sdiff.mp hzA).2 (Finset.mem_sdiff.mp hzB).1
  refine ⟨A, B, hcards.1, hcards.2, hdis, ?_, ?_⟩
  · exact (Finset.sdiff_union_inter
      (H.neighborFinset x) (H.neighborFinset y)).symm
  · simpa [Finset.inter_comm] using
      (Finset.sdiff_union_inter
        (H.neighborFinset y) (H.neighborFinset x)).symm

/-- A nonadjacent codegree-five pair on sixteen vertices leaves five exterior
vertices, equivalently five common neighbors in the complement. -/
theorem sevenRegular_codegreeFive_compl_codegree_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : Fintype.card V = 16) (hreg : ∀ z, H.degree z = 7)
    {x y : V} (hxy : x ≠ y) (hnot : ¬ H.Adj x y)
    (hcommon : (H.neighborFinset x ∩ H.neighborFinset y).card = 5) :
    (Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y).card = 5 := by
  let N := H.neighborFinset x ∪ H.neighborFinset y
  have hNcard : N.card = 9 := by
    have hsum := Finset.card_union_add_card_inter
      (H.neighborFinset x) (H.neighborFinset y)
    change N.card +
      (H.neighborFinset x ∩ H.neighborFinset y).card =
        (H.neighborFinset x).card + (H.neighborFinset y).card at hsum
    rw [H.card_neighborFinset_eq_degree, hreg x,
      H.card_neighborFinset_eq_degree, hreg y, hcommon] at hsum
    omega
  have hxN : x ∉ N := by
    simp only [N, Finset.mem_union, H.mem_neighborFinset]
    rintro (hxx | hyx)
    · exact H.loopless.irrefl x hxx
    · exact hnot hyx.symm
  have hyN : y ∉ N := by
    simp only [N, Finset.mem_union, H.mem_neighborFinset]
    rintro (hxy' | hyy)
    · exact hnot hxy'
    · exact H.loopless.irrefl y hyy
  have hxclosed : x ∉ insert y N := by simp [hxy, hxN]
  have hclosed : (insert x (insert y N)).card = 11 := by
    rw [Finset.card_insert_of_notMem hxclosed,
      Finset.card_insert_of_notMem hyN, hNcard]
  rw [← nearTwinExteriorFinset_eq_compl_common H x y,
    nearTwinExteriorFinset,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    hcard, hclosed]

/-- For a nonadjacent pair, the complement neighborhood of `x` splits into
`y`, the common complement core, and the neighbors private to `y` in the
original graph. -/
theorem compl_neighborFinset_eq_insert_complCommon_union_reversePrivate
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {x y : V} (hxy : x ≠ y) (hnot : ¬ H.Adj x y) :
    Hᶜ.neighborFinset x = insert y
      ((Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y) ∪
        (H.neighborFinset y \ H.neighborFinset x)) := by
  ext z
  simp only [SimpleGraph.mem_neighborFinset, compl_adj,
    Finset.mem_insert, Finset.mem_union, Finset.mem_inter,
    Finset.mem_sdiff]
  constructor
  · rintro ⟨hxz, hnotxz⟩
    by_cases hzy : z = y
    · exact Or.inl hzy
    by_cases hyz : H.Adj y z
    · exact Or.inr (Or.inr ⟨hyz, hnotxz⟩)
    · exact Or.inr (Or.inl ⟨⟨hxz, hnotxz⟩, Ne.symm hzy, hyz⟩)
  · rintro (hzy | hcommon | hprivate)
    · subst z
      exact ⟨hxy, hnot⟩
    · exact hcommon.1
    · have hxz : x ≠ z := by
        intro hxz
        subst z
        exact hnot hprivate.1.symm
      exact ⟨hxz, hprivate.2⟩

/-- Symmetric version at `y`. -/
theorem compl_neighborFinset_eq_insert_complCommon_union_forwardPrivate
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {x y : V} (hxy : x ≠ y) (hnot : ¬ H.Adj x y) :
    Hᶜ.neighborFinset y = insert x
      ((Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y) ∪
        (H.neighborFinset x \ H.neighborFinset y)) := by
  have h := compl_neighborFinset_eq_insert_complCommon_union_reversePrivate
    H (x := y) (y := x) hxy.symm (fun h => hnot h.symm)
  simpa only [Finset.inter_comm] using h

end

end Erdos85
