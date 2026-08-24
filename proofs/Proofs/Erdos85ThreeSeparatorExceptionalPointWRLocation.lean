import Proofs.Erdos85ThreeSeparatorExceptionalPointWCrossMatching

/-! # R-location on the separator-exceptional branch -/

open Finset SimpleGraph

namespace Erdos85

/-- On a two-point set, a zero-one internal-degree profile is uniform: both
points are selected or neither is. -/
theorem twoSet_indicator_internalDegree_uniform
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S R : Finset V) (hScard : S.card = 2)
    (hprofile : ∀ x ∈ S,
      (G.neighborFinset x ∩ S).card = if x ∈ R then 1 else 0) :
    R ∩ S = ∅ ∨ R ∩ S = S := by
  by_cases hempty : R ∩ S = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨x, hxRS⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hxR := (Finset.mem_inter.mp hxRS).1
    have hxS := (Finset.mem_inter.mp hxRS).2
    apply Finset.Subset.antisymm Finset.inter_subset_right
    intro y hyS
    apply Finset.mem_inter.mpr
    refine ⟨?_, hyS⟩
    by_cases hyx : y = x
    · simpa [hyx] using hxR
    · have hNxCard : (G.neighborFinset x ∩ S).card = 1 := by
        simpa [hxR] using hprofile x hxS
      have hsub : G.neighborFinset x ∩ S ⊆ S.erase x := by
        intro z hz
        have hz' := Finset.mem_inter.mp hz
        exact Finset.mem_erase.mpr
          ⟨G.ne_of_adj ((G.mem_neighborFinset x z).mp hz'.1).symm, hz'.2⟩
      have heraseCard : (S.erase x).card = 1 := by
        rw [Finset.card_erase_of_mem hxS, hScard]
      have heq : G.neighborFinset x ∩ S = S.erase x :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hNxCard, heraseCard])
      have hyN : y ∈ G.neighborFinset x := by
        have : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hyx, hyS⟩
        rw [← heq] at this
        exact (Finset.mem_inter.mp this).1
      have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hyN
      by_contra hyR
      have hyZero : (G.neighborFinset y ∩ S).card = 0 := by
        simpa [hyR] using hprofile y hyS
      have hxmem : x ∈ G.neighborFinset y ∩ S := by
        exact Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset y x).mpr ((G.adj_comm x y).mp hxy), hxS⟩
      rw [Finset.card_eq_zero.mp hyZero] at hxmem
      simp at hxmem

/-- B17W''': the positive-spike W-profile places either neither or both of
the nonexceptional separator points in R. -/
theorem exceptionalPoint_W_R_location_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W R : Finset V) (c : V)
    (hWcard : W.card = 3) (hcW : c ∈ W) (hcR : c ∉ R)
    (hprofile : ∀ w ∈ W.erase c,
      (G.neighborFinset w ∩ (W.erase c)).card = if w ∈ R then 1 else 0) :
    R ∩ W = ∅ ∨ R ∩ W = W.erase c := by
  have hScard : (W.erase c).card = 2 := by
    rw [Finset.card_erase_of_mem hcW, hWcard]
  have hcases := twoSet_indicator_internalDegree_uniform
    G (W.erase c) R hScard hprofile
  have hinter : R ∩ W = R ∩ (W.erase c) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · intro hz
      exact ⟨hz.1, ⟨by rintro rfl; exact hcR hz.1, hz.2⟩⟩
    · intro hz
      exact ⟨hz.1, hz.2.2⟩
  rw [hinter]
  exact hcases

#print axioms twoSet_indicator_internalDegree_uniform
#print axioms exceptionalPoint_W_R_location_cases

end Erdos85
