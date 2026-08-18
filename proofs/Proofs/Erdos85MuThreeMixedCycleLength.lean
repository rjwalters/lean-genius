import Proofs.Erdos85MuThreeMixedGridCode

/-!
# Mixed-sector cycle length

In a mixed pair of `H`-components, a triangle-bearing component must contain
at least four vertices on either shore: its two `H` neighbours and two `K`
holes are disjoint, while a triangle-free component's columns are already
saturated by their two `H = K` edges.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def relationComponentRightFiber
    {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (H : X → Y → Prop)
    [DecidableEq (relationBipartiteGraph H).ConnectedComponent]
    (c : (relationBipartiteGraph H).ConnectedComponent) : Finset Y :=
  Finset.univ.filter fun y =>
    (relationBipartiteGraph H).connectedComponentMk (Sum.inr y) = c

/-- If two `H`-components cover the right shore, one is `H`-disjoint from
`K`, and the other has all of its `H`-edges in `K`, then the former has at
least four right-shore vertices.  This is the abstract hole-counting core of
the exclusion of a triangle-bearing `C6` in a mixed sector. -/
theorem relationFactor_mixed_triComponent_rightFiber_card_ge_four
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    [DecidableEq (relationBipartiteGraph H).ConnectedComponent]
    (hH : RelationTwoRegular H) (hK : RelationTwoRegular K)
    (ctri ctf : (relationBipartiteGraph H).ConnectedComponent)
    (hneq : ctri ≠ ctf)
    (hcover : ∀ y : Y, Sum.inr y ∈ ctri.supp ∨ Sum.inr y ∈ ctf.supp)
    (htri : ∀ x y, H x y → Sum.inl x ∈ ctri.supp → ¬ K x y)
    (htf : ∀ x y, H x y → Sum.inl x ∈ ctf.supp → K x y)
    {x : X} (hx : Sum.inl x ∈ ctri.supp) :
    4 ≤ (relationComponentRightFiber H ctri).card := by
  let HF : Finset Y := Finset.univ.filter fun y => H x y
  let KF : Finset Y := Finset.univ.filter fun y => K x y
  let RF : Finset Y := relationComponentRightFiber H ctri
  have hHcard : HF.card = 2 := by simpa [HF] using hH.1 x
  have hKcard : KF.card = 2 := by simpa [KF] using hK.1 x
  have hHKdisj : Disjoint HF KF := by
    rw [Finset.disjoint_left]
    intro y hyH hyK
    exact htri x y (Finset.mem_filter.mp hyH).2 hx
      (Finset.mem_filter.mp hyK).2
  have hHsub : HF ⊆ RF := by
    intro y hy
    have hxy : H x y := (Finset.mem_filter.mp hy).2
    have hadj : (relationBipartiteGraph H).Adj (Sum.inl x) (Sum.inr y) := hxy
    have hyc : Sum.inr y ∈ ctri.supp := by
      rw [ConnectedComponent.mem_supp_iff] at hx ⊢
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm.trans hx
    rw [ConnectedComponent.mem_supp_iff] at hyc
    have hyRF : y ∈ relationComponentRightFiber H ctri :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ y, hyc⟩
    simpa [RF] using hyRF
  have hKsub : KF ⊆ RF := by
    intro y hy
    have hxyK : K x y := (Finset.mem_filter.mp hy).2
    rcases hcover y with hytri | hytf
    · rw [ConnectedComponent.mem_supp_iff] at hytri
      have hyRF : y ∈ relationComponentRightFiber H ctri :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ y, hytri⟩
      simpa [RF] using hyRF
    · exfalso
      let Hy : Finset X := Finset.univ.filter fun z => H z y
      let Ky : Finset X := Finset.univ.filter fun z => K z y
      have hHycard : Hy.card = 2 := by simpa [Hy] using hH.2 y
      have hKycard : Ky.card = 2 := by simpa [Ky] using hK.2 y
      have hHySub : Hy ⊆ Ky := by
        intro z hz
        have hzy : H z y := (Finset.mem_filter.mp hz).2
        have hadj : (relationBipartiteGraph H).Adj (Sum.inl z) (Sum.inr y) := hzy
        have hzTf : Sum.inl z ∈ ctf.supp := by
          rw [ConnectedComponent.mem_supp_iff] at hytf ⊢
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hytf
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, htf z y hzy hzTf⟩
      have hHyKy : Hy = Ky :=
        Finset.eq_of_subset_of_card_le hHySub (by omega)
      have hxHy : x ∈ Hy := by
        rw [hHyKy]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxyK⟩
      have hxyH : H x y := (Finset.mem_filter.mp hxHy).2
      have hadj : (relationBipartiteGraph H).Adj (Sum.inl x) (Sum.inr y) := hxyH
      have hxTf : Sum.inl x ∈ ctf.supp := by
        rw [ConnectedComponent.mem_supp_iff] at hytf ⊢
        exact (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hytf
      rw [ConnectedComponent.mem_supp_iff] at hx hxTf
      exact hneq (hx.symm.trans hxTf)
  have hunionSub : HF ∪ KF ⊆ RF := Finset.union_subset hHsub hKsub
  have hunionCard : (HF ∪ KF).card = 4 := by
    rw [Finset.card_union_of_disjoint hHKdisj, hHcard, hKcard]
  have := Finset.card_le_card hunionSub
  simpa [RF, hunionCard] using this

end


end Erdos85

#print axioms Erdos85.relationFactor_mixed_triComponent_rightFiber_card_ge_four
