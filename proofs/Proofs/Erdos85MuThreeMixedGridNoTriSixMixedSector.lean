import Proofs.Erdos85MuThreeMixedGridCommonForeignRowsCard

/-!
# No three-by-three triangle block in a mixed sector

This is the pure hole-counting obstruction behind the mixed `C10 + C6`
exclusion.  If a three-column triangle block has its `H`-edges disjoint from
the hole factor `K`, while every column outside the block is an `H ⊆ K`
triangle-free column, then column two-regularity traps the two `K`-holes of
each triangle row inside the block.  Together with its two disjoint `H`
neighbors this would require four columns inside a three-element set.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A three-column `H \ K` block cannot coexist with `H ⊆ K` on every
outside column.  This is the abstract-code form of “a triangle-sector cycle
has length at least eight in a genuinely mixed sector.” -/
theorem MuThreeMixedGridCode.no_threeColumn_notK_block_of_outside_all_K
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (S : Finset Y) (hScard : S.card = 3) (x : X)
    (hHinside : ∀ y, H x y → y ∈ S)
    (hHnotK : ∀ y, H x y → ¬ K x y)
    (houtside : ∀ y, y ∉ S → ∀ z, H z y → K z y) : False := by
  classical
  have hKinside : ∀ y, K x y → y ∈ S := by
    intro y hKxy
    by_contra hyS
    let A : Finset X := Finset.univ.filter fun z => H z y
    let B : Finset X := Finset.univ.filter fun z => K z y
    have hAB : A ⊆ B := by
      intro z hz
      have hzH : H z y := (Finset.mem_filter.mp hz).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, houtside y hyS z hzH⟩
    have hAcard : A.card = 2 := by
      simpa [A] using code.H_twoRegular.2 y
    have hBcard : B.card = 2 := by
      simpa [B] using code.K_twoRegular.2 y
    have hABeq : A = B :=
      Finset.eq_of_subset_of_card_le hAB (by omega)
    have hxB : x ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hKxy⟩
    have hxA : x ∈ A := hABeq.symm ▸ hxB
    have hxH : H x y := (Finset.mem_filter.mp hxA).2
    exact hHnotK y hxH hKxy
  let RH : Finset Y := Finset.univ.filter fun y => H x y
  let RK : Finset Y := Finset.univ.filter fun y => K x y
  have hRHcard : RH.card = 2 := by
    simpa [RH] using code.H_twoRegular.1 x
  have hRKcard : RK.card = 2 := by
    simpa [RK] using code.K_twoRegular.1 x
  have hRHsub : RH ⊆ S := by
    intro y hy
    exact hHinside y (Finset.mem_filter.mp hy).2
  have hRKsub : RK ⊆ S := by
    intro y hy
    exact hKinside y (Finset.mem_filter.mp hy).2
  have hdisj : Disjoint RH RK := by
    rw [Finset.disjoint_left]
    intro y hyH hyK
    exact hHnotK y (Finset.mem_filter.mp hyH).2
      (Finset.mem_filter.mp hyK).2
  have hunionSub : RH ∪ RK ⊆ S := Finset.union_subset hRHsub hRKsub
  have hunionCard : (RH ∪ RK).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj, hRHcard, hRKcard]
  have hle := Finset.card_le_card hunionSub
  rw [hunionCard, hScard] at hle
  omega

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.no_threeColumn_notK_block_of_outside_all_K
