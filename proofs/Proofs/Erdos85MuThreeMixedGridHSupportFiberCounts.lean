import Proofs.Erdos85MuThreeMixedGridCycleSectorLocalClosure

/-!
# Exact fibers of the occupied H-support

At any occupied `H \ K` cell, both `H`-edges in its row and both `H`-edges
in its column remain occupied.  The corresponding support fibers therefore
have cardinality exactly two.
-/

open SimpleGraph

namespace Erdos85

/-- The occupied cells that are also `H`-edges. -/
def mixedGridHSupport {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K] :
    Finset (muThreeMixedCell K) :=
  Finset.univ.filter fun u => H u.1.1 u.1.2

/-- An occupied `H`-cell lies in an occupied H-support row of size two. -/
theorem MuThreeMixedGridCode.HSupport_row_card_eq_two
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (huH : H u.1.1 u.1.2) :
    ((mixedGridHSupport H K).filter fun v => v.1.1 = u.1.1).card = 2 := by
  let S := (mixedGridHSupport H K).filter fun v => v.1.1 = u.1.1
  let T := (Finset.univ : Finset Y).filter fun y => H u.1.1 y
  have hcard : S.card = T.card := by
    apply Finset.card_bij (fun v _hv => v.1.2)
    · intro v hv
      have hv' := Finset.mem_filter.mp hv
      have hvH := (Finset.mem_filter.mp hv'.1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hv'.2] using hvH⟩
    · intro v hv w hw heq
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hv).2.trans
          (Finset.mem_filter.mp hw).2.symm
      · exact heq
    · intro y hy
      have hyH := (Finset.mem_filter.mp hy).2
      have hyK := code.not_K_of_H_same_row_of_H_cell H K C u huH hyH
      let v : muThreeMixedCell K := ⟨(u.1.1, y), hyK⟩
      refine ⟨v, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hyH⟩, rfl⟩
  change S.card = 2
  rw [hcard]
  exact code.H_twoRegular.1 u.1.1

/-- Column-dual exact support fiber. -/
theorem MuThreeMixedGridCode.HSupport_column_card_eq_two
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (huH : H u.1.1 u.1.2) :
    ((mixedGridHSupport H K).filter fun v => v.1.2 = u.1.2).card = 2 := by
  let S := (mixedGridHSupport H K).filter fun v => v.1.2 = u.1.2
  let T := (Finset.univ : Finset X).filter fun x => H x u.1.2
  have hcard : S.card = T.card := by
    apply Finset.card_bij (fun v _hv => v.1.1)
    · intro v hv
      have hv' := Finset.mem_filter.mp hv
      have hvH := (Finset.mem_filter.mp hv'.1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hv'.2] using hvH⟩
    · intro v hv w hw heq
      apply Subtype.ext
      apply Prod.ext
      · exact heq
      · exact (Finset.mem_filter.mp hv).2.trans
          (Finset.mem_filter.mp hw).2.symm
    · intro x hx
      have hxH := (Finset.mem_filter.mp hx).2
      have hxK := code.not_K_of_H_same_column_of_H_cell H K C u huH hxH
      let v : muThreeMixedCell K := ⟨(x, u.1.2), hxK⟩
      refine ⟨v, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hxH⟩, rfl⟩
  change S.card = 2
  rw [hcard]
  exact code.H_twoRegular.2 u.1.2

/-- After deleting the cell itself, there is exactly one occupied H-support
partner in its row and exactly one in its column.  This is the local
two-factor form of the sector closure. -/
theorem MuThreeMixedGridCode.HSupport_punctured_fiber_cards_eq_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (huH : H u.1.1 u.1.2) :
    ((((mixedGridHSupport H K).filter fun v => v.1.1 = u.1.1).erase u).card = 1) ∧
      ((((mixedGridHSupport H K).filter fun v => v.1.2 = u.1.2).erase u).card = 1) := by
  have huRow : u ∈ (mixedGridHSupport H K).filter fun v => v.1.1 = u.1.1 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, huH⟩, rfl⟩
  have huColumn : u ∈ (mixedGridHSupport H K).filter fun v => v.1.2 = u.1.2 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, huH⟩, rfl⟩
  constructor
  · rw [Finset.card_erase_of_mem huRow,
      code.HSupport_row_card_eq_two H K C u huH]
  · rw [Finset.card_erase_of_mem huColumn,
      code.HSupport_column_card_eq_two H K C u huH]

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.HSupport_row_card_eq_two
#print axioms Erdos85.MuThreeMixedGridCode.HSupport_column_card_eq_two
#print axioms
  Erdos85.MuThreeMixedGridCode.HSupport_punctured_fiber_cards_eq_one
