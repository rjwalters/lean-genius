import Proofs.Erdos85MuThreeAllTrianglePartnerStep

/-!
# Four-cell row and column fibers of the partner support

When the two 2-factors `H` and `K` are edge-disjoint, every row and column
has two `H`-cells, two forbidden `K`-cells, and four remaining partner cells.
Row mate restricts to a fixed-point-free involution of each four-cell row
fiber, and column mate does the same on each column fiber.
-/

open SimpleGraph

namespace Erdos85

/-- Non-`H` occupied cells in one row. -/
def mixedGridNonHRow
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (x : X) : Finset (mixedGridNonHCell H K) :=
  Finset.univ.filter fun u => u.1.1.1 = x

/-- Non-`H` occupied cells in one column. -/
def mixedGridNonHColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (y : Y) : Finset (mixedGridNonHCell H K) :=
  Finset.univ.filter fun u => u.1.1.2 = y

private theorem card_complement_two_disjoint_two_eq_four
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (P Q : Z → Prop) [DecidablePred P] [DecidablePred Q]
    (hcard : Fintype.card Z = 8)
    (hP : ((Finset.univ : Finset Z).filter P).card = 2)
    (hQ : ((Finset.univ : Finset Z).filter Q).card = 2)
    (hdisjoint : ∀ z, P z → ¬ Q z) :
    ((Finset.univ : Finset Z).filter fun z => ¬ P z ∧ ¬ Q z).card = 4 := by
  classical
  let S := (Finset.univ : Finset Z).filter P
  let T := (Finset.univ : Finset Z).filter Q
  let U := (Finset.univ : Finset Z).filter fun z => ¬ P z ∧ ¬ Q z
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    exact hdisjoint z (Finset.mem_filter.mp hzS).2 (Finset.mem_filter.mp hzT).2
  have hcover : S ∪ T ∪ U = Finset.univ := by
    ext z
    simp only [S, T, U, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  have hUdis : Disjoint (S ∪ T) U := by
    rw [Finset.disjoint_left]
    intro z hzST hzU
    rcases Finset.mem_union.mp hzST with hzS | hzT
    · exact (Finset.mem_filter.mp hzU).2.1 (Finset.mem_filter.mp hzS).2
    · exact (Finset.mem_filter.mp hzU).2.2 (Finset.mem_filter.mp hzT).2
  have htotal := congrArg Finset.card hcover
  rw [Finset.card_union_of_disjoint hUdis,
    Finset.card_union_of_disjoint hST] at htotal
  simp only [Finset.card_univ, hcard] at htotal
  change S.card = 2 at hP
  change T.card = 2 at hQ
  change U.card = 4
  omega

/-- Every row has four non-`H` occupied cells. -/
theorem MuThreeMixedGridCode.card_nonHRow_eq_four
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) (x : X) :
    (mixedGridNonHRow H K x).card = 4 := by
  classical
  let T := (Finset.univ : Finset Y).filter fun y => ¬ K x y ∧ ¬ H x y
  have hT : T.card = 4 := by
    apply card_complement_two_disjoint_two_eq_four
      (fun y => K x y) (fun y => H x y) code.card_right
      (code.K_twoRegular.1 x) (code.H_twoRegular.1 x)
    intro y hK hH
    exact hdisjoint x y hH hK
  apply Eq.trans (Finset.card_bij (fun u _hu => u.1.1.2)
    (by
      intro u hu
      have hrow := (Finset.mem_filter.mp hu).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        constructor
        · simpa [hrow] using u.1.2
        · simpa [hrow] using u.2⟩)
    (by
      intro u hu v hv heq
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext ((Finset.mem_filter.mp hu).2.trans
        (Finset.mem_filter.mp hv).2.symm) heq)
    (by
      intro y hy
      have hy' := (Finset.mem_filter.mp hy).2
      let u : mixedGridNonHCell H K := ⟨⟨(x, y), hy'.1⟩, hy'.2⟩
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩)) hT

/-- Every column has four non-`H` occupied cells. -/
theorem MuThreeMixedGridCode.card_nonHColumn_eq_four
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) (y : Y) :
    (mixedGridNonHColumn H K y).card = 4 := by
  classical
  let T := (Finset.univ : Finset X).filter fun x => ¬ K x y ∧ ¬ H x y
  have hT : T.card = 4 := by
    apply card_complement_two_disjoint_two_eq_four
      (fun x => K x y) (fun x => H x y) code.card_left
      (code.K_twoRegular.2 y) (code.H_twoRegular.2 y)
    intro x hK hH
    exact hdisjoint x y hH hK
  apply Eq.trans (Finset.card_bij (fun u _hu => u.1.1.1)
    (by
      intro u hu
      have hcol := (Finset.mem_filter.mp hu).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        constructor
        · simpa [hcol] using u.1.2
        · simpa [hcol] using u.2⟩)
    (by
      intro u hu v hv heq
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext heq ((Finset.mem_filter.mp hu).2.trans
        (Finset.mem_filter.mp hv).2.symm))
    (by
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      let u : mixedGridNonHCell H K := ⟨⟨(x, y), hx'.1⟩, hx'.2⟩
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩)) hT

/-- Row mate stays in the same four-cell row fiber. -/
theorem MuThreeMixedGridCode.rowMate_mem_nonHRow
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : mixedGridNonHCell H K) :
    code.rowMate H K C u ∈ mixedGridNonHRow H K u.1.1.1 := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (code.rowMate_adj H K C u).2.symm⟩

/-- Column mate stays in the same four-cell column fiber. -/
theorem MuThreeMixedGridCode.columnMate_mem_nonHColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : mixedGridNonHCell H K) :
    code.columnMate H K C u ∈ mixedGridNonHColumn H K u.1.1.2 := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (code.columnMate_adj H K C u).2.symm⟩

/-- Row mate restricted to one four-cell row fiber. -/
noncomputable def MuThreeMixedGridCode.rowMateFiberEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (x : X) :
    (↥(mixedGridNonHRow H K x)) ≃ (↥(mixedGridNonHRow H K x)) where
  toFun u := ⟨code.rowMate H K C u.1, by
    have hm := code.rowMate_mem_nonHRow H K C u.1
    have hx := (Finset.mem_filter.mp u.2).2
    simpa [hx] using hm⟩
  invFun u := ⟨code.rowMate H K C u.1, by
    have hm := code.rowMate_mem_nonHRow H K C u.1
    have hx := (Finset.mem_filter.mp u.2).2
    simpa [hx] using hm⟩
  left_inv u := by
    apply Subtype.ext
    exact code.rowMate_rowMate H K C u.1
  right_inv u := by
    apply Subtype.ext
    exact code.rowMate_rowMate H K C u.1

/-- Column mate restricted to one four-cell column fiber. -/
noncomputable def MuThreeMixedGridCode.columnMateFiberEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y : Y) :
    (↥(mixedGridNonHColumn H K y)) ≃ (↥(mixedGridNonHColumn H K y)) where
  toFun u := ⟨code.columnMate H K C u.1, by
    have hm := code.columnMate_mem_nonHColumn H K C u.1
    have hy := (Finset.mem_filter.mp u.2).2
    simpa [hy] using hm⟩
  invFun u := ⟨code.columnMate H K C u.1, by
    have hm := code.columnMate_mem_nonHColumn H K C u.1
    have hy := (Finset.mem_filter.mp u.2).2
    simpa [hy] using hm⟩
  left_inv u := by
    apply Subtype.ext
    exact code.columnMate_columnMate H K C u.1
  right_inv u := by
    apply Subtype.ext
    exact code.columnMate_columnMate H K C u.1

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.card_nonHRow_eq_four
#print axioms Erdos85.MuThreeMixedGridCode.card_nonHColumn_eq_four
#print axioms Erdos85.MuThreeMixedGridCode.rowMate_mem_nonHRow
#print axioms Erdos85.MuThreeMixedGridCode.columnMate_mem_nonHColumn
#print axioms Erdos85.MuThreeMixedGridCode.rowMateFiberEquiv
#print axioms Erdos85.MuThreeMixedGridCode.columnMateFiberEquiv
