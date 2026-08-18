import Proofs.Erdos85MuThreeMixedGridColumnRowEquiv
import Proofs.Erdos85MuThreeMixedGridPerCellColumnMates

/-!
# The mixed-grid K-symmetry law

Exterior adjacency gives a bijection between the occupied cells of row `x`
whose columns are foreign to row `x'` and the corresponding cells with the
two rows reversed.  Since every row has six occupied cells, their complementary
`H`-incidence counts agree.  The column statement is dual.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def mixedGridForeignOccupiedRow
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (x x' : X) :=
  {u : mixedGridOccupiedRow K x // ¬ H x' u.1.1.2}

/-- Exterior adjacency matches the foreign occupied parts of two rows. -/
noncomputable def mixedGridForeignOccupiedRowEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (x x' : X) :
    mixedGridForeignOccupiedRow H K x x' ≃
      mixedGridForeignOccupiedRow H K x' x where
  toFun u :=
    ⟨⟨mixedGridRowRoute H K C code u.1.1 x' u.2,
      mixedGridRowRoute_row H K C code u.1.1 x' u.2⟩,
      by simpa [u.1.2] using
        (mixedGridRowRoute_back_allowed H K C code u.1.1 x' u.2)⟩
  invFun v :=
    ⟨⟨mixedGridRowRoute H K C code v.1.1 x v.2,
      mixedGridRowRoute_row H K C code v.1.1 x v.2⟩,
      by simpa [v.1.2] using
        (mixedGridRowRoute_back_allowed H K C code v.1.1 x v.2)⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [u.1.2] using
      (mixedGridRowRoute_inverse H K C code u.1.1 x' u.2)
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [v.1.2] using
      (mixedGridRowRoute_inverse H K C code v.1.1 x v.2)

/-- Coordinate presentation of the `H`-incident occupied cells in a row. -/
def mixedGridHOccupiedRowEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (x x' : X) :
    {y : Y // H x' y ∧ ¬ K x y} ≃
      {u : mixedGridOccupiedRow K x // H x' u.1.1.2} where
  toFun y := ⟨⟨⟨(x, y.1), y.2.2⟩, rfl⟩, y.2.1⟩
  invFun u := ⟨u.1.1.1.2, u.2, by simpa [u.1.2] using u.1.1.2⟩
  left_inv y := by ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext u.1.2.symm rfl

/-- **Row K-symmetry.**  Swapping two rows preserves the number of occupied
columns that are `H`-incident to the other row. -/
theorem MuThreeMixedGridCode.card_H_and_not_K_row_symm
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (x x' : X) :
    Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
      Fintype.card {y : Y // H x y ∧ ¬ K x' y} := by
  let A := Fintype.card {u : mixedGridOccupiedRow K x // H x' u.1.1.2}
  let B := Fintype.card {u : mixedGridOccupiedRow K x' // H x u.1.1.2}
  have hforeign :
      Fintype.card {u : mixedGridOccupiedRow K x // ¬ H x' u.1.1.2} =
        Fintype.card {u : mixedGridOccupiedRow K x' // ¬ H x u.1.1.2} :=
    Fintype.card_congr (mixedGridForeignOccupiedRowEquiv H K C code x x')
  have hleft : 6 - A =
      Fintype.card {u : mixedGridOccupiedRow K x // ¬ H x' u.1.1.2} := by
    rw [Fintype.card_subtype_compl]
    simp only [A]
    rw [code.card_occupiedRow_eq_six H K C x]
  have hright : 6 - B =
      Fintype.card {u : mixedGridOccupiedRow K x' // ¬ H x u.1.1.2} := by
    rw [Fintype.card_subtype_compl]
    simp only [B]
    rw [code.card_occupiedRow_eq_six H K C x']
  have hAle : A ≤ 6 := by
    simpa [A, code.card_occupiedRow_eq_six H K C x] using
      (Fintype.card_subtype_le (fun u : mixedGridOccupiedRow K x => H x' u.1.1.2))
  have hBle : B ≤ 6 := by
    simpa [B, code.card_occupiedRow_eq_six H K C x'] using
      (Fintype.card_subtype_le (fun u : mixedGridOccupiedRow K x' => H x u.1.1.2))
  have hAB : A = B := by omega
  rw [Fintype.card_congr (mixedGridHOccupiedRowEquiv H K x x'),
    Fintype.card_congr (mixedGridHOccupiedRowEquiv H K x' x)]
  exact hAB

def mixedGridForeignOccupiedColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (y y' : Y) :=
  {u : mixedGridOccupiedColumn K y // ¬ H u.1.1.1 y'}

/-- The reverse column route is allowed.  This is the column dual of
`mixedGridRowRoute_back_allowed`. -/
theorem mixedGridColumnRoute_back_allowed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) (hy : ¬ H u.1.1 y) :
    let v := mixedGridColumnRoute H K C code u y hy
    ¬ H v.1.1 u.1.2 := by
  dsimp
  rw [← MuThreeMixedGridCode.existsUnique_column_neighbor_iff H K C code]
  refine ⟨u, ⟨C.adj_symm (mixedGridColumnRoute_spec H K C code u y hy).1,
    rfl⟩, ?_⟩
  intro w hw
  by_contra hwu
  have hsep := code.rook (mixedGridColumnRoute H K C code u y hy) u w
    (C.adj_symm (mixedGridColumnRoute_spec H K C code u y hy).1)
    hw.1 (Ne.symm hwu)
  exact hsep.2 hw.2.symm

/-- Routing back to the source column returns the source cell. -/
theorem mixedGridColumnRoute_inverse
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) (hy : ¬ H u.1.1 y) :
    let v := mixedGridColumnRoute H K C code u y hy
    mixedGridColumnRoute H K C code v u.1.2
      (mixedGridColumnRoute_back_allowed H K C code u y hy) = u := by
  dsimp
  apply mixedGridColumnRoute_eq_of_adj_of_column H K C code
  · exact C.adj_symm (mixedGridColumnRoute_spec H K C code u y hy).1
  · rfl

/-- Exterior adjacency matches the foreign occupied parts of two columns. -/
noncomputable def mixedGridForeignOccupiedColumnEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y y' : Y) :
    mixedGridForeignOccupiedColumn H K y y' ≃
      mixedGridForeignOccupiedColumn H K y' y where
  toFun u :=
    ⟨⟨mixedGridColumnRoute H K C code u.1.1 y' u.2,
      (mixedGridColumnRoute_spec H K C code u.1.1 y' u.2).2⟩,
      by simpa [u.1.2] using
        (mixedGridColumnRoute_back_allowed H K C code u.1.1 y' u.2)⟩
  invFun v :=
    ⟨⟨mixedGridColumnRoute H K C code v.1.1 y v.2,
      (mixedGridColumnRoute_spec H K C code v.1.1 y v.2).2⟩,
      by simpa [v.1.2] using
        (mixedGridColumnRoute_back_allowed H K C code v.1.1 y v.2)⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [u.1.2] using
      (mixedGridColumnRoute_inverse H K C code u.1.1 y' u.2)
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [v.1.2] using
      (mixedGridColumnRoute_inverse H K C code v.1.1 y v.2)

/-- Coordinate presentation of the `H`-incident occupied cells in a column. -/
def mixedGridHOccupiedColumnEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (y y' : Y) :
    {x : X // H x y' ∧ ¬ K x y} ≃
      {u : mixedGridOccupiedColumn K y // H u.1.1.1 y'} where
  toFun x := ⟨⟨⟨(x.1, y), x.2.2⟩, rfl⟩, x.2.1⟩
  invFun u := ⟨u.1.1.1.1, u.2, by simpa [u.1.2] using u.1.1.2⟩
  left_inv x := by ext; rfl
  right_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl u.1.2.symm

/-- **Column K-symmetry.**  Swapping two columns preserves the number of
occupied rows that are `H`-incident to the other column. -/
theorem MuThreeMixedGridCode.card_H_and_not_K_column_symm
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y y' : Y) :
    Fintype.card {x : X // H x y' ∧ ¬ K x y} =
      Fintype.card {x : X // H x y ∧ ¬ K x y'} := by
  let A := Fintype.card {u : mixedGridOccupiedColumn K y // H u.1.1.1 y'}
  let B := Fintype.card {u : mixedGridOccupiedColumn K y' // H u.1.1.1 y}
  have hforeign :
      Fintype.card {u : mixedGridOccupiedColumn K y // ¬ H u.1.1.1 y'} =
        Fintype.card {u : mixedGridOccupiedColumn K y' // ¬ H u.1.1.1 y} :=
    Fintype.card_congr (mixedGridForeignOccupiedColumnEquiv H K C code y y')
  have hleft : 6 - A =
      Fintype.card {u : mixedGridOccupiedColumn K y // ¬ H u.1.1.1 y'} := by
    rw [Fintype.card_subtype_compl]
    simp only [A]
    rw [code.card_occupiedColumn_eq_six H K C y]
  have hright : 6 - B =
      Fintype.card {u : mixedGridOccupiedColumn K y' // ¬ H u.1.1.1 y} := by
    rw [Fintype.card_subtype_compl]
    simp only [B]
    rw [code.card_occupiedColumn_eq_six H K C y']
  have hAle : A ≤ 6 := by
    simpa [A, code.card_occupiedColumn_eq_six H K C y] using
      (Fintype.card_subtype_le
        (fun u : mixedGridOccupiedColumn K y => H u.1.1.1 y'))
  have hBle : B ≤ 6 := by
    simpa [B, code.card_occupiedColumn_eq_six H K C y'] using
      (Fintype.card_subtype_le
        (fun u : mixedGridOccupiedColumn K y' => H u.1.1.1 y))
  have hAB : A = B := by omega
  rw [Fintype.card_congr (mixedGridHOccupiedColumnEquiv H K y y'),
    Fintype.card_congr (mixedGridHOccupiedColumnEquiv H K y' y)]
  exact hAB

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.card_H_and_not_K_row_symm
#print axioms Erdos85.MuThreeMixedGridCode.card_H_and_not_K_column_symm
