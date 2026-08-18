import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromySignCoboundary

/-!
# Common eligible-row cardinality

For two columns in the eight-by-eight mixed grid, inclusion-exclusion and
two-regularity give an exact formula: the number of rows avoiding both
columns in `H` is four plus the number of their common `H`-neighbors.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact common-eligible-row formula for two columns. -/
theorem MuThreeMixedGridCode.card_commonForeignRows_eq_four_add_common
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (b b' : Y) :
    Fintype.card (commonForeignRows H b b') =
      4 + ((Finset.univ : Finset X).filter fun x => H x b ∧ H x b').card := by
  classical
  let A : Finset X := Finset.univ.filter fun x => H x b
  let B : Finset X := Finset.univ.filter fun x => H x b'
  let I : Finset X := Finset.univ.filter fun x => H x b ∧ H x b'
  let U : Finset X := Finset.univ.filter fun x => H x b ∨ H x b'
  let Z : Finset X := Finset.univ.filter fun x => ¬ (H x b ∨ H x b')
  have hA : A.card = 2 := by
    simpa [A] using code.H_twoRegular.2 b
  have hB : B.card = 2 := by
    simpa [B] using code.H_twoRegular.2 b'
  have hI : A ∩ B = I := by
    ext x
    simp [A, B, I]
  have hU : A ∪ B = U := by
    ext x
    simp [A, B, U]
  have hunion := Finset.card_union_add_card_inter A B
  rw [hI, hU, hA, hB] at hunion
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset X)) (p := fun x => H x b ∨ H x b')
  have hpart : U.card + Z.card = 8 := by
    simpa [U, Z, code.card_left] using hpartition
  have hZ : Fintype.card (commonForeignRows H b b') = Z.card := by
    change Fintype.card {x : X // ¬ H x b ∧ ¬ H x b'} = Z.card
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp [Z, not_or]
  rw [hZ]
  change Z.card = 4 + I.card
  omega

/-- If two columns have exactly one common `H`-neighbor, they have exactly
five common eligible rows. -/
theorem MuThreeMixedGridCode.card_commonForeignRows_eq_five_of_common_eq_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (b b' : Y)
    (hcommon : ((Finset.univ : Finset X).filter
      fun x => H x b ∧ H x b').card = 1) :
    Fintype.card (commonForeignRows H b b') = 5 := by
  rw [code.card_commonForeignRows_eq_four_add_common H K C b b', hcommon]

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.card_commonForeignRows_eq_four_add_common
#print axioms
  Erdos85.MuThreeMixedGridCode.card_commonForeignRows_eq_five_of_common_eq_one
