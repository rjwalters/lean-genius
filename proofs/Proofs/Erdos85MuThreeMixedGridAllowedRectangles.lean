import Proofs.Erdos85MuThreeMixedGridRectangleHolonomy

/-!
# Density of allowed rectangles

Since `H` is two-regular on two shores of size eight, its complement has
degree six.  Consequently any two columns have at least four common allowed
rows, so nondegenerate allowed rectangles are abundant.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def mixedGridCommonAllowedRows
    {X Y : Type*} [Fintype X] [DecidableEq X]
    (H : X → Y → Prop) [DecidableRel H] (y₁ y₂ : Y) : Finset X :=
  Finset.univ.filter fun x => ¬ H x y₁ ∧ ¬ H x y₂

theorem MuThreeMixedGridCode.allowedRows_card_eq_six
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y : Y) :
    ((Finset.univ : Finset X).filter fun x => ¬ H x y).card = 6 := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset X)) (p := fun x => H x y)
  simp only [Finset.card_univ, code.card_left] at hpartition
  rw [code.H_twoRegular.2 y] at hpartition
  omega

/-- Two columns share at least four `H`-allowed rows. -/
theorem MuThreeMixedGridCode.four_le_commonAllowedRows_card
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y₁ y₂ : Y) :
    4 ≤ (mixedGridCommonAllowedRows H y₁ y₂).card := by
  let A := (Finset.univ : Finset X).filter fun x => ¬ H x y₁
  let B := (Finset.univ : Finset X).filter fun x => ¬ H x y₂
  have hA : A.card = 6 := code.allowedRows_card_eq_six H K C y₁
  have hB : B.card = 6 := code.allowedRows_card_eq_six H K C y₂
  have hunion : (A ∪ B).card ≤ 8 := by
    have hsub : A ∪ B ⊆ (Finset.univ : Finset X) := by simp
    exact (Finset.card_le_card hsub).trans_eq code.card_left
  have hie := Finset.card_union_add_card_inter A B
  have hinter : 4 ≤ (A ∩ B).card := by omega
  have heq : A ∩ B = mixedGridCommonAllowedRows H y₁ y₂ := by
    ext x
    simp [A, B, mixedGridCommonAllowedRows]
  simpa [heq] using hinter

/-- Every pair of distinct columns supports a nondegenerate allowed
rectangle, with at least two choices of its two rows. -/
theorem MuThreeMixedGridCode.exists_allowedRectangle_on_columns
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y₁ y₂ : Y) (hy : y₁ ≠ y₂) :
    y₁ ≠ y₂ ∧ ∃ x₁ x₂ : X, x₁ ≠ x₂ ∧
      ¬ H x₁ y₁ ∧ ¬ H x₁ y₂ ∧ ¬ H x₂ y₂ ∧ ¬ H x₂ y₁ := by
  let S := mixedGridCommonAllowedRows H y₁ y₂
  have hcard : 4 ≤ S.card := by
    simpa [S] using code.four_le_commonAllowedRows_card H K C y₁ y₂
  have hOne : 1 < S.card := by omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ :=
    Finset.one_lt_card.mp hOne
  have hx₁' := (Finset.mem_filter.mp hx₁).2
  have hx₂' := (Finset.mem_filter.mp hx₂).2
  exact ⟨hy, x₁, x₂, hne, hx₁'.1, hx₁'.2, hx₂'.2, hx₂'.1⟩

/-- Every distinct column pair therefore carries a six-point derangement
obtained as the holonomy around some allowed rectangle. -/
theorem MuThreeMixedGridCode.exists_fixedPointFree_rectangleHolonomy_on_columns
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y₁ y₂ : Y) (hy : y₁ ≠ y₂) :
    ∃ (x₁ x₂ : X) (hx : x₁ ≠ x₂)
        (h11 : ¬ H x₁ y₁) (h12 : ¬ H x₁ y₂)
        (h22 : ¬ H x₂ y₂) (h21 : ¬ H x₂ y₁),
      ∀ u : mixedGridOccupiedColumn K y₁,
        mixedGridRectangleHolonomy H K C code x₁ x₂ y₁ y₂
          h11 h12 h22 h21 u ≠ u := by
  obtain ⟨_, x₁, x₂, hx, h11, h12, h22, h21⟩ :=
    code.exists_allowedRectangle_on_columns H K C y₁ y₂ hy
  exact ⟨x₁, x₂, hx, h11, h12, h22, h21,
    fun u => mixedGridRectangleHolonomy_ne H K C code
      x₁ x₂ y₁ y₂ hx hy h11 h12 h22 h21 u⟩

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.four_le_commonAllowedRows_card
#print axioms Erdos85.MuThreeMixedGridCode.exists_allowedRectangle_on_columns
#print axioms
  Erdos85.MuThreeMixedGridCode.exists_fixedPointFree_rectangleHolonomy_on_columns
