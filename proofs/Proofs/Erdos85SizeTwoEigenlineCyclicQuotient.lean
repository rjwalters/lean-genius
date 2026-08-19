import Mathlib

/-!
# Cyclic quotient coordinates for the size-two eigenline grid

For the normalized connected internal factor, the two ambient holes have
differences `0` and `-1`.  A reflection-circulant forbidden factor has
differences `a` and `-1-a`.  Simultaneous translation of both grid
coordinates preserves all four relations.

This file isolates the quotient which is available without assuming that the
unknown exterior graph itself is translation-invariant.  Every allowed cell is
uniquely a base point together with its translation-invariant difference.
Thus diagonal-translation orbit sums may be indexed by allowed differences;
no symmetry of a hypothetical solution is smuggled into the reduction.
-/

namespace Erdos85

/-- The normalized connected ambient factor: differences `0` and `-1`. -/
def sizeTwoCyclicAmbientRel (q : ℕ) (x y : ZMod q) : Prop :=
  y - x = 0 ∨ y - x = -1

/-- The reflection-circulant forbidden factor with parameter `a`. -/
def sizeTwoReflectionRel (q : ℕ) (a x y : ZMod q) : Prop :=
  y - x = a ∨ y - x = -1 - a

/-- Differences which are not holes of the reflection-circulant factor. -/
def sizeTwoAllowedDifference (q : ℕ) (a : ZMod q) :=
  {t : ZMod q // t ≠ a ∧ t ≠ -1 - a}

/-- Cells outside the reflection-circulant forbidden factor. -/
def sizeTwoCyclicExteriorCell (q : ℕ) (a : ZMod q) :=
  {p : ZMod q × ZMod q // ¬ sizeTwoReflectionRel q a p.1 p.2}

noncomputable instance (q : ℕ) [NeZero q] (a : ZMod q) :
    Fintype (sizeTwoAllowedDifference q a) :=
  Subtype.fintype _

noncomputable instance (q : ℕ) [NeZero q] (a : ZMod q) :
    Fintype (sizeTwoCyclicExteriorCell q a) :=
  @Subtype.fintype _ _ (Classical.decPred _) _

/-- Simultaneous translation preserves the normalized ambient factor. -/
theorem sizeTwoCyclicAmbientRel_add_add_iff
    (q : ℕ) (g x y : ZMod q) :
    sizeTwoCyclicAmbientRel q (x + g) (y + g) ↔
      sizeTwoCyclicAmbientRel q x y := by
  simp [sizeTwoCyclicAmbientRel, add_sub_add_right_eq_sub]

/-- Simultaneous translation preserves every reflection-circulant factor. -/
theorem sizeTwoReflectionRel_add_add_iff
    (q : ℕ) (a g x y : ZMod q) :
    sizeTwoReflectionRel q a (x + g) (y + g) ↔
      sizeTwoReflectionRel q a x y := by
  simp [sizeTwoReflectionRel, add_sub_add_right_eq_sub]

/-- The diagonal translation action on allowed exterior cells. -/
def sizeTwoCyclicExteriorTranslate (q : ℕ) (a g : ZMod q) :
    sizeTwoCyclicExteriorCell q a ≃ sizeTwoCyclicExteriorCell q a where
  toFun u :=
    ⟨(u.1.1 + g, u.1.2 + g),
      fun h => u.2 ((sizeTwoReflectionRel_add_add_iff q a g _ _).mp h)⟩
  invFun u :=
    ⟨(u.1.1 - g, u.1.2 - g), by
      intro h
      apply u.2
      simpa [sizeTwoReflectionRel] using h⟩
  left_inv u := by
    apply Subtype.ext
    simp
  right_inv u := by
    apply Subtype.ext
    simp

/-- The difference coordinate is invariant under diagonal translation. -/
theorem sizeTwoCyclicExteriorTranslate_difference
    (q : ℕ) (a g : ZMod q) (u : sizeTwoCyclicExteriorCell q a) :
    ((sizeTwoCyclicExteriorTranslate q a g u).1.2 -
      (sizeTwoCyclicExteriorTranslate q a g u).1.1) =
      u.1.2 - u.1.1 := by
  simp [sizeTwoCyclicExteriorTranslate, add_sub_add_right_eq_sub]

/-- Exact quotient coordinates: base point × allowed difference.

The first coordinate parametrizes a diagonal-translation orbit and the second
coordinate labels the orbit.  This is the safe replacement for assuming that
an unknown exterior graph is itself cyclic.
-/
def sizeTwoCyclicExteriorCellEquiv (q : ℕ) (a : ZMod q) :
    sizeTwoCyclicExteriorCell q a ≃
      ZMod q × sizeTwoAllowedDifference q a where
  toFun u :=
    (u.1.1, ⟨u.1.2 - u.1.1, by
      constructor
      · intro h
        exact u.2 (Or.inl h)
      · intro h
        exact u.2 (Or.inr h)⟩)
  invFun z :=
    ⟨(z.1, z.1 + z.2.1), by
      intro h
      rcases h with h | h
      · exact z.2.2.1 (by simpa [sizeTwoReflectionRel] using h)
      · exact z.2.2.2 (by simpa [sizeTwoReflectionRel] using h)⟩
  left_inv u := by
    apply Subtype.ext
    simp
  right_inv z := by
    rcases z with ⟨x, t⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp

/-- In quotient coordinates, diagonal translation changes only the base
point; the allowed-difference orbit label is fixed. -/
theorem sizeTwoCyclicExteriorCellEquiv_translate
    (q : ℕ) (a g : ZMod q) (u : sizeTwoCyclicExteriorCell q a) :
    sizeTwoCyclicExteriorCellEquiv q a
        (sizeTwoCyclicExteriorTranslate q a g u) =
      ((sizeTwoCyclicExteriorCellEquiv q a u).1 + g,
        (sizeTwoCyclicExteriorCellEquiv q a u).2) := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact sizeTwoCyclicExteriorTranslate_difference q a g u

/-- When the two forbidden reflection shifts are distinct, exactly two of the
`q` difference classes are removed. -/
theorem sizeTwoAllowedDifference_card
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : a ≠ -1 - a) :
    Fintype.card (sizeTwoAllowedDifference q a) = q - 2 := by
  classical
  change Fintype.card {t : ZMod q // t ≠ a ∧ t ≠ -1 - a} = q - 2
  rw [Fintype.card_subtype]
  rw [show ({t : ZMod q | t ≠ a ∧ t ≠ -1 - a} : Finset (ZMod q)) =
      Finset.univ \ {a, -1 - a} by
    ext t
    simp [not_or]]
  simp [Finset.card_sdiff, ZMod.card, ha]

/-- Consequently the full exterior grid contains `q(q-2)` cells. -/
theorem sizeTwoCyclicExteriorCell_card
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : a ≠ -1 - a) :
    Fintype.card (sizeTwoCyclicExteriorCell q a) = q * (q - 2) := by
  rw [Fintype.card_congr (sizeTwoCyclicExteriorCellEquiv q a),
    Fintype.card_prod, ZMod.card, sizeTwoAllowedDifference_card q a ha]

/-- Orbit aggregation for functions of the difference coordinate: every
allowed difference occurs once over each of the `q` base points. -/
theorem sizeTwoCyclicExteriorCell_sum_difference
    (q : ℕ) [NeZero q] (a : ZMod q) {M : Type*} [AddCommMonoid M]
    (f : sizeTwoAllowedDifference q a → M) :
    (∑ u : sizeTwoCyclicExteriorCell q a,
        f (sizeTwoCyclicExteriorCellEquiv q a u).2) =
      q • ∑ t : sizeTwoAllowedDifference q a, f t := by
  calc
    _ = ∑ z : ZMod q × sizeTwoAllowedDifference q a, f z.2 :=
      (sizeTwoCyclicExteriorCellEquiv q a).sum_comp (fun z => f z.2)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [ZMod.card]

end Erdos85

#print axioms Erdos85.sizeTwoCyclicAmbientRel_add_add_iff
#print axioms Erdos85.sizeTwoReflectionRel_add_add_iff
#print axioms Erdos85.sizeTwoCyclicExteriorTranslate_difference
#print axioms Erdos85.sizeTwoCyclicExteriorCellEquiv_translate
#print axioms Erdos85.sizeTwoAllowedDifference_card
#print axioms Erdos85.sizeTwoCyclicExteriorCell_card
#print axioms Erdos85.sizeTwoCyclicExteriorCell_sum_difference
