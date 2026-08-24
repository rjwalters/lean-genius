import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationExactCode
import Proofs.Erdos85SizeTwoEigenlineCyclicRawMatchingAgreement

/-!
# Generic five-cell ternary separation subsystem

The fiber-resolved q=8 MUS uses three difference fibers and only five
agreement cells:

* left fiber at short shifts `d₁,d₂`;
* middle fiber at `d₁` and the involutive shift `m`;
* right fiber at `d₂`.

This file packages that pattern at general parameters.  It retains global
reciprocity and looplessness but no agreement caps beyond those five cells.
Thus it is the smallest current q-generic interface suggested by the exact
ternary core, without baking q=8 constants into the statement.
-/

namespace Erdos85

noncomputable section

/-- A reciprocal loopless routing code with exactly the five separation
caps in the localized ternary MUS. -/
structure SizeTwoCyclicLooplessFiveCellCode
    (q : ℕ) [NeZero q] (a : ZMod q)
    (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ m : ZMod q) where
  code : SizeTwoCyclicReciprocalPermutationCode q a
  loopless : code.Loopless
  left_d₁ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₁ left left) ≤ 1
  left_d₂ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₂ left left) ≤ 1
  middle_d₁ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₁ middle middle) ≤ 1
  middle_m : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x m middle middle) ≤ 1
  right_d₂ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₂ right right) ≤ 1

/-- Every exact code restricts to the five-cell subsystem at any three
fibers and any three nonzero shifts. -/
def SizeTwoCyclicExactPermutationCode.toFiveCellCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    (exact : SizeTwoCyclicExactPermutationCode q a)
    (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ m : ZMod q) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hm : m ≠ 0) :
    SizeTwoCyclicLooplessFiveCellCode q a
      left middle right d₁ d₂ m where
  code := exact.toReciprocalCode
  loopless := exact.loopless
  left_d₁ := by
    intro x
    exact exact.toFullCode.cross_agreement_le_one
      x d₁ left left (Or.inl hd₁)
  left_d₂ := by
    intro x
    exact exact.toFullCode.cross_agreement_le_one
      x d₂ left left (Or.inl hd₂)
  middle_d₁ := by
    intro x
    exact exact.toFullCode.cross_agreement_le_one
      x d₁ middle middle (Or.inl hd₁)
  middle_m := by
    intro x
    exact exact.toFullCode.cross_agreement_le_one
      x m middle middle (Or.inl hm)
  right_d₂ := by
    intro x
    exact exact.toFullCode.cross_agreement_le_one
      x d₂ right right (Or.inl hd₂)

/-- The exact generic ternary target: find three distinct fibers, two short
nonzero shifts, and one nonzero involutive shift for which the five-cell
subsystem is empty. -/
def SizeTwoCyclicLooplessFiveCellExclusion
    (q : ℕ) [NeZero q] (a : ZMod q) : Prop :=
  ∃ (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ m : ZMod q),
    left ≠ middle ∧ middle ≠ right ∧ left ≠ right ∧
    d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ m ≠ 0 ∧ m + m = 0 ∧
    IsEmpty (SizeTwoCyclicLooplessFiveCellCode q a
      left middle right d₁ d₂ m)

/-- Five-cell exclusion is already enough to rule out an exact code. -/
theorem isEmpty_sizeTwoCyclicExactPermutationCode_of_fiveCellExclusion
    {q : ℕ} [NeZero q] {a : ZMod q}
    (h : SizeTwoCyclicLooplessFiveCellExclusion q a) :
    IsEmpty (SizeTwoCyclicExactPermutationCode q a) := by
  rcases h with ⟨left, middle, right, d₁, d₂, m,
    _hlm, _hmr, _hlr, hd₁, hd₂, hm, _horder, hempty⟩
  constructor
  intro exact
  exact hempty.false
    (exact.toFiveCellCode left middle right d₁ d₂ m hd₁ hd₂ hm)

end

end Erdos85

#print axioms
  Erdos85.isEmpty_sizeTwoCyclicExactPermutationCode_of_fiveCellExclusion
