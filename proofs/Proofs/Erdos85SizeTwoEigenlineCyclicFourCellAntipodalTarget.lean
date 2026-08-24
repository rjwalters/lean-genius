import Proofs.Erdos85SizeTwoEigenlineCyclicFiveCellSubsystem

/-!
# Four short cells force the middle antipodal collision

The fiber-resolved `q = 8` core factors more sharply than the five-cell
interface suggests.  After removing the middle antipodal cap, the remaining
four short-shift caps force two agreements between antipodal sources in the
middle fiber.  Reinstating the fifth cap immediately contradicts that forced
collision.

This file packages the q-generic form of that factorization.  It proves the
consumer, not the forcing statement: the latter is the remaining mathematical
leaf suggested by the exact core.
-/

namespace Erdos85

noncomputable section

/-- The five-cell subsystem with its middle antipodal cap removed. -/
structure SizeTwoCyclicLooplessFourCellCode
    (q : ℕ) [NeZero q] (a : ZMod q)
    (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ : ZMod q) where
  code : SizeTwoCyclicReciprocalPermutationCode q a
  loopless : code.Loopless
  left_d₁ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₁ left left) ≤ 1
  left_d₂ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₂ left left) ≤ 1
  middle_d₁ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₁ middle middle) ≤ 1
  right_d₂ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₂ right right) ≤ 1

/-- Forget the fifth, middle-`m` cap. -/
def SizeTwoCyclicLooplessFiveCellCode.toFourCellCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ m : ZMod q}
    (five : SizeTwoCyclicLooplessFiveCellCode q a
      left middle right d₁ d₂ m) :
    SizeTwoCyclicLooplessFourCellCode q a
      left middle right d₁ d₂ where
  code := five.code
  loopless := five.loopless
  left_d₁ := five.left_d₁
  left_d₂ := five.left_d₂
  middle_d₁ := five.middle_d₁
  right_d₂ := five.right_d₂

/-- Two common targets for a pair of middle-fiber sources separated by `m`.
Under the selected-fiber graph interpretation this is an antipodal rectangle. -/
def SizeTwoCyclicLooplessFourCellCode.HasMiddleAntipodalCollision
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ : ZMod q}
    (four : SizeTwoCyclicLooplessFourCellCode q a
      left middle right d₁ d₂)
    (m : ZMod q) : Prop :=
  ∃ x : ZMod q,
    2 ≤ Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a four.code.toPermutationCode.perm x m middle middle)

/-- The exact new leaf: every four-cell code has a middle antipodal
collision. -/
def SizeTwoCyclicLooplessFourCellAntipodalForcing
    (q : ℕ) [NeZero q] (a : ZMod q)
    (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ m : ZMod q) : Prop :=
  ∀ four : SizeTwoCyclicLooplessFourCellCode q a
      left middle right d₁ d₂,
    four.HasMiddleAntipodalCollision m

/-- Four-cell antipodal forcing contradicts the fifth cap. -/
theorem isEmpty_sizeTwoCyclicLooplessFiveCellCode_of_fourCellAntipodalForcing
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ m : ZMod q}
    (hforce : SizeTwoCyclicLooplessFourCellAntipodalForcing q a
      left middle right d₁ d₂ m) :
    IsEmpty (SizeTwoCyclicLooplessFiveCellCode q a
      left middle right d₁ d₂ m) := by
  constructor
  intro five
  obtain ⟨x, htwo⟩ := hforce five.toFourCellCode
  change 2 ≤ Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a five.code.toPermutationCode.perm x m middle middle) at htwo
  have hone := five.middle_m x
  omega

/-- A selected four-cell forcing statement supplies the previously packaged
five-cell exclusion. -/
theorem sizeTwoCyclicLooplessFiveCellExclusion_of_fourCellAntipodalForcing
    {q : ℕ} [NeZero q] {a : ZMod q}
    (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ m : ZMod q)
    (hlm : left ≠ middle) (hmr : middle ≠ right)
    (hlr : left ≠ right)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hm : m ≠ 0)
    (hm2 : m + m = 0)
    (hforce : SizeTwoCyclicLooplessFourCellAntipodalForcing q a
      left middle right d₁ d₂ m) :
    SizeTwoCyclicLooplessFiveCellExclusion q a := by
  exact ⟨left, middle, right, d₁, d₂, m,
    hlm, hmr, hlr, hd₁, hd₂, hm, hm2,
    isEmpty_sizeTwoCyclicLooplessFiveCellCode_of_fourCellAntipodalForcing
      hforce⟩

end

end Erdos85

#print axioms
  Erdos85.isEmpty_sizeTwoCyclicLooplessFiveCellCode_of_fourCellAntipodalForcing
#print axioms
  Erdos85.sizeTwoCyclicLooplessFiveCellExclusion_of_fourCellAntipodalForcing
