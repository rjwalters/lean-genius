import Proofs.Erdos85SizeTwoEigenlineCyclicFiveCellSubsystem

/-!
# Antipodal rectangle terminal for the five-cell subsystem

The exact `q = 8` deletion witness shows that the two units of excess in the
middle half-turn cell form one internal `K₂,₂`: the source matchings at `x`
and `x + m` share two target edges.  This file packages that rectangle and
proves that it is exactly what the middle half-turn cap forbids.

The remaining generic content is deliberately isolated: the four short-cell
caps must force such a rectangle.  No finite `q = 8` constant enters the
terminal below.
-/

namespace Erdos85

noncomputable section

/-- The middle-fiber source matchings at antipodal bases share at least two
target edges, i.e. contain an internal `K₂,₂` rectangle. -/
def SizeTwoCyclicMiddleAntipodalRectangle
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (middle : sizeTwoAllowedDifference q a)
    (x m : ZMod q) : Prop :=
  2 ≤ (sizeTwoCyclicRawSourceMatching P (x, middle) ∩
    sizeTwoCyclicRawSourceMatching P (x + m, middle)).card

/-- The middle half-turn cap excludes an antipodal rectangle. -/
theorem SizeTwoCyclicLooplessFiveCellCode.not_middleAntipodalRectangle
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ m : ZMod q}
    (five : SizeTwoCyclicLooplessFiveCellCode q a
      left middle right d₁ d₂ m)
    (x : ZMod q) :
    ¬ SizeTwoCyclicMiddleAntipodalRectangle
      five.code.toPermutationCode.perm middle x m := by
  intro hrect
  rw [SizeTwoCyclicMiddleAntipodalRectangle,
    sizeTwoCyclicRawSourceMatching_inter_card_eq_agreement] at hrect
  have hshift : (x + m) - x = m := by abel
  rw [hshift] at hrect
  have hrect' : 2 ≤ Fintype.card
      (SizeTwoCrossShiftedPermutationAgreement q a
        five.code.toPermutationCode.perm x m middle middle) := by
    simpa using hrect
  have hcap := five.middle_m x
  omega

/-- A four-short-cell forcing lemma whose conclusion is an antipodal
rectangle immediately empties the corresponding five-cell subsystem. -/
theorem isEmpty_sizeTwoCyclicLooplessFiveCellCode_of_middleRectangle
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ m : ZMod q}
    (hrectangle : ∀ five : SizeTwoCyclicLooplessFiveCellCode q a
        left middle right d₁ d₂ m,
      ∃ x, SizeTwoCyclicMiddleAntipodalRectangle
        five.code.toPermutationCode.perm middle x m) :
    IsEmpty (SizeTwoCyclicLooplessFiveCellCode q a
      left middle right d₁ d₂ m) := by
  constructor
  intro five
  rcases hrectangle five with ⟨x, hx⟩
  exact five.not_middleAntipodalRectangle x hx

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicLooplessFiveCellCode.not_middleAntipodalRectangle
#print axioms Erdos85.isEmpty_sizeTwoCyclicLooplessFiveCellCode_of_middleRectangle
