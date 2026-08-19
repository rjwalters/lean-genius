import Proofs.Erdos85SizeTwoEigenlineCyclicHalfTurnAutocorrelation

/-!
# Negation-orbit reduction for cyclic agreement shifts

Swapping the two sources sends a shift `d` to `-d`.  Consequently an
agreement cap imposed for every base point at `d` already contains the cap
at `-d`.  Sparse packing cores therefore only need one representative of
each negation orbit of shifts (with a self-negative half-turn when `q` is
even).
-/

namespace Erdos85

noncomputable section

/-- The same-difference agreement cap at one fixed translation shift. -/
def SizeTwoCyclicAgreementBoundAtShift
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (t : sizeTwoAllowedDifference q a) (d : ZMod q) : Prop :=
  ∀ x : ZMod q,
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a P x d t t) ≤ 1

/-- A cap at `d` and a cap at `-d` are the same family of inequalities after
translating the base point. -/
theorem sizeTwoCyclicAgreementBoundAtShift_neg_iff
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (t : sizeTwoAllowedDifference q a) (d : ZMod q) :
    SizeTwoCyclicAgreementBoundAtShift P t (-d) ↔
      SizeTwoCyclicAgreementBoundAtShift P t d := by
  constructor
  · intro h x
    calc
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a P x d t t) =
          Fintype.card (SizeTwoCrossShiftedPermutationAgreement
            q a P (x + d) (-d) t t) :=
        sizeTwoCrossShiftedPermutationAgreement_card_swap P x d t t
      _ ≤ 1 := h (x + d)
  · intro h x
    calc
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a P x (-d) t t) =
          Fintype.card (SizeTwoCrossShiftedPermutationAgreement
            q a P (x + (-d)) (-(-d)) t t) :=
        sizeTwoCrossShiftedPermutationAgreement_card_swap P x (-d) t t
      _ = Fintype.card (SizeTwoCrossShiftedPermutationAgreement
            q a P (x - d) d t t) := by simp [sub_eq_add_neg]
      _ ≤ 1 := h (x - d)

/-- The q=8 shifts `1` and `7` give identical agreement-cap families. -/
theorem sizeTwoCyclicAgreementBoundAtShift_eight_one_iff_seven
    (P : SizeTwoCyclicPermutationFamily 8 (1 : ZMod 8))
    (t : sizeTwoAllowedDifference 8 (1 : ZMod 8)) :
    SizeTwoCyclicAgreementBoundAtShift P t 1 ↔
      SizeTwoCyclicAgreementBoundAtShift P t 7 := by
  have hneg : -(1 : ZMod 8) = 7 := by decide
  rw [← hneg]
  exact (sizeTwoCyclicAgreementBoundAtShift_neg_iff P t 1).symm

/-- The q=8 shifts `2` and `6` likewise form one negation orbit. -/
theorem sizeTwoCyclicAgreementBoundAtShift_eight_two_iff_six
    (P : SizeTwoCyclicPermutationFamily 8 (1 : ZMod 8))
    (t : sizeTwoAllowedDifference 8 (1 : ZMod 8)) :
    SizeTwoCyclicAgreementBoundAtShift P t 2 ↔
      SizeTwoCyclicAgreementBoundAtShift P t 6 := by
  have hneg : -(2 : ZMod 8) = 6 := by decide
  rw [← hneg]
  exact (sizeTwoCyclicAgreementBoundAtShift_neg_iff P t 2).symm

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicAgreementBoundAtShift_neg_iff
#print axioms Erdos85.sizeTwoCyclicAgreementBoundAtShift_eight_one_iff_seven
#print axioms Erdos85.sizeTwoCyclicAgreementBoundAtShift_eight_two_iff_six
