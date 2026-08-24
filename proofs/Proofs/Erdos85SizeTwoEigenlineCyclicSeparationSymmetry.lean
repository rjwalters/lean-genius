import Proofs.Erdos85SizeTwoEigenlineCyclicRawMatchingAgreement

/-!
# Undirected symmetry of cyclic source separations

The same-fiber agreement constraint at shift `d` is identical, after a base
translation, to the constraint at `-d`.  This formally justifies organizing
the parity obstruction by undirected separation orbits, as in the q=8 core
`{1,2,4}` rather than by all seven nonzero directed shifts.
-/

namespace Erdos85

noncomputable section

/-- Reversing the ordered pair of source bases sends `(x,d)` to
`(x+d,-d)` without changing the agreement cardinality. -/
theorem sizeTwoCrossShiftedPermutationAgreement_card_neg_shift
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a P x d t t) =
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a P (x + d) (-d) t t) := by
  calc
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P x d t t) =
      (sizeTwoCyclicRawSourceMatching P (x, t) ∩
        sizeTwoCyclicRawSourceMatching P (x + d, t)).card := by
      rw [sizeTwoCyclicRawSourceMatching_inter_card_eq_agreement]
      congr 2
      all_goals simp [sub_eq_add_neg]
    _ = (sizeTwoCyclicRawSourceMatching P (x + d, t) ∩
        sizeTwoCyclicRawSourceMatching P (x, t)).card := by
      rw [Finset.inter_comm]
    _ = Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P (x + d) (-d) t t) := by
      rw [sizeTwoCyclicRawSourceMatching_inter_card_eq_agreement]
      congr 2
      all_goals simp [sub_eq_add_neg]

/-- Agreement restricted to one directed source separation. -/
def SizeTwoCyclicRoutingData.AgreementAtShift
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a) (d : ZMod q) : Prop :=
  ∀ x : ZMod q,
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a data.perm x d t t) ≤ 1

/-- The cap at a shift is equivalent to the cap at its negative. -/
theorem SizeTwoCyclicRoutingData.agreementAtShift_neg_iff
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a) (d : ZMod q) :
    data.AgreementAtShift t (-d) ↔ data.AgreementAtShift t d := by
  constructor
  · intro h x
    have hs := sizeTwoCrossShiftedPermutationAgreement_card_neg_shift
      data.perm (x + d) (-d) t
    have hx := h (x + d)
    rw [neg_neg] at hs
    have hbase : x + d + -d = x := by abel
    rw [hbase] at hs
    rwa [hs] at hx
  · intro h x
    have hs := sizeTwoCrossShiftedPermutationAgreement_card_neg_shift
      data.perm (x - d) d t
    have hx := h (x - d)
    have hbase : x - d + d = x := by abel
    rw [hbase] at hs
    rwa [hs] at hx

/-- The full one-fiber agreement law supplies every named nonzero separation
cap. -/
theorem SizeTwoCyclicRoutingData.agreementAtShift_of_agreementAt
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a)
    (hagreement : data.AgreementAt t)
    (d : ZMod q) (hd : d ≠ 0) :
    data.AgreementAtShift t d := by
  intro x
  exact hagreement x d hd

end

end Erdos85

#print axioms
  Erdos85.sizeTwoCrossShiftedPermutationAgreement_card_neg_shift
#print axioms Erdos85.SizeTwoCyclicRoutingData.agreementAtShift_neg_iff
