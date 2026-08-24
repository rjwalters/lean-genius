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

/-- Agreement mass at an involutive nonzero separation is even.  In
particular, at an even modulus this applies to the antipodal shift `q/2`:
base translation by that shift freely pairs agreement witnesses with equal
cardinality. -/
theorem sizeTwoCrossShiftedPermutationAgreement_antipodal_sum_even
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (d : ZMod q) (hd : d ≠ 0) (horder : d + d = 0)
    (t : sizeTwoAllowedDifference q a) :
    Even (∑ x : ZMod q,
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P x d t t)) := by
  classical
  let sigma : ZMod q → ZMod q := fun x => x + d
  let weight : ZMod q → ZMod 2 := fun x =>
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a P x d t t)
  have hpair (x : ZMod q) : weight x + weight (sigma x) = 0 := by
    have hs := sizeTwoCrossShiftedPermutationAgreement_card_neg_shift
      P x d t
    have hneg : -d = d := by
      apply add_left_cancel (a := d)
      simpa using horder.symm
    rw [hneg] at hs
    change ((Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a P x d t t) : ℕ) : ZMod 2) +
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P (x + d) d t t) = 0
    rw [← hs]
    exact CharTwo.add_self_eq_zero _
  have hsum : (∑ x : ZMod q, weight x) = 0 := by
    apply Finset.sum_ninvolution sigma
    · intro x
      exact hpair x
    · intro x _ hfix
      apply hd
      have h := congrArg (fun z : ZMod q => z - x) hfix
      simpa [sigma, sub_eq_add_neg, add_assoc] using h
    · intro x
      exact Finset.mem_univ _
    · intro x
      dsimp [sigma]
      rw [add_assoc, horder, add_zero]
  have hcast :
      (((∑ x : ZMod q,
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a P x d t t)) : ℕ) : ZMod 2) = 0 := by
    rw [Nat.cast_sum]
    exact hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

end

end Erdos85

#print axioms
  Erdos85.sizeTwoCrossShiftedPermutationAgreement_card_neg_shift
#print axioms Erdos85.SizeTwoCyclicRoutingData.agreementAtShift_neg_iff
#print axioms
  Erdos85.sizeTwoCrossShiftedPermutationAgreement_antipodal_sum_even
