import Proofs.Erdos85SizeTwoEigenlineCyclicTwoHoleShiftCompletion
import Proofs.Erdos85SizeTwoEigenlineCyclicReflectedHammingDistance

/-!
# Fixed points of the completed double-shift comparison

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

The same completed translation is applied before and after the reflected
routing permutation.  Away from the two input and two output hole-crossing
coordinates, a fixed point of this double-shift comparison is exactly a
shifted reflected agreement.  The C4 packing law therefore permits at most
one regular fixed point.
-/

namespace Erdos85

noncomputable section

set_option linter.unusedVariables false

/-- A fixed point for which both uses of the completed translation agree
with literal subtraction by `d`. -/
structure SizeTwoDoubleShiftRegularFixedPoint
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1)) where
  row : SizeTwoAdmissibleTargetRow q t.1
  shifted_admissible :
    t.1 ≠ row.1 - d ∧ t.1 ≠ (row.1 - d) - 1
  output_shifted_admissible :
    let shiftedRow : SizeTwoAdmissibleTargetRow q t.1 :=
      ⟨row.1 - d, shifted_admissible⟩
    let output := code.reflectedPerm (x + d) t shiftedRow
    t.1 ≠ output.1 - d ∧ t.1 ≠ (output.1 - d) - 1
  fixed : sizeTwoDoubleShiftComparison shift
      (code.reflectedPerm (x + d) t) (code.reflectedPerm x t) row = row

noncomputable instance SizeTwoDoubleShiftRegularFixedPoint.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1)) :
    Fintype (SizeTwoDoubleShiftRegularFixedPoint code x d t shift) :=
  Fintype.ofInjective (fun w => w.row.1) (by
    intro u v h
    cases u
    cases v
    cases Subtype.ext h
    rfl)

/-- A regular fixed point gives a genuine shifted agreement. -/
def SizeTwoDoubleShiftRegularFixedPoint.toReflectedAgreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1))
    (hshift : ∀ (r : SizeTwoAdmissibleTargetRow q t.1)
      (hr : t.1 ≠ r.1 - d ∧ t.1 ≠ (r.1 - d) - 1),
      (shift r).1 = r.1 - d)
    (w : SizeTwoDoubleShiftRegularFixedPoint code x d t shift) :
    SizeTwoReflectedShiftedAgreement q a code x d t := by
  let shiftedRow : SizeTwoAdmissibleTargetRow q t.1 :=
    ⟨w.row.1 - d, w.shifted_admissible⟩
  let output := code.reflectedPerm (x + d) t shiftedRow
  have hshiftInput : shift w.row = shiftedRow := by
    apply Subtype.ext
    exact hshift w.row w.shifted_admissible
  have hshiftOutput : shift output =
      (⟨output.1 - d, w.output_shifted_admissible⟩ :
        SizeTwoAdmissibleTargetRow q t.1) := by
    apply Subtype.ext
    exact hshift output w.output_shifted_admissible
  refine ⟨w.row, w.shifted_admissible, ?_⟩
  have hfixed := w.fixed
  change (code.reflectedPerm x t).symm
      (shift (code.reflectedPerm (x + d) t (shift w.row))) = w.row at hfixed
  rw [hshiftInput, hshiftOutput] at hfixed
  have hvalue := congrArg (fun r => (code.reflectedPerm x t r).1) hfixed
  have hvalue' : output.1 - d = (code.reflectedPerm x t w.row).1 := by
    simpa only [Equiv.apply_symm_apply] using hvalue
  change output.1 = (code.reflectedPerm x t w.row).1 + d
  exact eq_add_of_sub_eq hvalue'

theorem SizeTwoDoubleShiftRegularFixedPoint.toReflectedAgreement_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1))
    (hshift : ∀ (r : SizeTwoAdmissibleTargetRow q t.1)
      (hr : t.1 ≠ r.1 - d ∧ t.1 ≠ (r.1 - d) - 1),
      (shift r).1 = r.1 - d) :
    Function.Injective
      (SizeTwoDoubleShiftRegularFixedPoint.toReflectedAgreement
        code x d t shift hshift) := by
  intro u v h
  have hrow : u.row = v.row :=
    congrArg SizeTwoReflectedShiftedAgreement.row h
  cases u with
  | mk ur uin uout ufix =>
    cases v with
    | mk vr vin vout vfix =>
      dsimp only at hrow
      cases hrow
      rfl

/-- The packing law bounds regular fixed points by one. -/
theorem sizeTwoDoubleShiftRegularFixedPoint_card_le_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (hd : d ≠ 0)
    (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1))
    (hshift : ∀ (r : SizeTwoAdmissibleTargetRow q t.1)
      (hr : t.1 ≠ r.1 - d ∧ t.1 ≠ (r.1 - d) - 1),
      (shift r).1 = r.1 - d) :
    Fintype.card (SizeTwoDoubleShiftRegularFixedPoint code x d t shift) ≤ 1 := by
  calc
    Fintype.card (SizeTwoDoubleShiftRegularFixedPoint code x d t shift) ≤
      Fintype.card (SizeTwoReflectedShiftedAgreement q a code x d t) :=
      Fintype.card_le_of_injective
        (SizeTwoDoubleShiftRegularFixedPoint.toReflectedAgreement
          code x d t shift hshift)
        (SizeTwoDoubleShiftRegularFixedPoint.toReflectedAgreement_injective
          code x d t shift hshift)
    _ ≤ 1 := sizeTwoReflectedShiftedAgreement_card_le_one code x d hd t

/-- Cyclic parallel completion: at most one regular fixed point. -/
theorem sizeTwoCyclicParallelDoubleShiftRegularFixedPoint_card_le_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (hd : SizeTwoGenericRowShift d) :
    Fintype.card (SizeTwoDoubleShiftRegularFixedPoint code x d t
      (sizeTwoCyclicParallelRowShiftCompletion hq1 t.1 d hd)) ≤ 1 := by
  exact sizeTwoDoubleShiftRegularFixedPoint_card_le_one code x d hd.1 t
    (sizeTwoCyclicParallelRowShiftCompletion hq1 t.1 d hd)
    (sizeTwoCyclicParallelRowShiftCompletion_apply hq1 t.1 d hd)

/-- Cyclic crossed completion: at most one regular fixed point. -/
theorem sizeTwoCyclicCrossDoubleShiftRegularFixedPoint_card_le_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (hd : SizeTwoGenericRowShift d) :
    Fintype.card (SizeTwoDoubleShiftRegularFixedPoint code x d t
      (sizeTwoCyclicCrossRowShiftCompletion hq1 t.1 d hd)) ≤ 1 := by
  exact sizeTwoDoubleShiftRegularFixedPoint_card_le_one code x d hd.1 t
    (sizeTwoCyclicCrossRowShiftCompletion hq1 t.1 d hd)
    (sizeTwoCyclicCrossRowShiftCompletion_apply hq1 t.1 d hd)

end

end Erdos85

#print axioms Erdos85.SizeTwoDoubleShiftRegularFixedPoint.toReflectedAgreement
#print axioms Erdos85.sizeTwoDoubleShiftRegularFixedPoint_card_le_one
#print axioms Erdos85.sizeTwoCyclicParallelDoubleShiftRegularFixedPoint_card_le_one
#print axioms Erdos85.sizeTwoCyclicCrossDoubleShiftRegularFixedPoint_card_le_one
