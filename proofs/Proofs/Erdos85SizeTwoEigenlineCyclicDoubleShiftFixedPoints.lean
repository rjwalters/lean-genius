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

/-- All fixed points of a double-shift comparison. -/
abbrev SizeTwoDoubleShiftFixedPoint
    {q : ℕ} [NeZero q]
    (t : ZMod q)
    (shift next base : Equiv.Perm (SizeTwoAdmissibleTargetRow q t)) :=
  Function.fixedPoints (sizeTwoDoubleShiftComparison shift next base)

noncomputable instance SizeTwoDoubleShiftFixedPoint.instFintype
    {q : ℕ} [NeZero q] (t : ZMod q)
    (shift next base : Equiv.Perm (SizeTwoAdmissibleTargetRow q t)) :
    Fintype (SizeTwoDoubleShiftFixedPoint t shift next base) :=
  Fintype.ofFinite _

/-- First input hole crossing: literal translation lands at `t`. -/
abbrev SizeTwoDoubleShiftInputExceptionZero
    {q : ℕ} [NeZero q] (t d : ZMod q) :=
  {r : SizeTwoAdmissibleTargetRow q t // t = r.1 - d}

/-- Second input hole crossing: literal translation lands at `t+1`. -/
abbrev SizeTwoDoubleShiftInputExceptionOne
    {q : ℕ} [NeZero q] (t d : ZMod q) :=
  {r : SizeTwoAdmissibleTargetRow q t // t = (r.1 - d) - 1}

/-- First output hole crossing after `next ∘ shift`. -/
abbrev SizeTwoDoubleShiftOutputExceptionZero
    {q : ℕ} [NeZero q] (t d : ZMod q)
    (shift next : Equiv.Perm (SizeTwoAdmissibleTargetRow q t)) :=
  {r : SizeTwoAdmissibleTargetRow q t // t = (next (shift r)).1 - d}

/-- Second output hole crossing after `next ∘ shift`. -/
abbrev SizeTwoDoubleShiftOutputExceptionOne
    {q : ℕ} [NeZero q] (t d : ZMod q)
    (shift next : Equiv.Perm (SizeTwoAdmissibleTargetRow q t)) :=
  {r : SizeTwoAdmissibleTargetRow q t //
    t = ((next (shift r)).1 - d) - 1}

theorem sizeTwoDoubleShiftInputExceptionZero_card_le_one
    {q : ℕ} [NeZero q] (t d : ZMod q) :
    Fintype.card (SizeTwoDoubleShiftInputExceptionZero t d) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro u v
  apply Subtype.ext
  apply Subtype.ext
  have hu := u.2
  have hv := v.2
  change t = u.1.1 - d at hu
  change t = v.1.1 - d at hv
  exact sub_left_injective (hu.symm.trans hv)

theorem sizeTwoDoubleShiftInputExceptionOne_card_le_one
    {q : ℕ} [NeZero q] (t d : ZMod q) :
    Fintype.card (SizeTwoDoubleShiftInputExceptionOne t d) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro u v
  apply Subtype.ext
  apply Subtype.ext
  have hu := u.2
  have hv := v.2
  change t = (u.1.1 - d) - 1 at hu
  change t = (v.1.1 - d) - 1 at hv
  apply sub_left_injective
  exact sub_left_injective (hu.symm.trans hv)

theorem sizeTwoDoubleShiftOutputExceptionZero_card_le_one
    {q : ℕ} [NeZero q] (t d : ZMod q)
    (shift next : Equiv.Perm (SizeTwoAdmissibleTargetRow q t)) :
    Fintype.card (SizeTwoDoubleShiftOutputExceptionZero t d shift next) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro u v
  apply Subtype.ext
  apply shift.injective
  apply next.injective
  apply Subtype.ext
  have hu := u.2
  have hv := v.2
  change t = (next (shift u.1)).1 - d at hu
  change t = (next (shift v.1)).1 - d at hv
  exact sub_left_injective (hu.symm.trans hv)

theorem sizeTwoDoubleShiftOutputExceptionOne_card_le_one
    {q : ℕ} [NeZero q] (t d : ZMod q)
    (shift next : Equiv.Perm (SizeTwoAdmissibleTargetRow q t)) :
    Fintype.card (SizeTwoDoubleShiftOutputExceptionOne t d shift next) ≤ 1 := by
  rw [Fintype.card_le_one_iff]
  intro u v
  apply Subtype.ext
  apply shift.injective
  apply next.injective
  apply Subtype.ext
  have hu := u.2
  have hv := v.2
  change t = ((next (shift u.1)).1 - d) - 1 at hu
  change t = ((next (shift v.1)).1 - d) - 1 at hv
  apply sub_left_injective
  exact sub_left_injective (hu.symm.trans hv)

/-- Disjoint-sum target of the fixed-point classification. -/
abbrev SizeTwoDoubleShiftFixedPointClass
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1)) :=
  SizeTwoDoubleShiftRegularFixedPoint code x d t shift ⊕
    (SizeTwoDoubleShiftInputExceptionZero t.1 d ⊕
      (SizeTwoDoubleShiftInputExceptionOne t.1 d ⊕
        (SizeTwoDoubleShiftOutputExceptionZero t.1 d shift
            (code.reflectedPerm (x + d) t) ⊕
          SizeTwoDoubleShiftOutputExceptionOne t.1 d shift
            (code.reflectedPerm (x + d) t))))

/-- Classify a fixed point as regular or by the first hole crossing it
encounters. -/
def sizeTwoDoubleShiftFixedPointClassify
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1))
    (hshift : ∀ (r : SizeTwoAdmissibleTargetRow q t.1)
      (_hr : t.1 ≠ r.1 - d ∧ t.1 ≠ (r.1 - d) - 1),
      (shift r).1 = r.1 - d)
    (w : SizeTwoDoubleShiftFixedPoint t.1 shift
      (code.reflectedPerm (x + d) t) (code.reflectedPerm x t)) :
    SizeTwoDoubleShiftFixedPointClass code x d t shift := by
  classical
  by_cases hin : t.1 ≠ w.1.1 - d ∧ t.1 ≠ (w.1.1 - d) - 1
  · let shiftedRow : SizeTwoAdmissibleTargetRow q t.1 :=
      ⟨w.1.1 - d, hin⟩
    have hshiftInput : shift w.1 = shiftedRow := by
      apply Subtype.ext
      exact hshift w.1 hin
    let output := code.reflectedPerm (x + d) t shiftedRow
    by_cases hout : t.1 ≠ output.1 - d ∧ t.1 ≠ (output.1 - d) - 1
    · exact Sum.inl ⟨w.1, hin, hout, w.2⟩
    · by_cases hbad : t.1 = output.1 - d
      · exact Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨w.1, by
          rw [hshiftInput]
          simpa [shiftedRow, output] using hbad⟩)))
      · have hbad' : t.1 = (output.1 - d) - 1 := by
          push Not at hout
          exact hout hbad
        exact Sum.inr (Sum.inr (Sum.inr (Sum.inr ⟨w.1, by
          rw [hshiftInput]
          simpa [shiftedRow, output] using hbad'⟩)))
  · by_cases hbad : t.1 = w.1.1 - d
    · exact Sum.inr (Sum.inl ⟨w.1, hbad⟩)
    · have hbad' : t.1 = (w.1.1 - d) - 1 := by
        push Not at hin
        exact hin hbad
      exact Sum.inr (Sum.inr (Sum.inl ⟨w.1, hbad'⟩))

/-- Recover the underlying row from any classification branch. -/
def SizeTwoDoubleShiftFixedPointClass.row
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a}
    {shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1)} :
    SizeTwoDoubleShiftFixedPointClass code x d t shift →
      SizeTwoAdmissibleTargetRow q t.1
  | Sum.inl w => w.row
  | Sum.inr (Sum.inl w) => w.1
  | Sum.inr (Sum.inr (Sum.inl w)) => w.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl w))) => w.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr w))) => w.1

@[simp] theorem sizeTwoDoubleShiftFixedPointClassify_row
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1))
    (hshift : ∀ (r : SizeTwoAdmissibleTargetRow q t.1)
      (_hr : t.1 ≠ r.1 - d ∧ t.1 ≠ (r.1 - d) - 1),
      (shift r).1 = r.1 - d)
    (w : SizeTwoDoubleShiftFixedPoint t.1 shift
      (code.reflectedPerm (x + d) t) (code.reflectedPerm x t)) :
    (sizeTwoDoubleShiftFixedPointClassify code x d t shift hshift w).row = w.1 := by
  classical
  unfold sizeTwoDoubleShiftFixedPointClassify
  split <;> dsimp only
  all_goals repeat' first | split | rfl

theorem sizeTwoDoubleShiftFixedPointClassify_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1)) :
    ∀ (hshift : ∀ (r : SizeTwoAdmissibleTargetRow q t.1)
      (_hr : t.1 ≠ r.1 - d ∧ t.1 ≠ (r.1 - d) - 1),
      (shift r).1 = r.1 - d),
    Function.Injective
      (sizeTwoDoubleShiftFixedPointClassify code x d t shift hshift) := by
  intro hshift
  intro u v h
  have hrow := congrArg SizeTwoDoubleShiftFixedPointClass.row h
  rw [sizeTwoDoubleShiftFixedPointClassify_row,
    sizeTwoDoubleShiftFixedPointClassify_row] at hrow
  exact Subtype.ext hrow

/-- Total fixed points are bounded by the regular budget plus four hole
crossings. -/
theorem sizeTwoDoubleShiftFixedPoint_card_le_five
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (hd : d ≠ 0)
    (t : sizeTwoAllowedDifference q a)
    (shift : Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1))
    (hshift : ∀ (r : SizeTwoAdmissibleTargetRow q t.1)
      (_hr : t.1 ≠ r.1 - d ∧ t.1 ≠ (r.1 - d) - 1),
      (shift r).1 = r.1 - d) :
    Fintype.card (SizeTwoDoubleShiftFixedPoint t.1 shift
      (code.reflectedPerm (x + d) t) (code.reflectedPerm x t)) ≤ 5 := by
  have hregular := sizeTwoDoubleShiftRegularFixedPoint_card_le_one
    code x d hd t shift hshift
  have hin₀ := sizeTwoDoubleShiftInputExceptionZero_card_le_one t.1 d
  have hin₁ := sizeTwoDoubleShiftInputExceptionOne_card_le_one t.1 d
  have hout₀ := sizeTwoDoubleShiftOutputExceptionZero_card_le_one t.1 d
    shift (code.reflectedPerm (x + d) t)
  have hout₁ := sizeTwoDoubleShiftOutputExceptionOne_card_le_one t.1 d
    shift (code.reflectedPerm (x + d) t)
  calc
    Fintype.card (SizeTwoDoubleShiftFixedPoint t.1 shift
        (code.reflectedPerm (x + d) t) (code.reflectedPerm x t)) ≤
        Fintype.card (SizeTwoDoubleShiftFixedPointClass code x d t shift) :=
      Fintype.card_le_of_injective
        (sizeTwoDoubleShiftFixedPointClassify code x d t shift hshift)
        (sizeTwoDoubleShiftFixedPointClassify_injective code x d t shift hshift)
    _ ≤ 5 := by
      simp only [SizeTwoDoubleShiftFixedPointClass, Fintype.card_sum]
      omega

/-- Parallel cyclic completion: the canonical comparison has at most five
fixed points. -/
theorem sizeTwoCyclicParallelDoubleShiftFixedPoint_card_le_five
    {q : ℕ} [NeZero q] {a : ZMod q}
    (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (hd : SizeTwoGenericRowShift d) :
    Fintype.card (SizeTwoDoubleShiftFixedPoint t.1
      (sizeTwoCyclicParallelRowShiftCompletion hq1 t.1 d hd)
      (code.reflectedPerm (x + d) t) (code.reflectedPerm x t)) ≤ 5 := by
  exact sizeTwoDoubleShiftFixedPoint_card_le_five code x d hd.1 t
    (sizeTwoCyclicParallelRowShiftCompletion hq1 t.1 d hd)
    (sizeTwoCyclicParallelRowShiftCompletion_apply hq1 t.1 d hd)

/-- Crossed cyclic completion: the same bound. -/
theorem sizeTwoCyclicCrossDoubleShiftFixedPoint_card_le_five
    {q : ℕ} [NeZero q] {a : ZMod q}
    (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (hd : SizeTwoGenericRowShift d) :
    Fintype.card (SizeTwoDoubleShiftFixedPoint t.1
      (sizeTwoCyclicCrossRowShiftCompletion hq1 t.1 d hd)
      (code.reflectedPerm (x + d) t) (code.reflectedPerm x t)) ≤ 5 := by
  exact sizeTwoDoubleShiftFixedPoint_card_le_five code x d hd.1 t
    (sizeTwoCyclicCrossRowShiftCompletion hq1 t.1 d hd)
    (sizeTwoCyclicCrossRowShiftCompletion_apply hq1 t.1 d hd)

end

end Erdos85

#print axioms Erdos85.SizeTwoDoubleShiftRegularFixedPoint.toReflectedAgreement
#print axioms Erdos85.sizeTwoDoubleShiftRegularFixedPoint_card_le_one
#print axioms Erdos85.sizeTwoCyclicParallelDoubleShiftRegularFixedPoint_card_le_one
#print axioms Erdos85.sizeTwoCyclicCrossDoubleShiftRegularFixedPoint_card_le_one
#print axioms Erdos85.sizeTwoDoubleShiftFixedPoint_card_le_five
#print axioms Erdos85.sizeTwoCyclicParallelDoubleShiftFixedPoint_card_le_five
#print axioms Erdos85.sizeTwoCyclicCrossDoubleShiftFixedPoint_card_le_five
