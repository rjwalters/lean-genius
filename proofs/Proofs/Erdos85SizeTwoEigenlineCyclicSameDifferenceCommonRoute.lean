import Proofs.Erdos85SizeTwoEigenlineCyclicPackingBound
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationReconstructionHits

/-!
# Common routed targets in one difference fiber

The reduced packing code says exactly that two distinct source bases carrying
the same difference have at most one common routed target.  This file proves
that route-level interpretation directly, without assuming looplessness or
the full cross-difference agreement law.
-/

namespace Erdos85

noncomputable section

structure SizeTwoSameDifferenceCommonRoute
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) where
  target : sizeTwoCyclicExteriorCell q a
  left : sizeTwoCyclicCodeRouteRel q a code
    (sizeTwoCyclicCellAt q a x t) target
  right : sizeTwoCyclicCodeRouteRel q a code
    (sizeTwoCyclicCellAt q a (x + d) t) target

instance SizeTwoSameDifferenceCommonRoute.instFinite
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Finite (SizeTwoSameDifferenceCommonRoute q a code x d t) :=
  Finite.of_injective SizeTwoSameDifferenceCommonRoute.target (by
    intro u v h
    cases u
    cases v
    cases h
    rfl)

noncomputable instance SizeTwoSameDifferenceCommonRoute.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Fintype (SizeTwoSameDifferenceCommonRoute q a code x d t) :=
  Fintype.ofFinite _

def sizeTwoSameDifferenceCommonRoute_leftRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (w : SizeTwoSameDifferenceCommonRoute q a code x d t) :
    SizeTwoAdmissibleTargetRow q t.1 :=
  Classical.choose
    ((sizeTwoCyclicCodeRouteRel_cellAt_iff q a code x t w.target).mp w.left)

theorem sizeTwoSameDifferenceCommonRoute_leftRow_spec
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (w : SizeTwoSameDifferenceCommonRoute q a code x d t) :
    w.target = sizeTwoCyclicCellAt q a
      (x + (sizeTwoSameDifferenceCommonRoute_leftRow code x d t w).1)
      (code.targetDifference x t
        (sizeTwoSameDifferenceCommonRoute_leftRow code x d t w)) :=
  Classical.choose_spec
    ((sizeTwoCyclicCodeRouteRel_cellAt_iff q a code x t w.target).mp w.left)

def sizeTwoSameDifferenceCommonRoute_rightRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (w : SizeTwoSameDifferenceCommonRoute q a code x d t) :
    SizeTwoAdmissibleTargetRow q t.1 :=
  Classical.choose ((sizeTwoCyclicCodeRouteRel_cellAt_iff
    q a code (x + d) t w.target).mp w.right)

theorem sizeTwoSameDifferenceCommonRoute_rightRow_spec
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (w : SizeTwoSameDifferenceCommonRoute q a code x d t) :
    w.target = sizeTwoCyclicCellAt q a
      (x + d + (sizeTwoSameDifferenceCommonRoute_rightRow code x d t w).1)
      (code.targetDifference (x + d) t
        (sizeTwoSameDifferenceCommonRoute_rightRow code x d t w)) :=
  Classical.choose_spec ((sizeTwoCyclicCodeRouteRel_cellAt_iff
    q a code (x + d) t w.target).mp w.right)

def sizeTwoSameDifferenceCommonRoute_agreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (w : SizeTwoSameDifferenceCommonRoute q a code x d t) :
    SizeTwoCrossShiftedPermutationAgreement q a
      code.toPermutationCode.perm x d t t := by
  let r₁ := sizeTwoSameDifferenceCommonRoute_leftRow code x d t w
  let r₂ := sizeTwoSameDifferenceCommonRoute_rightRow code x d t w
  have htarget := (sizeTwoSameDifferenceCommonRoute_leftRow_spec
    code x d t w).symm.trans
      (sizeTwoSameDifferenceCommonRoute_rightRow_spec code x d t w)
  have hrow : r₂.1 = r₁.1 - d := by
    have h := congrArg (fun v => (sizeTwoCyclicExteriorCellEquiv q a v).1) htarget
    simp only [sizeTwoCyclicExteriorCellEquiv_cellAt] at h
    calc
      r₂.1 = -x - d + (x + d + r₂.1) := by abel
      _ = -x - d + (x + r₁.1) := by rw [← h]
      _ = r₁.1 - d := by abel
  refine ⟨r₁, ?_, ?_⟩
  · simpa [← hrow] using r₂.2
  · have h := congrArg (fun v => v.1.2) htarget
    rw [sizeTwoCyclicCellAt_snd, sizeTwoCyclicCellAt_snd] at h
    calc
      x + (code.toPermutationCode.perm x t r₁).1 =
          x + (r₁.1 + (code.targetDifference x t r₁).1) := by
        rw [code.target_column_eq x t r₁]
      _ = x + r₁.1 + (code.targetDifference x t r₁).1 := by abel
      _ = x + d + r₂.1 +
          (code.targetDifference (x + d) t r₂).1 := h
      _ = (x + d) +
          (r₂.1 + (code.targetDifference (x + d) t r₂).1) := by abel
      _ = (x + d) + (code.toPermutationCode.perm (x + d) t r₂).1 := by
        rw [code.target_column_eq (x + d) t r₂]
      _ = (x + d) + (code.toPermutationCode.perm (x + d) t
          ⟨r₁.1 - d, by simpa [← hrow] using r₂.2⟩).1 := by
        have hre : r₂ =
            ⟨r₁.1 - d, by simpa [← hrow] using r₂.2⟩ := Subtype.ext hrow
        rw [← hre]

theorem sizeTwoSameDifferenceCommonRoute_agreement_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Function.Injective
      (sizeTwoSameDifferenceCommonRoute_agreement code x d t) := by
  intro u v huv
  have hr : sizeTwoSameDifferenceCommonRoute_leftRow code x d t u =
      sizeTwoSameDifferenceCommonRoute_leftRow code x d t v := by
    simpa [sizeTwoSameDifferenceCommonRoute_agreement] using
      congrArg (fun w => w.row) huv
  cases u with
  | mk ut ul ur =>
    cases v with
    | mk vt vl vr =>
      have ht : ut = vt := by
        calc
          ut = sizeTwoCyclicCellAt q a
              (x + (sizeTwoSameDifferenceCommonRoute_leftRow
                code x d t ⟨ut, ul, ur⟩).1)
              (code.targetDifference x t
                (sizeTwoSameDifferenceCommonRoute_leftRow
                  code x d t ⟨ut, ul, ur⟩)) :=
            sizeTwoSameDifferenceCommonRoute_leftRow_spec
              code x d t ⟨ut, ul, ur⟩
          _ = sizeTwoCyclicCellAt q a
              (x + (sizeTwoSameDifferenceCommonRoute_leftRow
                code x d t ⟨vt, vl, vr⟩).1)
              (code.targetDifference x t
                (sizeTwoSameDifferenceCommonRoute_leftRow
                  code x d t ⟨vt, vl, vr⟩)) := by rw [hr]
          _ = vt := (sizeTwoSameDifferenceCommonRoute_leftRow_spec
              code x d t ⟨vt, vl, vr⟩).symm
      cases ht
      rfl

theorem sizeTwoSameDifferenceCommonRoute_card_le_one
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicSameDifferenceCode q a)
    (x d : ZMod q) (hd : d ≠ 0)
    (t : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoSameDifferenceCommonRoute
      q a code.toReciprocalCode x d t) ≤ 1 := by
  calc
    Fintype.card (SizeTwoSameDifferenceCommonRoute
        q a code.toReciprocalCode x d t) ≤
        Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
          code.toReciprocalCode.toPermutationCode.perm x d t t) :=
      Fintype.card_le_of_injective
        (sizeTwoSameDifferenceCommonRoute_agreement
          code.toReciprocalCode x d t)
        (sizeTwoSameDifferenceCommonRoute_agreement_injective
          code.toReciprocalCode x d t)
    _ ≤ 1 := code.same_difference_agreement_le_one x d hd t

end

end Erdos85

#print axioms Erdos85.sizeTwoSameDifferenceCommonRoute_card_le_one
