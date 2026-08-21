import Proofs.Erdos85TwoHolePermutationCompletion

/-!
# Two-hole completion of cyclic row translation

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

For a generic nonzero shift `d ∉ {1,-1}`, translation `r ↦ r-d` moves
both forbidden rows `{t,t+1}` away from the old holes.  The abstract
two-hole construction therefore gives two permutations of the admissible
row set.  They agree with translation on every common admissible row and
have opposite relative sign.
-/

namespace Erdos85

noncomputable section

/-- The routing row predicate is the complement of the two consecutive
holes `t,t+1`. -/
def sizeTwoAdmissibleTargetRowEquivTwoHole
    (q : ℕ) (t : ZMod q) :
    SizeTwoAdmissibleTargetRow q t ≃
      TwoHoleComplement (ZMod q) t (t + 1) where
  toFun r := ⟨r.1, by
    constructor
    · exact fun h => r.2.1 h.symm
    · intro h
      apply r.2.2
      rw [h]
      abel⟩
  invFun r := ⟨r.1, by
    constructor
    · exact fun h => r.2.1 h.symm
    · intro h
      apply r.2.2
      have := congrArg (fun z : ZMod q => z + 1) h
      simpa using this.symm⟩
  left_inv r := by cases r; rfl
  right_inv r := by cases r; rfl

/-- A shift is generic for the two-hole construction when it is neither
zero nor adjacent to zero. -/
def SizeTwoGenericRowShift {q : ℕ} (d : ZMod q) : Prop :=
  d ≠ 0 ∧ d ≠ 1 ∧ d ≠ -1

private theorem cyclic_holes_ne
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0) (t : ZMod q) :
    t ≠ t + 1 := by
  intro h
  apply hq1
  have := congrArg (fun z : ZMod q => z - t) h
  simpa using this.symm

private structure CyclicShiftHoleData
    {q : ℕ} (t d : ZMod q) where
  hholes : t ≠ t + 1
  hcross : (Equiv.subRight d) t ≠ (Equiv.subRight d) (t + 1)
  h₀₀ : (Equiv.subRight d) t ≠ t
  h₀₁ : (Equiv.subRight d) t ≠ t + 1
  h₁₀ : (Equiv.subRight d) (t + 1) ≠ t
  h₁₁ : (Equiv.subRight d) (t + 1) ≠ t + 1

private def cyclicShiftHoleData
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0)
    (t d : ZMod q) (hd : SizeTwoGenericRowShift d) :
    CyclicShiftHoleData t d := by
  have hholes := cyclic_holes_ne hq1 t
  refine {
    hholes := hholes
    hcross := (Equiv.subRight d).injective.ne hholes
    h₀₀ := ?_
    h₀₁ := ?_
    h₁₀ := ?_
    h₁₁ := ?_ }
  · intro h
    apply hd.1
    have h' : t - d = t := by simpa using h
    calc
      d = t - (t - d) := by abel
      _ = t - t := by rw [h']
      _ = 0 := sub_self t
  · intro h
    apply hd.2.2
    have h' : t - d = t + 1 := by simpa using h
    calc
      d = t - (t - d) := by abel
      _ = t - (t + 1) := by rw [h']
      _ = -1 := by abel
  · intro h
    apply hd.2.1
    have h' : (t + 1) - d = t := by simpa using h
    calc
      d = (t + 1) - ((t + 1) - d) := by abel
      _ = (t + 1) - t := by rw [h']
      _ = 1 := by abel
  · intro h
    apply hd.1
    have h' : (t + 1) - d = t + 1 := by simpa using h
    calc
      d = (t + 1) - ((t + 1) - d) := by abel
      _ = (t + 1) - (t + 1) := by rw [h']
      _ = 0 := sub_self (t + 1)

/-- The parallel completion of row translation `r ↦ r-d`. -/
def sizeTwoCyclicParallelRowShiftCompletion
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0)
    (t d : ZMod q) (hd : SizeTwoGenericRowShift d) :
    Equiv.Perm (SizeTwoAdmissibleTargetRow q t) := by
  let tau : Equiv.Perm (ZMod q) := Equiv.subRight d
  let H := cyclicShiftHoleData hq1 t d hd
  let completion := twoHoleParallelCompletion tau t (t + 1)
    H.hholes H.hcross H.h₀₀ H.h₀₁ H.h₁₀ H.h₁₁
  exact ((sizeTwoAdmissibleTargetRowEquivTwoHole q t).trans completion).trans
    (sizeTwoAdmissibleTargetRowEquivTwoHole q t).symm

/-- The crossed completion of the same partial translation. -/
def sizeTwoCyclicCrossRowShiftCompletion
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0)
    (t d : ZMod q) (hd : SizeTwoGenericRowShift d) :
    Equiv.Perm (SizeTwoAdmissibleTargetRow q t) := by
  let tau : Equiv.Perm (ZMod q) := Equiv.subRight d
  let H := cyclicShiftHoleData hq1 t d hd
  let completion := twoHoleCrossCompletion tau t (t + 1)
    H.hholes H.hcross H.h₀₀ H.h₀₁ H.h₁₀ H.h₁₁
  exact ((sizeTwoAdmissibleTargetRowEquivTwoHole q t).trans completion).trans
    (sizeTwoAdmissibleTargetRowEquivTwoHole q t).symm

/-- On the common row domain, the parallel completion is literally
translation by `-d`. -/
theorem sizeTwoCyclicParallelRowShiftCompletion_apply
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0)
    (t d : ZMod q) (hd : SizeTwoGenericRowShift d)
    (r : SizeTwoAdmissibleTargetRow q t)
    (hshift : t ≠ r.1 - d ∧ t ≠ (r.1 - d) - 1) :
    (sizeTwoCyclicParallelRowShiftCompletion hq1 t d hd r).1 = r.1 - d := by
  let tau : Equiv.Perm (ZMod q) := Equiv.subRight d
  let H := cyclicShiftHoleData hq1 t d hd
  let r' := sizeTwoAdmissibleTargetRowEquivTwoHole q t r
  have hr₀ : tau r'.1 ≠ t := by
    change r.1 - d ≠ t
    exact hshift.1.symm
  have hr₁ : tau r'.1 ≠ t + 1 := by
    change r.1 - d ≠ t + 1
    intro h
    apply hshift.2
    rw [h]
    abel
  unfold sizeTwoCyclicParallelRowShiftCompletion
  dsimp only
  simp only [Equiv.trans_apply]
  exact twoHoleParallelCompletion_apply_of_image_avoids tau t (t + 1)
    H.hholes H.hcross H.h₀₀ H.h₀₁ H.h₁₀ H.h₁₁ r' hr₀ hr₁

/-- The crossed completion has the same action on common rows. -/
theorem sizeTwoCyclicCrossRowShiftCompletion_apply
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0)
    (t d : ZMod q) (hd : SizeTwoGenericRowShift d)
    (r : SizeTwoAdmissibleTargetRow q t)
    (hshift : t ≠ r.1 - d ∧ t ≠ (r.1 - d) - 1) :
    (sizeTwoCyclicCrossRowShiftCompletion hq1 t d hd r).1 = r.1 - d := by
  let tau : Equiv.Perm (ZMod q) := Equiv.subRight d
  let H := cyclicShiftHoleData hq1 t d hd
  let r' := sizeTwoAdmissibleTargetRowEquivTwoHole q t r
  have hr₀ : tau r'.1 ≠ t := by
    change r.1 - d ≠ t
    exact hshift.1.symm
  have hr₁ : tau r'.1 ≠ t + 1 := by
    change r.1 - d ≠ t + 1
    intro h
    apply hshift.2
    rw [h]
    abel
  unfold sizeTwoCyclicCrossRowShiftCompletion
  dsimp only
  simp only [Equiv.trans_apply]
  exact twoHoleCrossCompletion_apply_of_image_avoids tau t (t + 1)
    H.hholes H.hcross H.h₀₀ H.h₀₁ H.h₁₀ H.h₁₁ r' hr₀ hr₁

/-- The two cyclic row-shift completions differ by an odd permutation. -/
theorem sizeTwoCyclicRowShiftCompletion_relative_sign
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0)
    (t d : ZMod q) [DecidableEq (SizeTwoAdmissibleTargetRow q t)]
    (hd : SizeTwoGenericRowShift d) :
    Equiv.Perm.sign
      ((sizeTwoCyclicCrossRowShiftCompletion hq1 t d hd).trans
        (sizeTwoCyclicParallelRowShiftCompletion hq1 t d hd).symm) = -1 := by
  classical
  let tau : Equiv.Perm (ZMod q) := Equiv.subRight d
  let H := cyclicShiftHoleData hq1 t d hd
  let E := sizeTwoAdmissibleTargetRowEquivTwoHole q t
  let P := twoHoleParallelCompletion tau t (t + 1)
    H.hholes H.hcross H.h₀₀ H.h₀₁ H.h₁₀ H.h₁₁
  let C := twoHoleCrossCompletion tau t (t + 1)
    H.hholes H.hcross H.h₀₀ H.h₀₁ H.h₁₀ H.h₁₁
  have hparallel : sizeTwoCyclicParallelRowShiftCompletion hq1 t d hd =
      (E.trans P).trans E.symm := by
    rfl
  have hcross : sizeTwoCyclicCrossRowShiftCompletion hq1 t d hd =
      (E.trans C).trans E.symm := by
    rfl
  rw [hparallel, hcross]
  have hrelative :
      (((E.trans C).trans E.symm).trans
        ((E.trans P).trans E.symm).symm) =
      (E.trans (C.trans P.symm)).trans E.symm := by
    ext r
    simp
  rw [hrelative, Equiv.Perm.sign_trans_trans_symm]
  exact twoHoleCompletion_relative_sign tau t (t + 1)
    H.hholes H.hcross H.h₀₀ H.h₀₁ H.h₁₀ H.h₁₁

/-- Shift both the input and output coordinates of a permutation comparison
by the same completed row translation. -/
def sizeTwoDoubleShiftComparison
    {A : Type*} (shift next base : Equiv.Perm A) : Equiv.Perm A :=
  (((shift.trans next).trans shift).trans base.symm)

/-- The completion sign occurs twice and cancels.  Hence the double-shift
comparison sign is canonical even though either individual hole completion
can be toggled by a transposition. -/
theorem sizeTwoDoubleShiftComparison_sign
    {A : Type*} [Fintype A] [DecidableEq A]
    (shift next base : Equiv.Perm A) :
    Equiv.Perm.sign (sizeTwoDoubleShiftComparison shift next base) =
      Equiv.Perm.sign next * Equiv.Perm.sign base := by
  rw [sizeTwoDoubleShiftComparison, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_symm, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_trans]
  calc
    Equiv.Perm.sign base *
          (Equiv.Perm.sign shift *
            (Equiv.Perm.sign next * Equiv.Perm.sign shift)) =
        (Equiv.Perm.sign shift * Equiv.Perm.sign shift) *
          (Equiv.Perm.sign next * Equiv.Perm.sign base) := by
      ac_rfl
    _ = Equiv.Perm.sign next * Equiv.Perm.sign base := by
      rw [Int.units_mul_self, one_mul]

/-- In particular, the parallel and crossed cyclic completions give the
same graded comparison sign. -/
theorem sizeTwoCyclicDoubleShiftComparison_sign_independent
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0)
    (t d : ZMod q) [DecidableEq (SizeTwoAdmissibleTargetRow q t)]
    (hd : SizeTwoGenericRowShift d)
    (next base : Equiv.Perm (SizeTwoAdmissibleTargetRow q t)) :
    Equiv.Perm.sign (sizeTwoDoubleShiftComparison
        (sizeTwoCyclicParallelRowShiftCompletion hq1 t d hd) next base) =
      Equiv.Perm.sign (sizeTwoDoubleShiftComparison
        (sizeTwoCyclicCrossRowShiftCompletion hq1 t d hd) next base) := by
  rw [sizeTwoDoubleShiftComparison_sign,
    sizeTwoDoubleShiftComparison_sign]

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicParallelRowShiftCompletion_apply
#print axioms Erdos85.sizeTwoCyclicCrossRowShiftCompletion_apply
#print axioms Erdos85.sizeTwoCyclicRowShiftCompletion_relative_sign
#print axioms Erdos85.sizeTwoDoubleShiftComparison_sign
#print axioms Erdos85.sizeTwoCyclicDoubleShiftComparison_sign_independent
