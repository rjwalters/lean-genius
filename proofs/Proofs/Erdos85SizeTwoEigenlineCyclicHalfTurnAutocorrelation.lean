import Proofs.Erdos85SizeTwoEigenlineCyclicCentralFiberSubsystem

/-!
# Reversal symmetry for cyclic agreement correlations

The agreement statistic compares routes based at `x` and `x + d`.  Swapping
the two sources identifies it with the statistic based at `x + d` and shift
`-d`.  At `q = 8` and `d = 4`, this is the antipodal symmetry observed in the
minimized Boolean core: the half-turn agreement counts at `x` and `x + 4`
are exactly equal.
-/

namespace Erdos85

noncomputable section

/-- Swap the two source cells in a shifted-permutation agreement. -/
def sizeTwoCrossShiftedPermutationAgreementSwapEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (x d : ZMod q) (t u : sizeTwoAllowedDifference q a) :
    SizeTwoCrossShiftedPermutationAgreement q a P x d t u ≃
      SizeTwoCrossShiftedPermutationAgreement q a P (x + d) (-d) u t where
  toFun w :=
    { row := ⟨w.row.1 - d, w.shifted_admissible⟩
      shifted_admissible := by
        simpa only [sub_neg_eq_add, sub_add_cancel] using w.row.2
      column_eq := by
        convert w.column_eq.symm using 1 <;>
          simp [sub_neg_eq_add] }
  invFun w :=
    { row := ⟨w.row.1 + d, by
          simpa only [sub_neg_eq_add, add_sub_cancel_right] using
            w.shifted_admissible⟩
      shifted_admissible := by
        simpa only [add_sub_cancel_right] using w.row.2
      column_eq := by
        convert w.column_eq.symm using 1 <;>
          simp [sub_neg_eq_add] }
  left_inv w := by
    apply SizeTwoCrossShiftedPermutationAgreement.row_injective
    apply Subtype.ext
    simp
  right_inv w := by
    apply SizeTwoCrossShiftedPermutationAgreement.row_injective
    apply Subtype.ext
    simp

/-- Agreement cardinality is invariant under reversing the source pair. -/
theorem sizeTwoCrossShiftedPermutationAgreement_card_swap
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (x d : ZMod q) (t u : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a P x d t u) =
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P (x + d) (-d) u t) := by
  exact Fintype.card_congr
    (sizeTwoCrossShiftedPermutationAgreementSwapEquiv P x d t u)

/-- At any self-negative shift, the same-difference agreement count is
constant on the two-point translation orbit.  This is the q-generic
half-turn symmetry; no arithmetic specialization of `q` is needed. -/
theorem sizeTwoCrossShiftedPermutationAgreement_card_selfNegShift
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (x d : ZMod q) (hd : -d = d)
    (t : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a P x d t t) =
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P (x + d) d t t) := by
  simpa only [hd] using
    (sizeTwoCrossShiftedPermutationAgreement_card_swap P x d t t)

/-- Additive form of the q-generic half-turn symmetry: a translation pair
contributes twice either member's agreement count. -/
theorem sizeTwoCrossShiftedPermutationAgreement_card_selfNegShift_pair
    {q : ℕ} [NeZero q] {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (x d : ZMod q) (hd : -d = d)
    (t : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P x d t t) +
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P (x + d) d t t) =
      2 * Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        q a P x d t t) := by
  rw [
    ← sizeTwoCrossShiftedPermutationAgreement_card_selfNegShift
      P x d hd t,
    two_mul]

/-- The canonical half-turn in every nontrivial even cyclic group is
self-negative. -/
theorem zmodEven_neg_half (m : ℕ) [NeZero m] :
    -(m : ZMod (2 * m)) = m := by
  rw [ZMod.neg_eq_self_iff]
  right
  have hm : 0 < m := NeZero.pos m
  rw [ZMod.val_natCast]
  simp only [Nat.mod_eq_of_lt (by omega : m < 2 * m)]

/-- In `ZMod 8`, the half-turn is its own negative. -/
theorem zmodEight_neg_four : -(4 : ZMod 8) = 4 := by decide

/-- The q=8 half-turn autocorrelation count is antipodally symmetric in the
base point.  This is the exact formal counterpart of the `x ↦ x + 4`
symmetry seen in the minimized q=8 models. -/
theorem sizeTwoCrossShiftedPermutationAgreement_card_halfTurn_eight
    (P : SizeTwoCyclicPermutationFamily 8 (1 : ZMod 8))
    (x : ZMod 8)
    (t : sizeTwoAllowedDifference 8 (1 : ZMod 8)) :
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      8 (1 : ZMod 8) P x 4 t t) =
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        8 (1 : ZMod 8) P (x + 4) 4 t t) := by
  exact sizeTwoCrossShiftedPermutationAgreement_card_selfNegShift
    P x 4 zmodEight_neg_four t

/-- Each antipodal pair contributes twice either member's half-turn agreement
count.  This packages the symmetry in the additive form needed by a global
autocorrelation census. -/
theorem sizeTwoCrossShiftedPermutationAgreement_card_halfTurn_pair_eight
    (P : SizeTwoCyclicPermutationFamily 8 (1 : ZMod 8))
    (x : ZMod 8)
    (t : sizeTwoAllowedDifference 8 (1 : ZMod 8)) :
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        8 (1 : ZMod 8) P x 4 t t) +
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        8 (1 : ZMod 8) P (x + 4) 4 t t) =
      2 * Fintype.card (SizeTwoCrossShiftedPermutationAgreement
        8 (1 : ZMod 8) P x 4 t t) := by
  exact sizeTwoCrossShiftedPermutationAgreement_card_selfNegShift_pair
    P x 4 zmodEight_neg_four t

end

end Erdos85

#print axioms Erdos85.sizeTwoCrossShiftedPermutationAgreement_card_swap
#print axioms Erdos85.sizeTwoCrossShiftedPermutationAgreement_card_selfNegShift
#print axioms Erdos85.sizeTwoCrossShiftedPermutationAgreement_card_selfNegShift_pair
#print axioms Erdos85.zmodEven_neg_half
#print axioms Erdos85.sizeTwoCrossShiftedPermutationAgreement_card_halfTurn_eight
#print axioms Erdos85.sizeTwoCrossShiftedPermutationAgreement_card_halfTurn_pair_eight
