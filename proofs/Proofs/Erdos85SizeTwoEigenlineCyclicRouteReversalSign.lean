import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationInvolution
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingCounts
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Sign of cyclic route reversal

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

The most canonical sign candidate on the base-resolved system is reversal of
all routed darts.  This file computes its sign.  For `4 ∣ q` the dart count
has an even number of reversal pairs, so this global involution is even.  Thus
its sign alone cannot strengthen the binary sharp-profile census; any useful
sign obstruction must retain finer line or base data.
-/

namespace Erdos85

noncomputable section

/-- Routed darts are the sigma type of a base, an allowed difference, and an
admissible relative row. -/
def sizeTwoCyclicRouteDartEquivSigma
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    SizeTwoCyclicRouteDart q a code ≃
      Σ _x : ZMod q, Σ t : sizeTwoAllowedDifference q a,
        SizeTwoAdmissibleTargetRow q t.1 where
  toFun e := ⟨e.1.1, e.1.2.1, ⟨e.1.2.2, e.2⟩⟩
  invFun e := ⟨(e.1, (e.2.1, e.2.2.1)), e.2.2.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

noncomputable instance SizeTwoCyclicRouteDart.instFintype
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    Fintype (SizeTwoCyclicRouteDart q a code) :=
  Fintype.ofEquiv _ (sizeTwoCyclicRouteDartEquivSigma q a code).symm

noncomputable instance SizeTwoCyclicRouteDart.instDecidableEq
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    DecidableEq (SizeTwoCyclicRouteDart q a code) := Classical.decEq _

/-- Exact number of routed darts in the nondegenerate size-two subsystem. -/
theorem sizeTwoCyclicRouteDart_card
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0) :
    Fintype.card (SizeTwoCyclicRouteDart q a code) =
      q * (q - 2) * (q - 2) := by
  rw [Fintype.card_congr (sizeTwoCyclicRouteDartEquivSigma q a code),
    Fintype.card_sigma]
  simp_rw [Fintype.card_sigma,
    sizeTwoAdmissibleTargetRow_card q _ hq1]
  simp [sizeTwoAllowedDifference_card q a ha, ZMod.card, Nat.mul_assoc]

/-- When `4 ∣ q`, global routed-dart reversal is an even permutation.

This is a negative diagnostic for the packing-bound program: the unrefined
global reversal sign is forced to `+1`, not to a contradictory value. -/
theorem sizeTwoCyclicRouteDartReverseEquiv_sign_eq_one
    {q : ℕ} [NeZero q] (h4q : 4 ∣ q) {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless) :
    Equiv.Perm.sign (sizeTwoCyclicRouteDartReverseEquiv q a code) = 1 := by
  classical
  let σ := sizeTwoCyclicRouteDartReverseEquiv q a code
  have hq1 : (1 : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.one_eq_zero_iff]
    intro hq
    subst q
    norm_num at h4q
  have ha : a ≠ -1 - a := by
    intro h
    have htwoa : 2 * a = -1 := by
      have := congrArg (fun z : ZMod q => z + a) h
      simpa [two_mul] using this
    have h2q : 2 ∣ q := dvd_trans (by norm_num : 2 ∣ 4) h4q
    let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
    have hφtwo : φ (2 : ZMod q) = 0 := by
      rw [show (2 : ZMod q) = 1 + 1 by norm_num, map_add, map_one]
      exact CharTwo.two_eq_zero
    have hzeroone : (0 : ZMod 2) = 1 := by
      calc
        0 = φ (2 * a) := by rw [map_mul, hφtwo, zero_mul]
        _ = φ (-1) := congrArg φ htwoa
        _ = 1 := by norm_num
    exact zero_ne_one hzeroone
  have hσpow : σ ^ 2 = 1 := by
    apply Equiv.ext
    intro e
    exact SizeTwoCyclicRouteDart.reverse_reverse e
  rw [Equiv.Perm.sign_of_pow_two_eq_one hσpow]
  have hfixed : Fintype.card (Function.fixedPoints σ) = 0 := by
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun e =>
      (Erdos85.SizeTwoCyclicRouteDart.reverse_ne hloop e.1) e.2⟩
  rw [hfixed, Nat.sub_zero,
    sizeTwoCyclicRouteDart_card q a code ha hq1]
  obtain ⟨k, rfl⟩ := h4q
  let n := k * (4 * k - 2) * (4 * k - 2)
  have hproduct : 4 * k * (4 * k - 2) * (4 * k - 2) = 4 * n := by
    simp [n, Nat.mul_assoc]
  rw [hproduct, show 4 * n / 2 = 2 * n by omega]
  simp

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRouteDart_card
#print axioms Erdos85.sizeTwoCyclicRouteDartReverseEquiv_sign_eq_one
