import Proofs.Erdos85SizeTwoEigenlineCyclicDoubleShiftFixedPoints

/-!
# Graded holonomy of double-shift comparisons

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

The sign of the comparison from base `x` to base `x+d` is the product of
the two endpoint reflected-permutation signs.  Multiplying around all bases,
translation merely reindexes one factor, so every local sign occurs twice
and the total graded holonomy is `+1`.
-/

namespace Erdos85

noncomputable section

/-- Abstract graded holonomy identity for a translated family of
permutations. -/
theorem sizeTwoDoubleShiftComparison_sign_product_eq_one
    {X A : Type*} [Fintype X] [DecidableEq X] [AddGroup X]
    [Fintype A] [DecidableEq A]
    (d : X) (shift : Equiv.Perm A) (frame : X → Equiv.Perm A) :
    (∏ x : X, Equiv.Perm.sign
      (sizeTwoDoubleShiftComparison shift (frame (x + d)) (frame x))) = 1 := by
  simp_rw [sizeTwoDoubleShiftComparison_sign]
  rw [Finset.prod_mul_distrib]
  have hreindex : (∏ x : X, Equiv.Perm.sign (frame (x + d))) =
      ∏ x : X, Equiv.Perm.sign (frame x) := by
    exact Function.Bijective.prod_comp (Equiv.addRight d).bijective
      (fun x : X => Equiv.Perm.sign (frame x))
  rw [hreindex, Int.units_mul_self]

/-- Parallel cyclic completion: the product of comparison signs around all
bases is even. -/
theorem sizeTwoCyclicParallelDoubleShift_sign_product_eq_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (d : ZMod q) (t : sizeTwoAllowedDifference q a)
    [DecidableEq (SizeTwoAdmissibleTargetRow q t.1)]
    (hd : SizeTwoGenericRowShift d) :
    (∏ x : ZMod q, Equiv.Perm.sign
      (sizeTwoDoubleShiftComparison
        (sizeTwoCyclicParallelRowShiftCompletion hq1 t.1 d hd)
        (code.reflectedPerm (x + d) t) (code.reflectedPerm x t))) = 1 := by
  exact sizeTwoDoubleShiftComparison_sign_product_eq_one d
    (sizeTwoCyclicParallelRowShiftCompletion hq1 t.1 d hd)
    (fun x => code.reflectedPerm x t)

/-- Crossed completion gives the identical graded holonomy. -/
theorem sizeTwoCyclicCrossDoubleShift_sign_product_eq_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (d : ZMod q) (t : sizeTwoAllowedDifference q a)
    [DecidableEq (SizeTwoAdmissibleTargetRow q t.1)]
    (hd : SizeTwoGenericRowShift d) :
    (∏ x : ZMod q, Equiv.Perm.sign
      (sizeTwoDoubleShiftComparison
        (sizeTwoCyclicCrossRowShiftCompletion hq1 t.1 d hd)
        (code.reflectedPerm (x + d) t) (code.reflectedPerm x t))) = 1 := by
  exact sizeTwoDoubleShiftComparison_sign_product_eq_one d
    (sizeTwoCyclicCrossRowShiftCompletion hq1 t.1 d hd)
    (fun x => code.reflectedPerm x t)

end

end Erdos85

#print axioms Erdos85.sizeTwoDoubleShiftComparison_sign_product_eq_one
#print axioms Erdos85.sizeTwoCyclicParallelDoubleShift_sign_product_eq_one
#print axioms Erdos85.sizeTwoCyclicCrossDoubleShift_sign_product_eq_one
