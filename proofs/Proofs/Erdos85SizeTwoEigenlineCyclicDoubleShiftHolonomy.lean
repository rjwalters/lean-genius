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

/-- Group-theoretic normal form of the double-shift comparison. -/
theorem sizeTwoDoubleShiftComparison_eq_mul
    {A : Type*} (shift next base : Equiv.Perm A) :
    sizeTwoDoubleShiftComparison shift next base =
      base⁻¹ * shift * next * shift := by
  ext r
  rfl

/-- The frame obtained after absorbing `i` copies of the two-sided shift. -/
def sizeTwoTwistedFrame
    {A : Type*} (shift : Equiv.Perm A) (frame : ℕ → Equiv.Perm A)
    (i : ℕ) : Equiv.Perm A :=
  shift ^ i * frame i * shift ^ i

/-- Each conjugated comparison is the ordinary multiplicative difference
of two consecutive twisted frames. -/
theorem sizeTwoDoubleShiftComparison_conj_eq_twistedFrame_div
    {A : Type*} (shift : Equiv.Perm A) (frame : ℕ → Equiv.Perm A)
    (i : ℕ) :
    (shift ^ i)⁻¹ *
        sizeTwoDoubleShiftComparison shift (frame (i + 1)) (frame i) *
        shift ^ i =
      (sizeTwoTwistedFrame shift frame i)⁻¹ *
        sizeTwoTwistedFrame shift frame (i + 1) := by
  rw [sizeTwoDoubleShiftComparison_eq_mul]
  simp only [sizeTwoTwistedFrame, pow_succ']
  group

/-- Ordered product of the conjugated comparisons along the first `n`
steps. -/
def sizeTwoTwistedComparisonProduct
    {A : Type*} (shift : Equiv.Perm A) (frame : ℕ → Equiv.Perm A) :
    ℕ → Equiv.Perm A
  | 0 => 1
  | n + 1 => sizeTwoTwistedComparisonProduct shift frame n *
      ((shift ^ n)⁻¹ *
        sizeTwoDoubleShiftComparison shift (frame (n + 1)) (frame n) *
        shift ^ n)

/-- Exact telescoping formula: the ordered twisted holonomy is the relative
permutation between its endpoint frames. -/
theorem sizeTwoTwistedComparisonProduct_eq_endpoints
    {A : Type*} (shift : Equiv.Perm A) (frame : ℕ → Equiv.Perm A) :
    ∀ n : ℕ,
    sizeTwoTwistedComparisonProduct shift frame n =
      (sizeTwoTwistedFrame shift frame 0)⁻¹ *
        sizeTwoTwistedFrame shift frame n := by
  intro n
  induction n with
  | zero => simp [sizeTwoTwistedComparisonProduct]
  | succ n ih =>
      rw [sizeTwoTwistedComparisonProduct, ih,
        sizeTwoDoubleShiftComparison_conj_eq_twistedFrame_div]
      group

/-- If both the frame and the completed shift close after `n` steps, the
twisted holonomy product is the identity. -/
theorem sizeTwoTwistedComparisonProduct_eq_one_of_closes
    {A : Type*} (shift : Equiv.Perm A) (frame : ℕ → Equiv.Perm A)
    (n : ℕ) (hshift : shift ^ n = 1) (hframe : frame n = frame 0) :
    sizeTwoTwistedComparisonProduct shift frame n = 1 := by
  rw [sizeTwoTwistedComparisonProduct_eq_endpoints]
  simp [sizeTwoTwistedFrame, hshift, hframe]

end

end Erdos85

#print axioms Erdos85.sizeTwoDoubleShiftComparison_sign_product_eq_one
#print axioms Erdos85.sizeTwoCyclicParallelDoubleShift_sign_product_eq_one
#print axioms Erdos85.sizeTwoCyclicCrossDoubleShift_sign_product_eq_one
#print axioms Erdos85.sizeTwoDoubleShiftComparison_eq_mul
#print axioms Erdos85.sizeTwoDoubleShiftComparison_conj_eq_twistedFrame_div
#print axioms Erdos85.sizeTwoTwistedComparisonProduct_eq_endpoints
#print axioms Erdos85.sizeTwoTwistedComparisonProduct_eq_one_of_closes
