import Mathlib

/-!
# The size-two shore-switch arithmetic

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3.

After the signed normal-form collapse, negating the eigenline on one of the
two internal shores preserves the common parameters `k` and `r`.  If the old
defect eigenvalue is `mu`, the new one is

`mu - 2 * (7 + mu - 2*k - r)`.

This file records the involution and the complete tables for the three
remaining negative eigenvalue lanes.  The graph-facing switch theorem can
therefore route cases through these checked arithmetic identities.
-/

namespace Erdos85

/-- Defect eigenvalue produced by changing the sign of one shore in the
order-64 size-two normal form. -/
def sizeTwoMuSwitchTarget (mu k r : ℤ) : ℤ :=
  mu - 2 * (7 + mu - 2 * k - r)

/-- Changing the shore sign twice restores the original eigenvalue. -/
theorem sizeTwoMuSwitchTarget_involutive (mu k r : ℤ) :
    sizeTwoMuSwitchTarget (sizeTwoMuSwitchTarget mu k r) k r = mu := by
  simp only [sizeTwoMuSwitchTarget]
  ring

/-- The self-switching cells are exactly one affine hyperplane. -/
theorem sizeTwoMuSwitchTarget_eq_self_iff (mu k r : ℤ) :
    sizeTwoMuSwitchTarget mu k r = mu ↔ mu = 2 * k + r - 7 := by
  simp only [sizeTwoMuSwitchTarget]
  constructor <;> intro h <;> omega

/-- Complete post-collapse switch table in the `mu=-1` lane. -/
theorem sizeTwoMuSwitchTarget_negOne_table :
    sizeTwoMuSwitchTarget (-1) 0 3 = -7 ∧
    sizeTwoMuSwitchTarget (-1) 0 4 = -5 ∧
    sizeTwoMuSwitchTarget (-1) 0 5 = -3 ∧
    sizeTwoMuSwitchTarget (-1) 0 6 = -1 ∧
    sizeTwoMuSwitchTarget (-1) 0 7 = 1 ∧
    sizeTwoMuSwitchTarget (-1) 1 2 = -5 ∧
    sizeTwoMuSwitchTarget (-1) 1 3 = -3 ∧
    sizeTwoMuSwitchTarget (-1) 1 4 = -1 ∧
    sizeTwoMuSwitchTarget (-1) 1 5 = 1 ∧
    sizeTwoMuSwitchTarget (-1) 1 6 = 3 := by
  norm_num [sizeTwoMuSwitchTarget]

/-- Complete post-collapse switch table in the `mu=-3` lane. -/
theorem sizeTwoMuSwitchTarget_negThree_table :
    sizeTwoMuSwitchTarget (-3) 0 3 = -5 ∧
    sizeTwoMuSwitchTarget (-3) 0 4 = -3 ∧
    sizeTwoMuSwitchTarget (-3) 0 5 = -1 ∧
    sizeTwoMuSwitchTarget (-3) 0 6 = 1 ∧
    sizeTwoMuSwitchTarget (-3) 1 2 = -3 ∧
    sizeTwoMuSwitchTarget (-3) 1 3 = -1 ∧
    sizeTwoMuSwitchTarget (-3) 1 4 = 1 ∧
    sizeTwoMuSwitchTarget (-3) 1 5 = 3 := by
  norm_num [sizeTwoMuSwitchTarget]

/-- Complete post-collapse switch table in the `mu=-5` lane. -/
theorem sizeTwoMuSwitchTarget_negFive_table :
    sizeTwoMuSwitchTarget (-5) 0 3 = -3 ∧
    sizeTwoMuSwitchTarget (-5) 0 4 = -1 ∧
    sizeTwoMuSwitchTarget (-5) 0 5 = 1 ∧
    sizeTwoMuSwitchTarget (-5) 1 2 = -1 ∧
    sizeTwoMuSwitchTarget (-5) 1 3 = 1 ∧
    sizeTwoMuSwitchTarget (-5) 1 4 = 3 := by
  norm_num [sizeTwoMuSwitchTarget]

end Erdos85

#print axioms Erdos85.sizeTwoMuSwitchTarget_involutive
#print axioms Erdos85.sizeTwoMuSwitchTarget_eq_self_iff
#print axioms Erdos85.sizeTwoMuSwitchTarget_negOne_table
#print axioms Erdos85.sizeTwoMuSwitchTarget_negThree_table
#print axioms Erdos85.sizeTwoMuSwitchTarget_negFive_table
