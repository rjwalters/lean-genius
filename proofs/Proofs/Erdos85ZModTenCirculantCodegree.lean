import Mathlib

/-!
# Exact codegree tables for the two C10 antipodal circulants

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

These finite, kernel-checked tables are the arithmetic input needed to turn the
order-64 service/Frobenius partition into per-class identities in the all-triangle
`6+10` sector.
-/

namespace Erdos85

/-- The first possible all-triangle C10 support, `{\u00b12, \u00b13}`. -/
def ZModTenSupportTwoThree (z : ZMod 10) : Prop :=
  z = 2 ∨ z = 3 ∨ z = 7 ∨ z = 8

/-- The second possible all-triangle C10 support, `{\u00b13, \u00b14}`. -/
def ZModTenSupportThreeFour (z : ZMod 10) : Prop :=
  z = 3 ∨ z = 4 ∨ z = 6 ∨ z = 7

instance (z : ZMod 10) : Decidable (ZModTenSupportTwoThree z) := by
  unfold ZModTenSupportTwoThree
  infer_instance

instance (z : ZMod 10) : Decidable (ZModTenSupportThreeFour z) := by
  unfold ZModTenSupportThreeFour
  infer_instance

/-- Common-neighbor count in the `{\u00b12, \u00b13}` C10 circulant.  In difference
order `0,1,...,9`, the row is `4,2,0,0,2,4,2,0,0,2`. -/
theorem zmodTen_supportTwoThree_codegree_table (i j : ZMod 10) :
    (Finset.univ.filter fun k : ZMod 10 =>
      ZModTenSupportTwoThree (k - i) ∧ ZModTenSupportTwoThree (k - j)).card =
      if j - i = 0 then 4
      else if j - i = 1 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 9 then 2
      else if j - i = 5 then 4
      else 0 := by
  revert i j
  decide

/-- Common-neighbor count in the `{\u00b13, \u00b14}` C10 circulant.  In difference
order `0,1,...,9`, the row is `4,2,1,2,1,0,1,2,1,2`. -/
theorem zmodTen_supportThreeFour_codegree_table (i j : ZMod 10) :
    (Finset.univ.filter fun k : ZMod 10 =>
      ZModTenSupportThreeFour (k - i) ∧ ZModTenSupportThreeFour (k - j)).card =
      if j - i = 0 then 4
      else if j - i = 1 ∨ j - i = 3 ∨ j - i = 7 ∨ j - i = 9 then 2
      else if j - i = 2 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 8 then 1
      else 0 := by
  revert i j
  decide

end Erdos85

#print axioms Erdos85.zmodTen_supportTwoThree_codegree_table
#print axioms Erdos85.zmodTen_supportThreeFour_codegree_table
