import Mathlib

/-!
# Symmetric two-element supports on the odd offsets of ZMod 10

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

After excluding the ambient-cycle offsets `±1`, a negation-invariant
two-element support on the odd residues can only be `{±3}`.  The remaining
odd residue `5` is fixed by negation and therefore cannot by itself supply a
two-element orbit.
-/

namespace Erdos85

set_option maxRecDepth 100000

/-- A symmetric Boolean support of size two contained in the odd offsets of
`ZMod 10`, and avoiding the cycle offsets `±1`, is exactly `{±3}`. -/
theorem zmodTen_symmetric_odd_two_support_eq_three_seven
    (f : ZMod 10 → Bool)
    (hneg : ∀ z, f (-z) = f z)
    (hcard : ((Finset.univ : Finset (ZMod 10)).filter fun z => f z).card = 2)
    (hallowed : ∀ z, f z = true → z = 3 ∨ z = 5 ∨ z = 7) :
    ∀ z, f z = true ↔ z = 3 ∨ z = 7 := by
  revert f
  decide

end Erdos85

#print axioms Erdos85.zmodTen_symmetric_odd_two_support_eq_three_seven
