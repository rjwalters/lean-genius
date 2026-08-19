import Mathlib

/-!
# Symmetric two-element supports on the even offsets of ZMod 10

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The four nonzero even offsets split into the two negation orbits
`{±2}` and `{±4}`.  Consequently a symmetric support of cardinal two is
exactly one of those pairs.  This is the finite core of the all-triangle-free
`C10` same-sign diagonal-block classification.
-/

namespace Erdos85

set_option maxRecDepth 100000

/-- A symmetric Boolean support of size two contained in the nonzero even
offsets of `ZMod 10` is exactly `{±2}` or `{±4}`. -/
theorem zmodTen_symmetric_even_two_support
    (f : ZMod 10 → Bool)
    (hzero : f 0 = false)
    (hneg : ∀ z, f (-z) = f z)
    (hcard : ((Finset.univ : Finset (ZMod 10)).filter fun z => f z).card = 2)
    (heven : ∀ z, f z = true → z = 2 ∨ z = 4 ∨ z = 6 ∨ z = 8) :
    (∀ z, f z = true ↔ z = 2 ∨ z = 8) ∨
      (∀ z, f z = true ↔ z = 4 ∨ z = 6) := by
  revert f
  decide

end Erdos85

#print axioms Erdos85.zmodTen_symmetric_even_two_support
