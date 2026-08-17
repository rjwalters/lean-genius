import Mathlib

/-!
# Rational square-sector terminal for the order-64 branch

For the order-16 defect block, the rational defect eigenvalues whose
adjacency-square scalars `7 - μ` are positive squares are `6`, `3`, and
`-2`, with square roots `1`, `2`, and `3`.  Write `a,b,c` for their
multiplicities and `p,q,r` for the signed differences of the positive and
negative square-root multiplicities.

The second spectral moment supplies `36a + 9b + 4c ≤ 63`; the order-16
moment cap supplies `b ≤ 3`; trace gives `p + 2q + 3r = -8`; and the cubic
color identity gives `p + 8q + 27r = -2C`.  The graph-side support theorem
gives `0 ≤ C ≤ 16`.  These linear constraints are inconsistent.
-/

namespace Erdos85

/-- Arithmetic endpoint for the rational-linear primary sectors in the
order-64 seven-component branch. -/
theorem false_of_orderSixtyFour_rationalSquareSector_constraints
    (a b c p q r colorOrder : ℤ)
    (hb : 0 ≤ b)
    (hb3 : b ≤ 3)
    (hmoment : 36 * a + 9 * b + 4 * c ≤ 63)
    (hpLower : -a ≤ p) (hpUpper : p ≤ a)
    (hqLower : -b ≤ q) (hqUpper : q ≤ b)
    (hrLower : -c ≤ r) (hrUpper : r ≤ c)
    (htrace : p + 2 * q + 3 * r = -8)
    (hcubic : p + 8 * q + 27 * r = -2 * colorOrder)
    (hcolorNonnegative : 0 ≤ colorOrder)
    (hcolorCap : colorOrder ≤ 16) : False := by
  omega

end Erdos85
