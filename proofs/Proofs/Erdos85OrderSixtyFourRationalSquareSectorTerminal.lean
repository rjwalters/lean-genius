import Mathlib

/-!
# Rational square-sector terminal for the order-64 branch

For the order-16 defect block, the rational defect eigenvalues whose
adjacency-square scalars `7 - μ` are positive squares are `6`, `3`, and
`-2`, with square roots `1`, `2`, and `3`.  Write `a,b,c` for their
multiplicities and `p,q,r` for the signed differences of the positive and
negative square-root multiplicities.

The conditional inequality used below is `36a + 9b + 4c ≤ 63`; the order-16
moment cap supplies `b ≤ 3`; trace gives `p + 2q + 3r = -8`; and the cubic
color identity gives `p + 8q + 27r = -2C`.  The graph-side support theorem
gives `0 ≤ C ≤ 16`.  These linear constraints are inconsistent.

Important scope correction: `36a + 9b + 4c` is the raw `Σμ²` contribution.
For adjacency roots with squares `7-μ`, the second adjacency moment is
instead `a + 4b + 9c`.  The corrected inequality is consistent with the
other displayed constraints, so the theorem below is not a graph-level
terminal unless a separate raw-`μ` square bound is proved.
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

/-- Correct adjacency-square contribution of the three rational sectors
`μ = 6,3,-2`, whose paired adjacency roots have absolute values `1,2,3`. -/
def rationalSquareSectorAdjacencySecondMoment (a b c : ℤ) : ℤ :=
  a + 4 * b + 9 * c

/-- The corrected adjacency-moment version of the displayed constraints is
not contradictory: this explicit profile satisfies every one of them. -/
theorem corrected_rationalSquareSector_constraints_consistent :
    ∃ a b c p q r colorOrder : ℤ,
      0 ≤ b ∧ b ≤ 3 ∧
      rationalSquareSectorAdjacencySecondMoment a b c ≤ 63 ∧
      -a ≤ p ∧ p ≤ a ∧ -b ≤ q ∧ q ≤ b ∧
      -c ≤ r ∧ r ≤ c ∧
      p + 2 * q + 3 * r = -8 ∧
      p + 8 * q + 27 * r = -2 * colorOrder ∧
      0 ≤ colorOrder ∧ colorOrder ≤ 16 := by
  refine ⟨2, 3, 0, -2, -3, 0, 13, ?_⟩
  norm_num [rationalSquareSectorAdjacencySecondMoment]

end Erdos85
