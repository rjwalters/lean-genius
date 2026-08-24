import Proofs.Erdos85ThreeSeparatorBottomWingRigidity
import Proofs.Erdos85ThreeSeparatorPResidualPartition

/-!
# Bottom-slice P-to-R residual profiles

Combining the paired B48 wing sizes with the exact B52 partition leaves
only two consecutive possibilities for each P-center's defect degree into
its complementary R-wing.  These normal forms expose the remaining binary
residue classes for the location-specific endgame.
-/

namespace Erdos85

/-- In the `q=3r+2` bottom slice all three R-wings have size `r+1`.
Writing `tᵢ` for the mutually exclusive X/Y resolution indicator, B52 says
`dᵢ+tᵢ+1=r+1`; hence every residual degree is `r` or `r-1`, with exact
total degree-plus-resolution mass `3r`. -/
theorem bottomResidual_threeTwo_profile
    (r d0 d1 d2 t0 t1 t2 : ℕ)
    (hr : 1 ≤ r)
    (ht0 : t0 ≤ 1) (ht1 : t1 ≤ 1) (ht2 : t2 ≤ 1)
    (h0 : d0 + t0 + 1 = r + 1)
    (h1 : d1 + t1 + 1 = r + 1)
    (h2 : d2 + t2 + 1 = r + 1) :
    (d0 = r ∨ d0 = r - 1) ∧
      (d1 = r ∨ d1 = r - 1) ∧
      (d2 = r ∨ d2 = r - 1) ∧
      (d0 + d1 + d2) + (t0 + t1 + t2) = 3 * r := by
  omega

/-- In the `q=3r+1` bottom slice, after relabeling the exceptional wing,
the R-wing sizes are `r+1,r+1,r`.  The first two residual degrees are
`r` or `r-1`, the last is `r-1` or `r-2`, and their exact combined mass is
`3r-1`. -/
theorem bottomResidual_threeOne_profile
    (r d0 d1 d2 t0 t1 t2 : ℕ)
    (hr : 2 ≤ r)
    (ht0 : t0 ≤ 1) (ht1 : t1 ≤ 1) (ht2 : t2 ≤ 1)
    (h0 : d0 + t0 + 1 = r + 1)
    (h1 : d1 + t1 + 1 = r + 1)
    (h2 : d2 + t2 + 1 = r) :
    (d0 = r ∨ d0 = r - 1) ∧
      (d1 = r ∨ d1 = r - 1) ∧
      (d2 = r - 1 ∨ d2 = r - 2) ∧
      (d0 + d1 + d2) + (t0 + t1 + t2) = 3 * r - 1 := by
  omega

/-- The number of one-unit degree drops is exactly the total resolution
mass in the `3r+2` profile. -/
theorem bottomResidual_threeTwo_drop_count
    (r d0 d1 d2 t0 t1 t2 : ℕ)
    (h0 : d0 + t0 = r)
    (h1 : d1 + t1 = r)
    (h2 : d2 + t2 = r) :
    (3 * r - (d0 + d1 + d2)) = t0 + t1 + t2 := by
  omega

/-- The analogous exact drop ledger for the `3r+1` profile. -/
theorem bottomResidual_threeOne_drop_count
    (r d0 d1 d2 t0 t1 t2 : ℕ)
    (h0 : d0 + t0 = r)
    (h1 : d1 + t1 = r)
    (h2 : d2 + t2 + 1 = r) :
    (3 * r - 1 - (d0 + d1 + d2)) = t0 + t1 + t2 := by
  omega

end Erdos85

#print axioms Erdos85.bottomResidual_threeTwo_profile
#print axioms Erdos85.bottomResidual_threeOne_profile
#print axioms Erdos85.bottomResidual_threeTwo_drop_count
#print axioms Erdos85.bottomResidual_threeOne_drop_count
