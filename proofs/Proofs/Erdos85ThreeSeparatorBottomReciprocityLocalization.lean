import Proofs.Erdos85ThreeSeparatorBottomPCoreProfiles
import Proofs.Erdos85ThreeSeparatorPReciprocity

/-!
# Bottom-slice reciprocity localization

The unit B51' budget in the `q = 3r+1` branch initially has six possible
locations.  Once B48 relabels the complementary R-wing sizes as
`r+1,r+1,r`, the B50' reciprocity equations force the unit onto the unique
smaller wing.  Thus only its defect incidence or its K-fiber-intersection
incidence can survive.
-/

namespace Erdos85

/-- In the `3r+2` branch, the zero P-core budget and B50' make all three
X-fiber attachment deficits equal to the baseline `r-1`. -/
theorem bottomReciprocity_threeTwo_deficits
    (r d0 d1 d2 f0 f1 f2 : ℕ)
    (hr : 1 ≤ r)
    (hd0 : d0 = 0) (hd1 : d1 = 0) (hd2 : d2 = 0)
    (hrec0 : f0 + 2 = d0 + (r + 1))
    (hrec1 : f1 + 2 = d1 + (r + 1))
    (hrec2 : f2 + 2 = d2 + (r + 1)) :
    f0 = r - 1 ∧ f1 = r - 1 ∧ f2 = r - 1 := by
  omega

/-- In the relabeled `3r+1` branch, B48+B50'+B51' reduce the six-way
one-hot split to the two relation types on the exceptional smaller wing. -/
theorem bottomReciprocity_threeOne_exceptionalWing
    (r d0 d1 d2 g0 g1 g2 f0 f1 f2 : ℕ)
    (hr : 2 ≤ r)
    (hone : (d0 + g0) + (d1 + g1) + (d2 + g2) = 1)
    (hrec0 : f0 + 2 = d0 + (r + 1))
    (hrec1 : f1 + 2 = d1 + (r + 1))
    (hrec2 : f2 + 2 = d2 + r)
    (hfiber0 : f0 + g0 = r - 1)
    (hfiber1 : f1 + g1 = r - 1)
    (hfiber2 : f2 + g2 = r - 1) :
    d0 = 0 ∧ g0 = 0 ∧ d1 = 0 ∧ g1 = 0 ∧
      f0 = r - 1 ∧ f1 = r - 1 ∧
      ((d2 = 1 ∧ g2 = 0 ∧ f2 = r - 1) ∨
        (d2 = 0 ∧ g2 = 1 ∧ f2 = r - 2)) := by
  omega

end Erdos85

#print axioms Erdos85.bottomReciprocity_threeTwo_deficits
#print axioms Erdos85.bottomReciprocity_threeOne_exceptionalWing
