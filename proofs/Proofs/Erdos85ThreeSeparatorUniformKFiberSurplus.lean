import Proofs.Erdos85ThreeSeparatorUniformRFiberOverlapLedger
import Proofs.Erdos85ThreeSeparatorFirstSliceAttachmentMultiplicity

/-!
# Uniform K-fiber intersection surplus

For `a≥1`, subtracting the total separator-attachment count from the
partition of X by attachment multiplicity gives
`n₀ = n₂ + q(a-1) + 2`.  In the K-fiber design, `n₀` counts pairwise
fiber intersections and `n₂` counts uncovered points, so this is the
non-endpoint, subtraction-safe form of (B38).
-/

namespace Erdos85

noncomputable section

/-- Arithmetic core of B38 over naturals, stated only in the range where
the signed ledger has a nonnegative right-hand side. -/
theorem uniform_attachmentClass_zero_surplus
    (q a n0 n1 n2 : ℕ)
    (hq : 2 ≤ q)
    (ha : 1 ≤ a)
    (hpartition : n0 + n1 + n2 = q * (a + 1) - 2)
    (hattachments : n1 + 2 * n2 = 2 * q - 4) :
    n0 = n2 + q * (a - 1) + 2 := by
  have hexpand : q * (a + 1) = q * (a - 1) + 2 * q := by
    calc
      q * (a + 1) = q * ((a - 1) + 2) := by
        congr 1
        omega
      _ = q * (a - 1) + 2 * q := by ring
  have hpartition' : n0 + n1 + n2 + 2 = q * (a - 1) + 2 * q := by
    omega
  have hattachments' : n1 + 2 * n2 + 4 = 2 * q := by
    omega
  omega

/-- Intersection-graph interpretation of B38. -/
theorem uniform_Kfiber_intersection_uncovered_surplus
    (q a edgeCount uncoveredCount n1 : ℕ)
    (hq : 2 ≤ q)
    (ha : 1 ≤ a)
    (hpartition : edgeCount + n1 + uncoveredCount = q * (a + 1) - 2)
    (hattachments : n1 + 2 * uncoveredCount = 2 * q - 4) :
    edgeCount = uncoveredCount + q * (a - 1) + 2 ∧
      uncoveredCount + 2 ≤ edgeCount := by
  have heq := uniform_attachmentClass_zero_surplus
    q a edgeCount n1 uncoveredCount hq ha hpartition hattachments
  exact ⟨heq, by omega⟩

end


end Erdos85

#print axioms Erdos85.uniform_attachmentClass_zero_surplus
#print axioms Erdos85.uniform_Kfiber_intersection_uncovered_surplus
