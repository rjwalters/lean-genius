import Proofs.Erdos85ThreeSeparatorUniformWingIntervals
import Proofs.Erdos85ThreeSeparatorReciprocalWingLower

/-!
# Combined separator-wing intervals

The bottom-range estimate (B46) and reciprocal estimate (B49') dominate
on complementary parameter ranges.  Their conjunction is the compact
sharp interval (B49'') used by all later wing arguments.
-/

namespace Erdos85

/-- Single-wing arithmetic form of (B49''). -/
theorem combined_wing_interval
    (q a b m n : ℕ)
    (hmn : m + n = q - 1)
    (hnpos : 1 ≤ n)
    (hB46 : b - 2 ≤ m ∧ m ≤ 2 * a + 2 ∧
      q - 2 * a - 3 ≤ n ∧ n ≤ a + 2)
    (hB49 : q / 2 - 1 ≤ m ∧ n ≤ q / 2) :
    max (b - 2) (q / 2 - 1) ≤ m ∧
      m ≤ min (2 * a + 2) (q - 2) ∧
      max 1 (q - 2 * a - 3) ≤ n ∧
      n ≤ min (a + 2) (q / 2) := by
  have hmUpper : m ≤ q - 2 := by omega
  exact ⟨max_le hB46.1 hB49.1,
    le_min hB46.2.1 hmUpper,
    max_le hnpos hB46.2.2.1,
    le_min hB46.2.2.2 hB49.2⟩

/-- Uniform B49'' interval for every member of an indexed wing family. -/
theorem combined_wing_intervals
    {ι : Type*}
    (q a b : ℕ) (m n : ι → ℕ)
    (hmn : ∀ w, m w + n w = q - 1)
    (hnpos : ∀ w, 1 ≤ n w)
    (hB46 : ∀ w, b - 2 ≤ m w ∧ m w ≤ 2 * a + 2 ∧
      q - 2 * a - 3 ≤ n w ∧ n w ≤ a + 2)
    (hB49 : ∀ w, q / 2 - 1 ≤ m w ∧ n w ≤ q / 2) :
    ∀ w,
      max (b - 2) (q / 2 - 1) ≤ m w ∧
        m w ≤ min (2 * a + 2) (q - 2) ∧
        max 1 (q - 2 * a - 3) ≤ n w ∧
        n w ≤ min (a + 2) (q / 2) := by
  intro w
  exact combined_wing_interval q a b (m w) (n w)
    (hmn w) (hnpos w) (hB46 w) (hB49 w)

#print axioms combined_wing_interval
#print axioms combined_wing_intervals

end Erdos85
