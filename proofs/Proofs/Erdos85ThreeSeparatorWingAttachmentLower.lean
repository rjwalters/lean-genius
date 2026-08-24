import Proofs.Erdos85ThreeSeparatorUniformKFiberSurplus

/-!
# Coupled-design lower bound on every wing attachment

For the P-center complementary to a separator color, the K-fiber
intersection-graph template gives `d ≤ m+1`.  Its exact deficit is supplied
by distinct D-attachments of that color, giving `a-d ≤ m`.  Together these
force `a ≤ 2m+1`, or `m ≥ ⌈(a-1)/2⌉ = a/2` over naturals.  This is (B42).
-/

open Finset

namespace Erdos85

noncomputable section

/-- Subtraction-safe arithmetic core of B42. -/
theorem wing_attachment_lower_of_degree_and_deficit
    (a d m : ℕ)
    (hdegree : d ≤ m + 1)
    (hdeficit : a - d ≤ m) :
    a ≤ 2 * m + 1 ∧ a / 2 ≤ m := by
  constructor <;> omega

/-- Uniform B42 consumer for all three separator colors. -/
theorem every_wing_attachment_lower
    {W : Type*} (S : Finset W)
    (a : ℕ) (degree attachment : W → ℕ)
    (hdegree : ∀ w ∈ S, degree w ≤ attachment w + 1)
    (hdeficit : ∀ w ∈ S, a - degree w ≤ attachment w) :
    ∀ w ∈ S,
      a ≤ 2 * attachment w + 1 ∧ a / 2 ≤ attachment w := by
  intro w hw
  exact wing_attachment_lower_of_degree_and_deficit
    a (degree w) (attachment w) (hdegree w hw) (hdeficit w hw)

end


end Erdos85

#print axioms Erdos85.wing_attachment_lower_of_degree_and_deficit
#print axioms Erdos85.every_wing_attachment_lower
