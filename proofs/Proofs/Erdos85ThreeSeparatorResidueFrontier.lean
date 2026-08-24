import Proofs.Erdos85TwoSeparatorMantelContradiction

/-!
# The residue `(q-2,q-1)` three-separator frontier

The cut budget and parity leave exactly the three numerical cases denoted
(B1) in the NONBIP-CONNECTED analysis.
-/

namespace Erdos85

/-- Exact arithmetic classification of the `(q-2,q-1)` three-separator
cut sizes. -/
theorem threeSeparator_residue_sub_two_pred_cut_cases
    (q e x y : ℕ) (hq : 8 ≤ q) (he : e ≤ 1)
    (hxLower : 2 * q - 4 ≤ x) (hyLower : q - 1 ≤ y)
    (hxEven : Even (x - (2 * q - 4)))
    (hyEven : Even (y - (q - 1)))
    (hbudget : x + y = 3 * (q - 1) - 2 * e) :
    (e = 1 ∧ x = 2 * q - 4 ∧ y = q - 1) ∨
      (e = 0 ∧ x = 2 * q - 2 ∧ y = q - 1) ∨
      (e = 0 ∧ x = 2 * q - 4 ∧ y = q + 1) := by
  obtain ⟨a, ha⟩ := hxEven
  obtain ⟨b, hb⟩ := hyEven
  have hx : x = (2 * q - 4) + (a + a) := by omega
  have hy : y = (q - 1) + (b + b) := by omega
  omega

end Erdos85

#print axioms Erdos85.threeSeparator_residue_sub_two_pred_cut_cases
