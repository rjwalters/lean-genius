import Proofs.Erdos85ThreeSeparatorUniformWingIntervals

/-!
# Reciprocal X/Y exclusion strengthens every wing

The reciprocal-fiber argument bounds the K-intersection degree, in
subtraction-free form, by `d+b ≤ m+2`, while the X-fiber deficit satisfies
`a-d≤m`.  Together with `a+b=q-1`, this forces `q≤2m+3`.  This is (B49′).
-/

namespace Erdos85

noncomputable section

/-- Subtraction-safe arithmetic core of B49′. -/
theorem reciprocal_wing_degree_deficit_forces_lower
    (q a b m d : ℕ)
    (hq : 2 ≤ q)
    (hab : a + b = q - 1)
    (hdegree : d + b ≤ m + 2)
    (hdeficit : a - d ≤ m) :
    q ≤ 2 * m + 3 ∧ (q - 2) / 2 ≤ m := by
  constructor <;> omega

/-- Even-parameter spelling used in B49″: `m≥q/2-1`. -/
theorem reciprocal_wing_lower_of_even_parameter
    (q r a b m d : ℕ)
    (hq : 2 ≤ q)
    (hqr : q = 2 * r)
    (hab : a + b = q - 1)
    (hdegree : d + b ≤ m + 2)
    (hdeficit : a - d ≤ m) :
    r - 1 ≤ m := by
  have h := reciprocal_wing_degree_deficit_forces_lower
    q a b m d hq hab hdegree hdeficit
  omega

/-- Complementary even-parameter bound `n≤q/2`. -/
theorem reciprocal_complementary_wing_upper_of_even_parameter
    (q r a b m n d : ℕ)
    (hq : 2 ≤ q)
    (hqr : q = 2 * r)
    (hab : a + b = q - 1)
    (hmn : m + n = q - 1)
    (hdegree : d + b ≤ m + 2)
    (hdeficit : a - d ≤ m) :
    n ≤ r := by
  have hm := reciprocal_wing_lower_of_even_parameter
    q r a b m d hq hqr hab hdegree hdeficit
  omega

end


end Erdos85

#print axioms Erdos85.reciprocal_wing_degree_deficit_forces_lower
#print axioms Erdos85.reciprocal_wing_lower_of_even_parameter
#print axioms Erdos85.reciprocal_complementary_wing_upper_of_even_parameter
