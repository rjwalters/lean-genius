import Proofs.Erdos85ThreeSeparatorPCoreBudget

/-!
# Exact reciprocity at a complementary P-center

B50 expresses the internal-K defect degree `d` and K-fiber intersection
degree `g` by `d+g+b=m+2`.  The X-fiber deficit `f` satisfies `f+g=a`,
while `m+n=q-1` and `a+b=q-1`.  Eliminating `g,m,a,b,q` gives the exact,
subtraction-free reciprocity `f+2=d+n`.  This is (B50′).
-/

namespace Erdos85

noncomputable section

/-- Subtraction-free arithmetic core of B50′. -/
theorem Pcenter_attachment_defect_reciprocity
    (q a b m n d g f : ℕ)
    (hab : a + b = q - 1)
    (hmn : m + n = q - 1)
    (hKtrichotomy : d + g + b = m + 2)
    (hfiberDeficit : f + g = a) :
    f + 2 = d + n := by
  omega

/-- Ledger spelling of B50′ when `n≥2`. -/
theorem Pcenter_attachment_deficit_eq_Kdegree_add_n_sub_two
    (q a b m n d g f : ℕ)
    (hab : a + b = q - 1)
    (hmn : m + n = q - 1)
    (hKtrichotomy : d + g + b = m + 2)
    (hfiberDeficit : f + g = a)
    (hn : 2 ≤ n) :
    f = d + (n - 2) := by
  have h := Pcenter_attachment_defect_reciprocity
    q a b m n d g f hab hmn hKtrichotomy hfiberDeficit
  omega

/-- Immediate monotonic consequences used in location arguments. -/
theorem Pcenter_reciprocity_bounds
    (q a b m n d g f : ℕ)
    (hab : a + b = q - 1)
    (hmn : m + n = q - 1)
    (hKtrichotomy : d + g + b = m + 2)
    (hfiberDeficit : f + g = a) :
    n - 2 ≤ f ∧ d ≤ f + 2 := by
  have h := Pcenter_attachment_defect_reciprocity
    q a b m n d g f hab hmn hKtrichotomy hfiberDeficit
  omega

end


end Erdos85

#print axioms Erdos85.Pcenter_attachment_defect_reciprocity
#print axioms Erdos85.Pcenter_attachment_deficit_eq_Kdegree_add_n_sub_two
#print axioms Erdos85.Pcenter_reciprocity_bounds
