import Proofs.Erdos85ThreeSeparatorReciprocalWingLower

/-!
# Exact global P-core budget

For each complementary P-center, B50 gives the subtraction-free equation
`d_w + g_w + b = m_w + 2`, where `d_w` is its defect incidence into
`K \ P` and `g_w` its K-fiber-intersection incidence.  Summing the three
equations produces the tiny global budget in (B51).  On the lower endpoint
of the two residue classes this budget is respectively zero or one.
-/

namespace Erdos85

noncomputable section

/-- Subtraction-free arithmetic core of B51. -/
theorem three_Pcenter_budgets_sum
    (q a b m0 m1 m2 d0 d1 d2 g0 g1 g2 : ℕ)
    (hq : 2 ≤ q)
    (hab : a + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (h0 : d0 + g0 + b = m0 + 2)
    (h1 : d1 + g1 + b = m1 + 2)
    (h2 : d2 + g2 + b = m2 + 2) :
    ((d0 + g0) + (d1 + g1) + (d2 + g2)) + q = 3 * a + 5 ∧
      (d0 + g0) + (d1 + g1) + (d2 + g2) = 3 * a + 5 - q := by
  constructor <;> omega

/-- Odd-exponent bottom slice in B51′: the entire P-core budget vanishes. -/
theorem Pcore_budget_zero_at_three_r_add_two
    (r total : ℕ)
    (hr : 1 ≤ r)
    (hbudget : total + (3 * r + 2) = 3 * (r - 1) + 5) :
    total = 0 := by
  omega

/-- Even-exponent bottom slice in B51′: exactly one P-core edge remains. -/
theorem Pcore_budget_one_at_three_r_add_one
    (r total : ℕ)
    (hr : 1 ≤ r)
    (hbudget : total + (3 * r + 1) = 3 * (r - 1) + 5) :
    total = 1 := by
  omega

/-- A zero six-term budget forces every constituent incidence to vanish. -/
theorem six_term_budget_zero
    (d0 d1 d2 g0 g1 g2 : ℕ)
    (hzero : (d0 + g0) + (d1 + g1) + (d2 + g2) = 0) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0 := by
  omega

end


end Erdos85

#print axioms Erdos85.three_Pcenter_budgets_sum
#print axioms Erdos85.Pcore_budget_zero_at_three_r_add_two
#print axioms Erdos85.Pcore_budget_one_at_three_r_add_one
#print axioms Erdos85.six_term_budget_zero
