import Proofs.Erdos85ThreeSeparatorPCoreBudget

/-!
# One-hot localization of the bottom P-core budget

In the `q = 3r+1` bottom slice, B51' leaves exactly one incidence among
the three defect and three K-fiber-intersection contributions.  This file
turns that scalar statement into the six explicit location alternatives
needed by the remaining separator analysis.
-/

namespace Erdos85

/-- Six nonnegative contributions with total one form a one-hot vector. -/
theorem six_term_budget_one_cases
    (d0 d1 d2 g0 g1 g2 : ℕ)
    (hone : (d0 + g0) + (d1 + g1) + (d2 + g2) = 1) :
    (d0 = 1 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 1 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 0 ∧ d2 = 1 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 1 ∧ g1 = 0 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 1 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 1) := by
  omega

/-- B51' at `q = 3r+1` has exactly one surviving incidence, with its
location classified among the three P-centers and the two relation types. -/
theorem Pcore_oneHot_at_three_r_add_one
    (r d0 d1 d2 g0 g1 g2 : ℕ)
    (hr : 1 ≤ r)
    (hbudget :
      ((d0 + g0) + (d1 + g1) + (d2 + g2)) + (3 * r + 1) =
        3 * (r - 1) + 5) :
    (d0 = 1 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 1 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 0 ∧ d2 = 1 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 1 ∧ g1 = 0 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 1 ∧ g2 = 0) ∨
      (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 1) := by
  apply six_term_budget_one_cases
  exact Pcore_budget_one_at_three_r_add_one r
    ((d0 + g0) + (d1 + g1) + (d2 + g2)) hr hbudget

end Erdos85

#print axioms Erdos85.six_term_budget_one_cases
#print axioms Erdos85.Pcore_oneHot_at_three_r_add_one
