import Proofs.Erdos85ThreeSeparatorBottomResidualProfiles

/-!
# Bottom-slice P-core profiles

At the two dyadic bottom residues, the exact B51 budget is respectively
zero or one.  This file expands those tiny totals into the incidence-level
normal forms needed by the remaining collision argument.
-/

namespace Erdos85

/-- A six-term natural-number budget of one has exactly one unit entry. -/
theorem six_term_budget_one
    (d0 d1 d2 g0 g1 g2 : ℕ)
    (hone : (d0 + g0) + (d1 + g1) + (d2 + g2) = 1) :
    (d0 = 1 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 1 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 0 ∧ d2 = 1 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 1 ∧ g1 = 0 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 1 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 1) := by
  omega

/-- In the `q=3r+2`, `a=r-1` bottom branch, B51 forces every P-to-K
defect incidence and every P-centered K-fiber intersection incidence to
vanish. -/
theorem bottomPCore_threeTwo_all_zero
    (q a b r m0 m1 m2 d0 d1 d2 g0 g1 g2 : ℕ)
    (hr : 1 ≤ r)
    (hq : q = 3 * r + 2)
    (ha : a = r - 1)
    (hab : a + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (h0 : d0 + g0 + b = m0 + 2)
    (h1 : d1 + g1 + b = m1 + 2)
    (h2 : d2 + g2 + b = m2 + 2) :
    d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0 := by
  have hsum := three_Pcenter_budgets_sum q a b m0 m1 m2
    d0 d1 d2 g0 g1 g2 (by omega) hab hmass h0 h1 h2
  have hzero : (d0 + g0) + (d1 + g1) + (d2 + g2) = 0 := by
    omega
  exact six_term_budget_zero d0 d1 d2 g0 g1 g2 hzero

/-- In the `q=3r+1`, `a=r-1` bottom branch, exactly one of the six P-core
incidence counts survives. -/
theorem bottomPCore_threeOne_exactly_one
    (q a b r m0 m1 m2 d0 d1 d2 g0 g1 g2 : ℕ)
    (hr : 1 ≤ r)
    (hq : q = 3 * r + 1)
    (ha : a = r - 1)
    (hab : a + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (h0 : d0 + g0 + b = m0 + 2)
    (h1 : d1 + g1 + b = m1 + 2)
    (h2 : d2 + g2 + b = m2 + 2) :
    (d0 = 1 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 1 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 0 ∧ d2 = 1 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 1 ∧ g1 = 0 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 1 ∧ g2 = 0) ∨
    (d0 = 0 ∧ d1 = 0 ∧ d2 = 0 ∧ g0 = 0 ∧ g1 = 0 ∧ g2 = 1) := by
  have hsum := three_Pcenter_budgets_sum q a b m0 m1 m2
    d0 d1 d2 g0 g1 g2 (by omega) hab hmass h0 h1 h2
  have hone : (d0 + g0) + (d1 + g1) + (d2 + g2) = 1 := by
    omega
  exact six_term_budget_one d0 d1 d2 g0 g1 g2 hone

end Erdos85

#print axioms Erdos85.six_term_budget_one
#print axioms Erdos85.bottomPCore_threeTwo_all_zero
#print axioms Erdos85.bottomPCore_threeOne_exactly_one
