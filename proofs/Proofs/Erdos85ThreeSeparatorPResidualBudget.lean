import Proofs.Erdos85ThreeSeparatorPReciprocity

/-!
# Exact P-to-R residual budget

For the complementary P-center in one wing, the candidate R-neighbors
split exactly as `d_R+s+f+1=n`.  The two resolution indicators `s,f` are
mutually exclusive, so `s+f≤1` and consequently `d_R≥n-2`.  Summing the
three exact equations gives the global budget (B52′).
-/

namespace Erdos85

noncomputable section

/-- One-wing lower bound in B52, stated without subtraction ambiguity. -/
theorem Pcenter_residual_degree_ge_n_sub_two
    (n d s f : ℕ)
    (hexact : d + s + f + 1 = n)
    (hmutex : s + f ≤ 1) :
    n - 2 ≤ d := by
  omega

/-- Subtraction-free global form of B52′. -/
theorem three_Pcenter_residual_budgets_sum
    (q n0 n1 n2 d0 d1 d2 s0 s1 s2 f0 f1 f2 : ℕ)
    (hnsum : n0 + n1 + n2 = q + 1)
    (h0 : d0 + s0 + f0 + 1 = n0)
    (h1 : d1 + s1 + f1 + 1 = n1)
    (h2 : d2 + s2 + f2 + 1 = n2) :
    ((d0 + d1 + d2) + ((s0 + f0) + (s1 + f1) + (s2 + f2))) + 2 = q ∧
      (d0 + d1 + d2) + ((s0 + f0) + (s1 + f1) + (s2 + f2)) = q - 2 := by
  constructor <;> omega

/-- At most three resolutions are removed from the full `q-2` budget. -/
theorem three_Pcenter_residual_degree_lower
    (q n0 n1 n2 d0 d1 d2 s0 s1 s2 f0 f1 f2 : ℕ)
    (hnsum : n0 + n1 + n2 = q + 1)
    (h0 : d0 + s0 + f0 + 1 = n0)
    (h1 : d1 + s1 + f1 + 1 = n1)
    (h2 : d2 + s2 + f2 + 1 = n2)
    (hmutex0 : s0 + f0 ≤ 1)
    (hmutex1 : s1 + f1 ≤ 1)
    (hmutex2 : s2 + f2 ≤ 1) :
    q - 5 ≤ d0 + d1 + d2 := by
  have hsum := three_Pcenter_residual_budgets_sum
    q n0 n1 n2 d0 d1 d2 s0 s1 s2 f0 f1 f2 hnsum h0 h1 h2
  omega

end


end Erdos85

#print axioms Erdos85.Pcenter_residual_degree_ge_n_sub_two
#print axioms Erdos85.three_Pcenter_residual_budgets_sum
#print axioms Erdos85.three_Pcenter_residual_degree_lower
