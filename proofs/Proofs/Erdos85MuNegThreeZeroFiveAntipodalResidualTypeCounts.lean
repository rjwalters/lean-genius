import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCommonTypeBalance
import Proofs.Erdos85MuNegThreeZeroFiveAntipodalForcedTypeCounts

/-! # Residual shore-type census after the eleven forced antipodal targets -/

namespace Erdos85

/-- Arithmetic form of the residual nineteen-target census.  If the full
thirty-target type counts satisfy the antipodal weighted balance and contain
the forced `5` type-two and `6` type-one targets, then a parameter `t ≤ 6`
determines every full and residual count. -/
theorem h305_antipodal_typeCounts_parameterized_of_forced_bounds
    (n0 n1 n2 : ℕ)
    (hpartition : n0 + n1 + n2 = 30)
    (hbalance : n0 = n2 + 2)
    (hforced2 : 5 ≤ n2)
    (hforced1 : 6 ≤ n1) :
    ∃ t : ℕ, t ≤ 6 ∧
      n2 = t + 5 ∧ n1 = 18 - 2 * t ∧ n0 = t + 7 ∧
      (n2 - 5) + (n1 - 6) + n0 = 19 ∧
      n1 - 6 = 12 - 2 * t := by
  refine ⟨n2 - 5, ?_⟩
  omega

/-- In particular, after deleting the forced `(5,6,0)` targets, the
nineteen residual targets have composition `(t, 12-2t, t+7)` for `t ≤ 6`.
The last equation records the unavoidable seven-edge type-zero surplus. -/
theorem h305_antipodal_residual_nineteen_parameterization
    (n0 n1 n2 : ℕ)
    (hpartition : n0 + n1 + n2 = 30)
    (hbalance : n0 = n2 + 2)
    (hforced2 : 5 ≤ n2)
    (hforced1 : 6 ≤ n1) :
    ∃ t : ℕ, t ≤ 6 ∧
      (n2 - 5 = t) ∧ (n1 - 6 = 12 - 2 * t) ∧
      n0 = t + 7 ∧
      (n2 - 5) + (n1 - 6) + n0 = 19 := by
  obtain ⟨t, ht, hn2, hn1, hn0, hsum, hr1⟩ :=
    h305_antipodal_typeCounts_parameterized_of_forced_bounds
      n0 n1 n2 hpartition hbalance hforced2 hforced1
  refine ⟨t, ht, ?_, hr1, hn0, hsum⟩
  omega

end Erdos85

#print axioms
  Erdos85.h305_antipodal_typeCounts_parameterized_of_forced_bounds
#print axioms Erdos85.h305_antipodal_residual_nineteen_parameterization
