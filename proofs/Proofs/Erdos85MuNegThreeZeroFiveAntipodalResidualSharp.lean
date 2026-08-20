import Proofs.Erdos85MuNegThreeZeroFiveAntipodalResidualTypeCounts

/-! # Population-sharp antipodal residual census -/

namespace Erdos85

/-- The global twelve-edge type-zero population removes the endpoint case
`t = 6` from the residual nineteen-target parameterization.  Consequently
at least two residual type-one targets remain at every antipodal center. -/
theorem h305_antipodal_residual_parameterization_of_typeZero_cap
    (n0 n1 n2 : ℕ)
    (hpartition : n0 + n1 + n2 = 30)
    (hbalance : n0 = n2 + 2)
    (hforced2 : 5 ≤ n2)
    (hforced1 : 6 ≤ n1)
    (htypeZeroCap : n0 ≤ 12) :
    ∃ t : ℕ, t ≤ 5 ∧
      (n2 - 5 = t) ∧ (n1 - 6 = 12 - 2 * t) ∧
      2 ≤ n1 - 6 ∧ n0 = t + 7 ∧
      (n2 - 5) + (n1 - 6) + n0 = 19 := by
  obtain ⟨t, ht, hn2, hn1, hn0, hsum⟩ :=
    h305_antipodal_residual_nineteen_parameterization
      n0 n1 n2 hpartition hbalance hforced2 hforced1
  refine ⟨t, ?_, hn2, hn1, ?_, hn0, hsum⟩ <;> omega

end Erdos85

#print axioms
  Erdos85.h305_antipodal_residual_parameterization_of_typeZero_cap
