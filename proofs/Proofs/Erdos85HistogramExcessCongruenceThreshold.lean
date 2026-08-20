import Mathlib

/-! # Arithmetic thresholds from sixth-trace congruences -/

namespace Erdos85

/-- A multiple of six above 192 whose residue modulo four is twice an even
triangle count must reach 204; for an odd triangle count it must reach 198. -/
theorem histogramExcess_threshold_of_mod_four_triangle
    (E T : ℤ) (hdiv : (6 : ℤ) ∣ E) (hstrict : 192 < E)
    (hmod4 : E % 4 = (2 * T) % 4) :
    (Even T → 204 ≤ E) ∧ (¬ Even T → 198 ≤ E) := by
  rcases hdiv with ⟨k, hk⟩
  constructor
  · rintro ⟨r, hr⟩
    omega
  · intro hodd
    have hT : T % 2 = 1 := by
      have hrange := Int.emod_two_eq_zero_or_one T
      rcases hrange with hz | ho
      · exfalso
        apply hodd
        refine ⟨T / 2, ?_⟩
        omega
      · exact ho
    omega

/-- Equivalent parity coordinate used by the diagonal histogram: if
`T mod 2 = (c2+c6) mod 2`, evenness of the two exceptional diagonal bins
selects the stronger 204 threshold. -/
theorem histogramExcess_ge_204_of_even_diagTwo_add_diagSix
    (E T c2 c6 : ℤ) (hdiv : (6 : ℤ) ∣ E) (hstrict : 192 < E)
    (hmod4 : E % 4 = (2 * T) % 4)
    (hTdiag : T % 2 = (c2 + c6) % 2)
    (hdiag : Even (c2 + c6)) :
    204 ≤ E := by
  apply (histogramExcess_threshold_of_mod_four_triangle
    E T hdiv hstrict hmod4).1
  rcases hdiag with ⟨r, hr⟩
  refine ⟨T / 2, ?_⟩
  have hr0 : (c2 + c6) % 2 = 0 := by omega
  rw [hr0] at hTdiag
  omega

end Erdos85

#print axioms Erdos85.histogramExcess_threshold_of_mod_four_triangle
#print axioms Erdos85.histogramExcess_ge_204_of_even_diagTwo_add_diagSix
