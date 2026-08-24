import Proofs.Erdos85ThreeSeparatorWingAttachmentLower

/-!
# The dual escape lies in the middle third

The B45 injections give `b-2 ≤ m_w` for each of the three separator
colors.  Summing and using the exact attachment mass `Σm_w=2q-4`, together
with `a+b=q-1`, forces `q≤3a+5`.  This is the subtraction-safe B45′ range
bound and immediately removes the endpoint and (for `q≥16`) first slice.
-/

namespace Erdos85

noncomputable section

/-- Arithmetic core of B45′. -/
theorem uniform_threeWing_lower_forces_q_le_three_a_add_five
    (q a b m0 m1 m2 : ℕ)
    (hq : 2 ≤ q)
    (hab : a + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (hm0 : b - 2 ≤ m0)
    (hm1 : b - 2 ≤ m1)
    (hm2 : b - 2 ≤ m2) :
    q ≤ 3 * a + 5 := by
  omega

/-- B45′ excludes the punctured-parallel-class endpoint for `q≥8`. -/
theorem false_of_uniform_threeWing_endpoint
    (q b m0 m1 m2 : ℕ)
    (hq : 8 ≤ q)
    (hab : 0 + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (hm0 : b - 2 ≤ m0)
    (hm1 : b - 2 ≤ m1)
    (hm2 : b - 2 ≤ m2) : False := by
  have hqle := uniform_threeWing_lower_forces_q_le_three_a_add_five
    q 0 b m0 m1 m2 (by omega) hab hmass hm0 hm1 hm2
  omega

/-- B45′ excludes the first path-cycle slice for every `q≥16`. -/
theorem false_of_uniform_threeWing_firstSlice
    (q b m0 m1 m2 : ℕ)
    (hq : 16 ≤ q)
    (hab : 1 + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (hm0 : b - 2 ≤ m0)
    (hm1 : b - 2 ≤ m1)
    (hm2 : b - 2 ≤ m2) : False := by
  have hqle := uniform_threeWing_lower_forces_q_le_three_a_add_five
    q 1 b m0 m1 m2 (by omega) hab hmass hm0 hm1 hm2
  omega

end


end Erdos85

#print axioms Erdos85.uniform_threeWing_lower_forces_q_le_three_a_add_five
#print axioms Erdos85.false_of_uniform_threeWing_endpoint
#print axioms Erdos85.false_of_uniform_threeWing_firstSlice
