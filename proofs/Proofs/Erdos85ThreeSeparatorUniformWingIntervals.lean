import Proofs.Erdos85ThreeSeparatorUniformWingRangeLower

/-!
# Individual wing intervals

Applying the B45 lower bound to the two wings complementary to a fixed
one and subtracting from the total attachment mass gives `m_w≤2a+2`.
Together with `m_w+n_w=q-1`, this traps both halves of every wing in the
intervals displayed in (B46).
-/

namespace Erdos85

noncomputable section

/-- One-wing arithmetic core of B46. -/
theorem uniform_oneWing_interval
    (q a b m m' m'' n : ℕ)
    (hq : 2 ≤ q)
    (hab : a + b = q - 1)
    (hmass : m + m' + m'' = 2 * q - 4)
    (hm : b - 2 ≤ m)
    (hm' : b - 2 ≤ m')
    (hm'' : b - 2 ≤ m'')
    (hcomplement : m + n = q - 1) :
    b - 2 ≤ m ∧ m ≤ 2 * a + 2 ∧
      q - 2 * a - 3 ≤ n ∧ n ≤ a + 2 := by
  omega

/-- Symmetric B46 bounds for all three wings. -/
theorem uniform_threeWing_intervals
    (q a b m0 m1 m2 n0 n1 n2 : ℕ)
    (hq : 2 ≤ q)
    (hab : a + b = q - 1)
    (hmass : m0 + m1 + m2 = 2 * q - 4)
    (hm0 : b - 2 ≤ m0)
    (hm1 : b - 2 ≤ m1)
    (hm2 : b - 2 ≤ m2)
    (hc0 : m0 + n0 = q - 1)
    (hc1 : m1 + n1 = q - 1)
    (hc2 : m2 + n2 = q - 1) :
    (b - 2 ≤ m0 ∧ m0 ≤ 2 * a + 2 ∧
      q - 2 * a - 3 ≤ n0 ∧ n0 ≤ a + 2) ∧
    (b - 2 ≤ m1 ∧ m1 ≤ 2 * a + 2 ∧
      q - 2 * a - 3 ≤ n1 ∧ n1 ≤ a + 2) ∧
    (b - 2 ≤ m2 ∧ m2 ≤ 2 * a + 2 ∧
      q - 2 * a - 3 ≤ n2 ∧ n2 ≤ a + 2) := by
  refine ⟨uniform_oneWing_interval q a b m0 m1 m2 n0
    hq hab hmass hm0 hm1 hm2 hc0, ?_, ?_⟩
  · apply uniform_oneWing_interval q a b m1 m0 m2 n1
      hq hab (by omega) hm1 hm0 hm2 hc1
  · apply uniform_oneWing_interval q a b m2 m0 m1 n2
      hq hab (by omega) hm2 hm0 hm1 hc2

end


end Erdos85

#print axioms Erdos85.uniform_oneWing_interval
#print axioms Erdos85.uniform_threeWing_intervals
