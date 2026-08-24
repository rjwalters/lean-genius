import Proofs.Erdos85PureLargeExceptionalGraphTerminal

/-!
# Four-class rigidity at the pure exceptional endpoint

At `c=q`, allowing replication-zero and replication-one shore points does
not weaken the familiar partial-Baer endpoint profile: the moment equations
and the C4-free pair budget force exactly `q` private points, all remaining
shore points have replication two, and no point has replication zero or
three.
-/

namespace Erdos85

/-- Four-class endpoint profile, using only a pair inequality. -/
theorem binarySquare_pureExceptional_fourClass_endpoint_profile
    {q s n₀ n₁ n₂ n₃ : ℕ}
    (hshore : 2 * s = q * q + q)
    (hclasses : n₀ + n₁ + n₂ + n₃ = s)
    (hincidence : n₁ + 2 * n₂ + 3 * n₃ = q * q)
    (hpairs : 2 * n₂ + 6 * n₃ ≤ q * (q - 1)) :
    n₀ = 0 ∧ n₁ = q ∧ n₃ = 0 ∧
      2 * n₂ = q * (q - 1) ∧
      2 * n₂ + 6 * n₃ = q * (q - 1) := by
  by_cases hq0 : q = 0
  · subst q
    simp only [mul_zero, zero_mul, add_zero] at hshore hincidence hpairs ⊢
    omega
  · have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hqprod : q * (q - 1) + q = q * q := by
      calc
        q * (q - 1) + q = q * ((q - 1) + 1) := by ring
        _ = q * q := by rw [Nat.sub_add_cancel hqpos]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

end Erdos85

#print axioms Erdos85.binarySquare_pureExceptional_fourClass_endpoint_profile
