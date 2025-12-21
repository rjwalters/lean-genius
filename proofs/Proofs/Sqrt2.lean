import Mathlib.Tactic

namespace Sqrt2

-- Test proof with tactics
theorem square_nonneg (n : ℤ) : 0 ≤ n * n := by
  by_cases h : 0 ≤ n
  · exact mul_nonneg h h
  · push_neg at h
    have h1 : n ≤ 0 := le_of_lt h
    have h2 : 0 ≤ -n := neg_nonneg.mpr h1
    calc n * n = (-n) * (-n) := by ring
             _ ≥ 0 := mul_nonneg h2 h2

theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

end Sqrt2
