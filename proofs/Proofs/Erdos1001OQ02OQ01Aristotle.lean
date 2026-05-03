/-
  Aristotle targets for Erdos1001OQ02OQ01
  Routine supporting lemmas for automated proof search.
  See Proofs/Erdos1001OQ02OQ01.lean for the main formalization.

  These lemmas establish real-analysis comparisons of asymptotic rates:
  - (log N)^(2/3) / N = o(log N / N)  — Walfisz rate is strictly better than Mertens rate
  - (log N)^(2/3) * (log log N)^(4/3) / N = o(log N / N)  — full Walfisz rate comparison
  - A * (Walfisz rate) = o(A * Mertens rate)  — scalar multiple preserves little-o
  - 1 / (log N)^(1/3) → 0  — improvement factor vanishes
-/
import Mathlib

open Filter Real Asymptotics

namespace Erdos1001OQ02OQ01.Aristotle

/-- The Walfisz range error rate is strictly smaller order than the Mertens rate.

    (log N)^(2/3) / N = o(log N / N), equivalently 1/(log N)^(1/3) → 0.
    Reduces to: log(N)^(2/3) / log(N) = 1/(log N)^(1/3) → 0. -/
theorem walfisz_rate_isLittleO_mertens_rate :
    (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) / N)
    =o[atTop] (fun N : ℕ => Real.log N / N) := by
  sorry

/-- The Walfisz range error rate with log log factor is also o(log N / N).

    (log N)^(2/3) * (log log N)^(4/3) / N = o(log N / N).
    Follows from (log log N)^(4/3) = o((log N)^(1/3)) at infinity. -/
theorem walfisz_full_rate_isLittleO_mertens_rate :
    (fun N : ℕ => (Real.log N) ^ ((2:ℝ)/3) *
                  (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N)
    =o[atTop] (fun N : ℕ => Real.log N / N) := by
  sorry

/-- A * (Walfisz rate) = o(A * Mertens rate) for A > 0.

    Follows from walfisz_full_rate_isLittleO_mertens_rate by IsLittleO.const_mul_left. -/
theorem sharp_rate_isLittleO_oq02_rate (A : ℝ) (hA : 0 < A) :
    (fun N : ℕ => A * ((Real.log N) ^ ((2:ℝ)/3) *
                       (Real.log (Real.log N)) ^ ((4:ℝ)/3) / N))
    =o[atTop]
    (fun N : ℕ => A * (Real.log N / N)) := by
  sorry

/-- The improvement factor 1/(log N)^(1/3) tends to zero.

    Since log N → ∞, (log N)^(1/3) → ∞, so its reciprocal → 0. -/
theorem improvement_factor_tends_to_zero :
    Tendsto (fun N : ℕ => 1 / (Real.log N) ^ ((1:ℝ)/3)) atTop (nhds 0) := by
  sorry

end Erdos1001OQ02OQ01.Aristotle
