/-
  Aristotle targets for Erdős Problem #961 (Smooth Numbers in Consecutive Intervals)
  Routine supporting lemmas for automated proof search.
  See Erdos961Problem.lean for the main formalization.

  Targets:
  1. f_nonneg — 0 ≤ (f k : ℝ) (cast of ℕ, positivity)
  2. log_atTop_tendsto — Real.log k → ∞ (Mathlib has Real.tendsto_log_atTop)
  3. three_div_log_tendsto_zero — 3 / log k → 0 as k → ∞
  4. three_k_div_log_isLittleO — (3k / log k) = o(k) as k → ∞
  5. f_sublinear — f(k) = o(k) from the Erdős 1955 bound

  Key axiom available: erdos_1955_bound : ∀ᶠ k in atTop, (f k : ℝ) < 3 * k / log k
-/
import Mathlib

namespace Erdos961Aristotle

open Filter Real Asymptotics

/-- f(k) as a real is nonneg (cast of ℕ). -/
theorem f_nonneg (k : ℕ) (f : ℕ → ℕ) : (0 : ℝ) ≤ (f k : ℝ) := by
  sorry

/-- Real.log is unbounded above. -/
theorem log_tendsto_atTop : Filter.Tendsto Real.log Filter.atTop Filter.atTop := by
  sorry

/-- 3 / log k tends to 0. -/
theorem three_div_log_tendsto_zero :
    Filter.Tendsto (fun k : ℕ => (3 : ℝ) / Real.log k) Filter.atTop (nhds 0) := by
  sorry

/-- 3 * k / log k is o(k). -/
theorem three_k_div_log_isLittleO :
    (fun k : ℕ => (3 : ℝ) * k / Real.log k) =o[Filter.atTop] (fun k : ℕ => (k : ℝ)) := by
  sorry

end Erdos961Aristotle
