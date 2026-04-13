/-
  Aristotle targets for Erdős Problem #492 (Uniform Distribution Relative to Fixed Sequence)
  Routine supporting lemmas for automated proof search.
  See Erdos492Problem.lean for the main formalization.

  Targets:
  1. naturals_ratio_limit — (n+2)/(n+1) → 1 as n → ∞
  2. one_add_one_div_tendsto_one — 1 + 1/(n+1) → 1 as n → ∞
  3. nat_succ_div_self_tendsto_one — (n+1)/n → 1 as n → ∞
  4. one_div_succ_tendsto_zero — 1/(n+1) → 0 as n → ∞

  Context: These support the ratioLimit field of `naturalsSeq : UnityRatioSeq`
  which requires Filter.Tendsto (fun n => seq(n+1)/seq(n)) atTop (nhds 1)
  where seq(n) = n+1, giving the ratio (n+2)/(n+1) → 1.
-/
import Mathlib

namespace Erdos492Aristotle

open Filter Real Topology

/-- 1/(n+1) → 0 as n → ∞. -/
theorem one_div_succ_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) := by
  sorry

/-- 1 + 1/(n+1) → 1 as n → ∞. -/
theorem one_add_one_div_tendsto_one :
    Filter.Tendsto (fun n : ℕ => 1 + (1 : ℝ) / (n + 1)) Filter.atTop (nhds 1) := by
  sorry

/-- (n+2)/(n+1) → 1 as n → ∞.
    This is the key limit for naturalsSeq.ratioLimit. -/
theorem naturals_ratio_limit :
    Filter.Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

/-- (n+1)/n → 1 as n → ∞ (alternative form). -/
theorem nat_succ_div_self_tendsto_one :
    Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

/-- For any a > 0: (n+a)/n → 1 as n → ∞. -/
theorem nat_add_div_tendsto_one (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) + a) / (n : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

end Erdos492Aristotle
