/-
  Aristotle targets for Erdos860Problem (Erdős #860: Prime Covering Intervals)
  Routine supporting lemmas for automated proof search.
  See Erdos860Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open problem (exact asymptotics of h(n))
  - NOT the deep axioms (Erdős-Selfridge, Ruzsa, Erdős-Pomerance, h_universal)
  - Routine corollaries: extracting concrete bounds from stated axioms
  - No definition sorries (def h has a sorry argument — excluded), no new axioms

  Targets:
  1. linear_lower_bound': ∃ c > 0, ∀ᶠ n in atTop, (h n : ℝ) ≥ c * n
     Direct corollary of erdos_selfridge_lower_bound with ε = 0.1:
     - erdos_selfridge_lower_bound 0.1 gives ∃ N, ∀ n ≥ N, (h n : ℝ) > 2.9 * n
     - Converting > to ≥ and using Filter.eventually_atTop gives the result
     - Witness c = 2.9

  2. subquadratic_upper_bound': (fun n => (h n : ℝ)) =o[atTop] (fun n => (n : ℝ)^2)
     Follows from erdos_pomerance_upper_bound (h n = O(n^(3/2) / (log n)^(1/2))):
     - Get C > 0 with h n ≤ C * n^(3/2) / (Real.log n)^(1/2) eventually
     - For any c > 0, eventually C * n^(3/2) / (Real.log n)^(1/2) ≤ c * n^2
     - This holds since n^(3/2) / n^2 = 1/n^(1/2) → 0 and (Real.log n)^(1/2) ≥ 1 for large n
     - So h n / n^2 ≤ C / n^(1/2) → 0

  Excluded (definition sorries — Aristotle skips):
  - h (n : ℕ) : ℕ := Nat.find (... by sorry ...) — definition sorry
  - The main open problem: exact asymptotics of h(n)/n
-/
import Mathlib
import Proofs.Erdos860Problem

namespace Erdos860.Aristotle

open Erdos860 Nat Filter Asymptotics Real

-- ============================================================
-- Aristotle Target 1: Linear lower bound
-- ============================================================

/-- **Linear lower bound for h(n)** (Aristotle target):
    There exists c > 0 such that h(n) ≥ c·n for all sufficiently large n.

    Proof sketch:
    1. Apply erdos_selfridge_lower_bound with ε = 0.1 to get ∃ N, ∀ n ≥ N, (h n : ℝ) > 2.9 * n
    2. Use Filter.eventually_atTop.mpr with witness N to convert to ∀ᶠ form
    3. Use le_of_lt to convert strict > to ≥
    4. Use c = 2.9 as the witness -/
theorem linear_lower_bound' :
    ∃ c > 0, ∀ᶠ n in atTop, (h n : ℝ) ≥ c * n := by
  sorry

-- ============================================================
-- Aristotle Target 2: Subquadratic upper bound
-- ============================================================

/-- **h(n) = o(n²)** (Aristotle target):
    The covering function h(n) grows strictly slower than n².

    Proof sketch:
    1. From erdos_pomerance_upper_bound: ∃ C > 0, ∀ᶠ n in atTop,
       (h n : ℝ) ≤ C * n ^ (3/2 : ℝ) / Real.log n ^ (1/2 : ℝ)
    2. Fix any c > 0. Need to show: eventually ‖(h n : ℝ)‖ ≤ c * ‖(n : ℝ)^2‖
    3. Since h n ≥ 0 and n ≥ 0, reduce to: h n ≤ c * n^2 eventually
    4. From step 1: h n ≤ C * n^(3/2) / (log n)^(1/2) eventually
    5. Key inequality: C * n^(3/2) / (log n)^(1/2) ≤ c * n^2 eventually
       (i.e., C / (n^(1/2) * (log n)^(1/2)) ≤ c eventually, since LHS → 0) -/
theorem subquadratic_upper_bound' :
    (fun n => (h n : ℝ)) =o[atTop] (fun n => (n : ℝ) ^ 2) := by
  sorry

end Erdos860.Aristotle
