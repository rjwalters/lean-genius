/-
  Aristotle targets for Erdős Problem #160: Rainbow-Free Colorings of APs
  Routine supporting lemmas for automated proof search.
  See Erdos160Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open problem (exact growth rate of h(N) is open)
  - NOT the deep published bounds (upper_bound_two_thirds, lower_bound_exp — axioms)
  - Derivable consequences of the known axiomatized bounds
  - Standard real analysis: rpow monotonicity, exp/log Filter.Tendsto facts
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (2):
  - h_sublinear_ari: for ε ∈ (0, 1/3), h(n) ≤ n^(1-ε) for large n
    (follows from upper_bound_two_thirds: h(n) ≤ C·n^(2/3), and 2/3 < 1-ε when ε < 1/3)
  - h_superlog_ari: h grows without bound (from lower_bound_exp: h(n) ≥ exp(c·(log n)^(1/9)) → ∞)
-/
import Proofs.Erdos160Problem
import Mathlib

namespace Erdos160Aristotle

open Erdos160 Real Filter

/-
## Section 1: h is sublinear for small ε

From upper_bound_two_thirds: ∃ C > 0, ∀ n ≥ 1, h(n) ≤ C·n^(2/3).
For ε < 1/3, we have 2/3 < 1-ε. For large enough n, C·n^(2/3) ≤ n^(1-ε)
because n^(1-ε-2/3) = n^(1/3-ε) → ∞.
-/

/-- For ε ∈ (0, 1/3), h(n) ≤ n^(1-ε) eventually.
Follows from the two-thirds upper bound: h(n) ≤ C·n^(2/3), and C·n^(2/3) ≤ n^(1-ε)
for large n since 2/3 < 1-ε (i.e., 1/3 > ε). -/
theorem h_sublinear_ari : ∀ ε > (0 : ℝ), ε < 1/3 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (h n : ℝ) ≤ (n : ℝ) ^ (1 - ε) := by
  sorry

/-
## Section 2: h grows without bound

From lower_bound_exp: ∃ c > 0, ∀ n ≥ 2, h(n) ≥ exp(c·(log n)^(1/9)).
Since exp(c·(log n)^(1/9)) → ∞ as n → ∞ (as (log n)^(1/9) → ∞),
h(n) → ∞ as well.
-/

/-- h grows without bound: for every C, h(n) ≥ C for all sufficiently large n.
Proof: the exponential lower bound exp(c·(log n)^(1/9)) → ∞. -/
theorem h_superlog_ari : ∀ C : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (h n : ℝ) ≥ C := by
  sorry

end Erdos160Aristotle
