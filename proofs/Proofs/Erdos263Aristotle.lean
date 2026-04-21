/-
  Aristotle targets for Erdős Problem #263 (Irrationality Sequences)
  Helper lemmas for the integer-gap proof of doubleExp_sum_irrational.
  See Stubs/Erdos263Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main doubleExp_sum_irrational theorem (OPEN problem)
  - Supporting lemmas for the integer-gap argument that should be decidable
  - No definition sorries
  - No axioms

  Included targets (3):
  - doubleExp_tail_pos: Tail ∑' k, 1/2^{2^(k+N+1)} is positive
  - doubleExp_tail_bound: 2^{2^N} * tail < 1 / (2^{2^N} - 1)
  - tsum_split_at: ∑' n, f n = ∑ n < N, f n + f N + ∑' n, f (n + N + 1)
-/
import Mathlib

open Real

namespace Erdos263Aristotle

-- Positive tail: each term 1/2^{2^(k+N+1)} is positive, so the tsum is positive.
theorem doubleExp_tail_pos (N : ℕ) :
    0 < ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) := by
  sorry

-- Tail bound: 2^{2^N} * Σ_{k≥0} 1/2^{2^(k+N+1)} < 1 / (2^{2^N} - 1).
-- Geometric bound: each term 1/2^{2^(k+N+1)} ≤ (1/2^{2^N})^k / 2^{2^N},
-- so D * tail ≤ Σ_{k≥0} (1/D)^k * 1 = 1/(1 - 1/D) * 1/D... refined bound gives < 1/(D-1).
theorem doubleExp_tail_bound (N : ℕ) :
    (2 : ℝ) ^ (2 ^ N) * ∑' k : ℕ, (1 : ℝ) / (2 : ℝ) ^ (2 ^ (k + N + 1)) <
    1 / ((2 : ℝ) ^ (2 ^ N) - 1) := by
  sorry

-- Sum splitting: ∑' n, f n = (∑ n in range N, f n) + f N + ∑' n, f (n + N + 1).
-- This is a standard Mathlib result (tsum_eq_zero_add, sum_add_tsum_compl, etc.).
theorem tsum_split_at (f : ℕ → ℝ) (hf : Summable f) (N : ℕ) :
    ∑' n, f n = (∑ n ∈ Finset.range N, f n) + f N + ∑' n, f (n + N + 1) := by
  sorry

end Erdos263Aristotle
