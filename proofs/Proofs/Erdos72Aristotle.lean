/-
  Aristotle targets for Erdős Problem #72 (Unavoidable Cycle Lengths)
  Routine density lemmas for automated proof search.
  See Erdos72Problem.lean for the main formalization.

  Criteria for inclusion:
  - powersOfTwo_density_zero: |{2^k ≤ n}|/n → 0 (count = O(log n))
  - arithmeticProgression_positive_density: AP has density 1/d > 0
  - perfectSquares_density_zero: |{k² ≤ n}|/n = √n/n → 0
  - NOT isStronglyUnavoidable (main open problem direction)
  - NOT Liu-Montgomery theorem (axiom — deep research result)
-/
import Mathlib

namespace Erdos72Aristotle

open Filter Real Finset

/-- The counting function for a set A up to n. -/
def countingFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.filter (· ∈ A) (Finset.range (n + 1))).card

/-- A set A ⊂ ℕ has density 0 if |A ∩ [0,n]|/n → 0 as n → ∞. -/
def hasDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ => (countingFunction A n : ℝ) / n) atTop (nhds 0)

/-- Powers of 2: {1, 2, 4, 8, 16, ...}. -/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

/-- Arithmetic progression with common difference d starting at a. -/
def arithmeticProgression (a d : ℕ) : Set ℕ := {n | ∃ k : ℕ, n = a + k * d}

/-- Perfect squares: {0, 1, 4, 9, 16, ...}. -/
def perfectSquares : Set ℕ := {n | ∃ k : ℕ, n = k ^ 2}

-- Routine: Powers of 2 have density 0.
-- Key bound: |{2^k ≤ n}| ≤ Nat.log 2 n + 1 = O(log n).
-- Since log n / n → 0, the density is 0.
-- Proof: countingFunction powersOfTwo n ≤ Nat.log 2 n + 1 (each 2^k ≤ n
-- gives k ≤ log₂ n), and (Nat.log 2 n + 1 : ℝ) / n → 0 by log growth.
theorem powersOfTwo_density_zero : hasDensityZero powersOfTwo := by
  sorry

-- Routine: Arithmetic progressions have positive density, not 0.
-- Key bound: countingFunction (arithmeticProgression a d) n ≥ n/d - 1
-- for large n. So the ratio stays ≥ 1/(d+1) > 0. Not a density-0 set.
-- Proof: ¬ Tendsto (.../n) atTop (nhds 0) since liminf ≥ 1/d > 0.
theorem arithmeticProgression_positive_density (a d : ℕ) (hd : d > 0) :
    ¬hasDensityZero (arithmeticProgression a d) := by
  sorry

-- Routine: Perfect squares have density 0.
-- Key bound: countingFunction perfectSquares n ≤ Nat.sqrt n + 1
-- (each k² ≤ n gives k ≤ √n), and (√n + 1)/n = 1/√n + 1/n → 0.
-- Uses: Nat.sqrt_le_self, Real.tendsto_inv_atTop_zero, squeeze.
theorem perfectSquares_density_zero : hasDensityZero perfectSquares := by
  sorry

end Erdos72Aristotle
