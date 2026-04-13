/-
  Aristotle targets for BaselProblemOQ01OQ01OQ02 (Apéry's ζ(3) irrationality scaffold)
  Routine supporting lemmas for automated proof search.
  See BaselProblemOQ01OQ01OQ02.lean for the main formalization.

  Targets (in order of tractability):
  1. aperyB_pos: All Apéry b-numbers are positive (sum of positive terms)
  2. harmonicNumber_mono: H_n is monotone (trivial from range_mono)
  3. lcmUpTo_pos: lcm(1,...,n) > 0 for n ≥ 1 (n divides lcm)
  4. apery_char_poly_roots: 34^2 - 4 = 1152 (norm_num)
  5. nair_lcm_bound: lcm(1,...,n) ≤ 4^n (Nair 1982 elementary bound)

  Not targeted (too deep or require WZ-theory):
  - aperyB_recurrence: requires Zeilberger's WZ-theory
  - aperyB_growth_upper: requires recurrence first
  - apery_theorem: Apéry 1978 irrationality, not in Mathlib
  - denominator_control: requires a-sequence formula
-/
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

open BigOperators Finset Nat

namespace AperyZetaThreeAristotle

/-- The Apéry b-sequence: bₙ = ∑_{k=0}^{n} C(n,k)² C(n+k,k)². -/
def aperyB (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), (n.choose k) ^ 2 * ((n + k).choose k) ^ 2

/-- lcm(1, 2, ..., n). -/
def lcmUpTo (n : ℕ) : ℕ :=
  (Finset.range n).lcm (· + 1)

/-- The harmonic number H_n = ∑_{k=1}^{n} 1/k. -/
noncomputable def harmonicNumber (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 : ℚ) / (k + 1)

/-- All Apéry b-numbers are positive. -/
theorem aperyB_pos (n : ℕ) : 0 < aperyB n := by
  sorry

/-- Harmonic numbers are non-negative. -/
theorem harmonicNumber_nonneg (n : ℕ) : 0 ≤ harmonicNumber n := by
  sorry

/-- Harmonic numbers are monotone increasing. -/
theorem harmonicNumber_mono (m n : ℕ) (hmn : m ≤ n) :
    harmonicNumber m ≤ harmonicNumber n := by
  sorry

/-- lcm(1,...,n) is positive for n ≥ 1. -/
theorem lcmUpTo_pos (n : ℕ) (hn : 1 ≤ n) : 0 < lcmUpTo n := by
  sorry

/-- **Nair's bound (1982)**: lcm(1, 2, ..., n) ≤ 4^n.
    This elementary bound replaces the prime number theorem in Apéry's proof.
    Proof: lcm(1,...,n) | C(2n, n) ≤ 2^{2n} = 4^n via the ballot integral. -/
theorem nair_lcm_bound (n : ℕ) : lcmUpTo n ≤ 4 ^ n := by
  sorry

end AperyZetaThreeAristotle
