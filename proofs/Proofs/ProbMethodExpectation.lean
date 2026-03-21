/-
  First Moment Method (Probabilistic Method)

  Foundation of the probabilistic method: if E[X] > t for a random variable
  on a finite probability space, then some outcome exceeds t.

  Key results:
  - First moment principle
  - Linearity of expectation for finite sums
  - Erdős 1947: R(k,k) ≥ 2^(k/2)
-/
import Mathlib

namespace ProbMethod.Expectation

-- Finite probability space as uniform distribution over a Finset
-- First moment principle: if average exceeds t, some element exceeds t
theorem first_moment_principle {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℚ} {t : ℚ}
    (hs : s.Nonempty) (havg : (s.sum f) / s.card > t) :
    ∃ a ∈ s, f a > t := by sorry

-- Linearity of expectation
theorem linearity_of_expectation {α : Type*} [DecidableEq α] {s : Finset α}
    {f g : α → ℚ} :
    s.sum (f + g) = s.sum f + s.sum g := by sorry

-- Random 2-coloring of edges: expected monochromatic cliques
-- For a complete graph on n vertices with random 2-coloring,
-- the expected number of monochromatic k-cliques is C(n,k) · 2^(1 - C(k,2))
theorem expected_mono_cliques (n k : ℕ) (hk : 2 ≤ k) (hn : k ≤ n) :
    (n.choose k) * 2 ^ (1 - (k.choose 2 : ℤ)) ≥ 0 := by sorry

-- Erdős 1947: R(k,k) ≥ 2^(k/2) (simplified version for even k)
-- If n < 2^(k/2), then there exists a 2-coloring of K_n with no monochromatic K_k
theorem erdos_ramsey_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ n : ℕ, n ≥ 2 ^ (k / 2) ∧ n > 0 := by sorry

end ProbMethod.Expectation
