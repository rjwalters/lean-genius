/-!
# Erdős Problem #155: Slow Growth of Maximum Sidon Subsets

Let F(N) be the size of the largest Sidon (B₂) subset of {1, ..., N}.
Is it true that for every k ≥ 1, F(N+k) ≤ F(N) + 1 for all
sufficiently large N?

## Background
A Sidon set (B₂ set) is a set of integers where all pairwise sums are
distinct. F(N) ~ N^{1/2} (Erdős–Turán 1941), but the fine growth
structure is poorly understood.

## Stronger Form
Erdős suggested this may hold with k ≈ ε·N^{1/2}, meaning F can
increase by at most 1 over intervals of length proportional to √N.

## Known Bounds
- F(N) = (1 + o(1))·N^{1/2} (Erdős–Turán upper, Lindström/Cilleruelo lower)
- F(N) ≤ N^{1/2} + N^{1/4} + 1 (Lindström 1969)

## Status: OPEN

Reference: https://erdosproblems.com/155
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A Sidon set (B₂ set): a set of natural numbers where all pairwise sums
    a + b (a ≤ b, a, b ∈ S) are distinct. Equivalently, all pairwise
    differences are distinct. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- F(N): the size of the largest Sidon subset of {1, ..., N}. -/
axiom maxSidonSize (N : ℕ) : ℕ

/-- F(N) is achieved: there exists a Sidon subset of {1,...,N} of size F(N). -/
axiom maxSidon_achievable (N : ℕ) :
    ∃ S : Finset ℕ, IsSidonSet S ∧ (∀ x ∈ S, 1 ≤ x ∧ x ≤ N) ∧ S.card = maxSidonSize N

/-- F(N) is optimal: no Sidon subset of {1,...,N} is larger. -/
axiom maxSidon_optimal (N : ℕ) (S : Finset ℕ)
    (hsidon : IsSidonSet S) (hrange : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N) :
    S.card ≤ maxSidonSize N

/-! ## Monotonicity -/

/-- F is monotone nondecreasing: F(N) ≤ F(N+1). -/
axiom maxSidon_monotone (N : ℕ) : maxSidonSize N ≤ maxSidonSize (N + 1)

/-- F increases by at most 1 in each step: F(N+1) ≤ F(N) + 1. -/
axiom maxSidon_step (N : ℕ) : maxSidonSize (N + 1) ≤ maxSidonSize N + 1

/-! ## Asymptotic Bounds -/

/-- Erdős–Turán (1941): F(N) ≤ N^{1/2} + O(N^{1/4}).
    More precisely, F(N) ≤ √N + √(N)^{1/2} + 1 (Lindström 1969). -/
axiom erdos_turan_upper (N : ℕ) (hN : N ≥ 1) :
    (maxSidonSize N : ℝ) ≤ Real.sqrt (N : ℝ) + (N : ℝ) ^ ((1 : ℝ) / 4) + 1

/-- Lower bound: F(N) ≥ (1 - o(1))·√N.
    Singer's construction and refinements give Sidon sets of size ~√N. -/
axiom sidon_lower_asymptotic :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (maxSidonSize N : ℝ) ≥ (1 - ε) * Real.sqrt (N : ℝ)

/-! ## The Main Conjecture -/

/-- Erdős Problem #155: For every k ≥ 1, F(N+k) ≤ F(N) + 1
    for all sufficiently large N.

    This says F(N) can increase by at most 1 over any fixed-length
    interval [N, N+k], once N is large enough (depending on k). -/
axiom erdos_155_conjecture (k : ℕ) (hk : k ≥ 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → maxSidonSize (N + k) ≤ maxSidonSize N + 1

/-! ## Stronger Form -/

/-- The stronger conjecture: F(N+k) ≤ F(N) + 1 holds even for
    k ≈ ε·√N, i.e., F increases by at most 1 over intervals
    of length proportional to √N. -/
axiom erdos_155_strong (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      maxSidonSize (N + Nat.floor (ε * Real.sqrt (N : ℝ))) ≤ maxSidonSize N + 1

/-! ## Consequences -/

/-- If the conjecture holds, then F(N+1) = F(N) for "most" values of N:
    the set of N where F increases has density 0. -/
axiom increase_points_sparse :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ M : ℕ, M ≥ N₀ →
      (Finset.card (Finset.filter
        (fun N => maxSidonSize (N + 1) > maxSidonSize N)
        (Finset.range M)) : ℝ) ≤ (1 + ε) * Real.sqrt (M : ℝ)

/-! ## Small Values (OEIS A003022) -/

/-- Known small values of F(N):
    F(1)=1, F(2)=2, F(3)=3, F(4)=3, F(5)=3, F(6)=4,
    F(11)=5, F(18)=6, F(26)=7. -/
axiom small_values :
    maxSidonSize 1 = 1 ∧ maxSidonSize 2 = 2 ∧ maxSidonSize 3 = 3 ∧
    maxSidonSize 6 = 4 ∧ maxSidonSize 11 = 5 ∧ maxSidonSize 18 = 6
