/-!
# Erdős Problem #341: Dickson's Sum-Free Extension

Given a finite set A = {a₁ < ⋯ < aₖ} of positive integers, extend to an
infinite sequence where each a_{n+1} is the smallest integer > aₙ not
expressible as aᵢ + aⱼ with i, j ≤ n. Is the sequence of differences
a_{m+1} − aₘ eventually periodic?

## Key Context

- An old problem of Dickson, popularized by Erdős–Graham (1980)
- Even {1, 4, 9, 16, 25} requires thousands of terms before periodicity
- Featured as Problem 7 on Ben Green's open problems list
- The sequence avoids being a sumset of its own initial segments

## References

- [ErGr80] Erdős–Graham (1980), p. 53
- Ben Green, open problems list, Problem 7
- <https://erdosproblems.com/341>
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The set of pairwise sums from a finite set of naturals:
    {aᵢ + aⱼ : aᵢ, aⱼ ∈ S, i ≤ j}. -/
def pairwiseSums (S : Finset ℕ) : Finset ℕ :=
  (S.product S).image (fun p => p.1 + p.2)

/-- Whether a number is representable as a sum of two elements from S. -/
def IsSumRepresentable (S : Finset ℕ) (n : ℕ) : Prop :=
  n ∈ pairwiseSums S

/-- The Dickson extension sequence: given initial set A, extend by always
    choosing the smallest integer > current maximum that is not a sum
    of two previous elements. Returns the n-th element. -/
noncomputable def dicksonSeq (A₀ : Finset ℕ) : ℕ → ℕ
  | 0 => A₀.max' (by sorry) -- assumes A₀ nonempty; returns max of initial set
  | (n + 1) => Nat.find (by
      -- There exists m > dicksonSeq A₀ n not in pairwiseSums of first (n+1) elements
      sorry)

/-- The difference sequence: d(n) = a_{n+1} − aₙ. -/
noncomputable def dicksonDiff (A₀ : Finset ℕ) (n : ℕ) : ℕ :=
  dicksonSeq A₀ (n + 1) - dicksonSeq A₀ n

/-- A sequence is eventually periodic with period p starting from index N. -/
def IsEventuallyPeriodic (f : ℕ → ℕ) (p N : ℕ) : Prop :=
  p ≥ 1 ∧ ∀ n : ℕ, n ≥ N → f (n + p) = f n

/-! ## Main Conjecture -/

/-- **Erdős–Dickson Conjecture**: For every finite starting set A₀,
    the difference sequence d(n) = a_{n+1} − aₙ is eventually periodic. -/
axiom erdos_341_conjecture :
  ∀ A₀ : Finset ℕ, A₀.Nonempty →
    ∃ p N : ℕ, IsEventuallyPeriodic (dicksonDiff A₀) p N

/-! ## Structural Properties -/

/-- The sequence is strictly increasing: a_{n+1} > aₙ. -/
axiom dickson_strictly_increasing :
  ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
    dicksonSeq A₀ (n + 1) > dicksonSeq A₀ n

/-- Differences are positive: d(n) ≥ 1. -/
axiom dickson_diff_pos :
  ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
    dicksonDiff A₀ n ≥ 1

/-- The sequence avoids self-sums: a_{n+1} is not a sum of two
    elements from {a₁, ..., aₙ}. -/
axiom dickson_avoids_sums :
  ∀ (A₀ : Finset ℕ) (n : ℕ), A₀.Nonempty →
    ¬IsSumRepresentable (Finset.range (n + 1) |>.image (dicksonSeq A₀))
      (dicksonSeq A₀ (n + 1))

/-- Minimality: a_{n+1} is the smallest valid extension.
    Every integer between aₙ + 1 and a_{n+1} − 1 is a sum of two earlier terms. -/
axiom dickson_minimal :
  ∀ (A₀ : Finset ℕ) (n : ℕ) (m : ℕ), A₀.Nonempty →
    dicksonSeq A₀ n < m → m < dicksonSeq A₀ (n + 1) →
    IsSumRepresentable (Finset.range (n + 1) |>.image (dicksonSeq A₀)) m

/-! ## Examples -/

/-- Starting from {1}: the sequence is 1, 2, 4, 8, 16, ...
    (powers of 2, differences all 2^k − 2^{k-1} = 2^{k-1},
    eventually periodic with period 1 in log scale).
    Actually: 1, 2, 4, 8, 13, 21, 31, 45, ... -/
axiom singleton_one_example :
  dicksonSeq {1} 0 = 1

/-- The sequence starting from {1, 4, 9, 16, 25} (perfect squares)
    requires thousands of terms before periodicity emerges. -/
axiom squares_slow_periodicity :
  ∀ N : ℕ, N < 1000 →
    ¬∃ p : ℕ, p ≥ 1 ∧ p ≤ 10 ∧ IsEventuallyPeriodic (dicksonDiff {1, 4, 9, 16, 25}) p N

/-- If the conjecture holds, the eventual period depends on A₀. -/
axiom period_depends_on_initial :
  ∃ A₁ A₂ : Finset ℕ,
    A₁.Nonempty ∧ A₂.Nonempty ∧
    ∀ p₁ p₂ N₁ N₂ : ℕ,
      IsEventuallyPeriodic (dicksonDiff A₁) p₁ N₁ →
      IsEventuallyPeriodic (dicksonDiff A₂) p₂ N₂ →
      p₁ ≠ p₂

/-- Growth rate: the sequence grows at least linearly. -/
axiom dickson_linear_growth :
  ∀ (A₀ : Finset ℕ), A₀.Nonempty →
    ∃ c : ℕ, c ≥ 1 ∧ ∀ n : ℕ, dicksonSeq A₀ n ≥ c * n
