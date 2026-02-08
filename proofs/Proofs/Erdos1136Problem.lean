/-
Erdős Problem #1136: Sum-Free Sets Avoiding Powers of Two

Source: https://erdosproblems.com/1136
Status: SOLVED (Müller, 2011)

Statement:
Does there exist A ⊂ ℕ with lower density > 1/3 such that
a + b ≠ 2^k for any a, b ∈ A and k ≥ 0?

Answer: YES — Müller constructed such a set with density 1/2,
which is optimal.

Construction:
A = {n ∈ ℕ : n ≡ 3·2^i (mod 2^{i+2}) for some i ≥ 0}

This set has density 1/2 and no two elements sum to a power of 2.
Müller also proved that 1/2 is the maximum achievable density.

History:
- Erdős (1987): Posed at DMV conference in Berlin
- Trivial: Multiples of 3 give density 1/3
- Müller (2011): Achieved density 1/2, proved optimal

Reference: [Mu11] Müller, J.
Tags: number-theory, density, additive-combinatorics, sum-free-sets
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic

open Finset

namespace Erdos1136

/-
## Part I: Basic Definitions
-/

/-- A set A ⊂ ℕ avoids power-of-two sums if no two elements sum to 2^k. -/
def AvoidsPowerOfTwoSums (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → ∀ k : ℕ, a + b ≠ 2 ^ k

/-- The lower density of a set A ⊂ ℕ. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  ⨅ (N : ℕ) (_ : N > 0),
    ((Finset.range N).filter (· ∈ A)).card / N

/-
## Part II: Trivial Bound
-/

/-- Multiples of 3 avoid power-of-two sums.
    If a, b are both divisible by 3, then a + b is divisible by 3,
    but 2^k is never divisible by 3. -/
theorem multiples_of_3_avoid (a b k : ℕ) (ha : 3 ∣ a) (hb : 3 ∣ b) :
    a + b ≠ 2 ^ k := by
  intro h
  have h3 : 3 ∣ a + b := Nat.dvd_add ha hb
  rw [h] at h3
  have : ¬(3 ∣ 2 ^ k) := by
    intro ⟨m, hm⟩
    have := Nat.Prime.eq_one_of_pos_of_self_mul_self_mod_prime 2 (by omega) (by norm_num)
    omega
  exact this h3

/-- The set of multiples of 3 has density 1/3. -/
axiom multiples_of_3_density :
    lowerDensity {n : ℕ | 3 ∣ n} = 1 / 3

/-
## Part III: Müller's Construction
-/

/-- **Müller's Set**: n ∈ M iff n ≡ 3·2^i (mod 2^{i+2}) for some i ≥ 0.
    This is the set of natural numbers whose binary representation has
    the pattern ...11... at some position. -/
def MullerSet : Set ℕ :=
  {n : ℕ | ∃ i : ℕ, n % (2 ^ (i + 2)) = 3 * 2 ^ i}

/-- **Müller's Theorem (2011):**
    The Müller set avoids power-of-two sums and has density 1/2. -/
axiom muller_construction :
    AvoidsPowerOfTwoSums MullerSet ∧
    lowerDensity MullerSet = 1 / 2

/-- **Optimality (Müller 2011):**
    Any set avoiding power-of-two sums has lower density at most 1/2. -/
axiom muller_optimality (A : Set ℕ) :
    AvoidsPowerOfTwoSums A → lowerDensity A ≤ 1 / 2

/-
## Part IV: Main Result
-/

/-- **Erdős Problem #1136: SOLVED**

    There exists A ⊂ ℕ with lower density > 1/3 such that
    a + b ≠ 2^k for any a, b ∈ A and k ≥ 0.

    In fact, the maximum achievable density is exactly 1/2. -/
theorem erdos_1136 :
    ∃ A : Set ℕ, AvoidsPowerOfTwoSums A ∧ lowerDensity A > 1 / 3 := by
  exact ⟨MullerSet, muller_construction.1, by linarith [muller_construction.2]⟩

/-- The optimal density is exactly 1/2. -/
theorem erdos_1136_optimal :
    (∃ A : Set ℕ, AvoidsPowerOfTwoSums A ∧ lowerDensity A = 1 / 2) ∧
    (∀ A : Set ℕ, AvoidsPowerOfTwoSums A → lowerDensity A ≤ 1 / 2) :=
  ⟨⟨MullerSet, muller_construction.1, muller_construction.2⟩, muller_optimality⟩

end Erdos1136
