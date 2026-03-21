/-
  Erdős Problem #18: Practical Numbers

  Source: https://erdosproblems.com/18
  Status: OPEN
  Prize: $250

  Definition:
  A positive integer m is **practical** if every integer n with 1 ≤ n < m
  can be expressed as a sum of distinct divisors of m.

  Examples:
  - 12 is practical: divisors {1,2,3,4,6,12}, and 5=1+4, 7=1+6, 8=2+6, etc.
  - 1, 2, 4, 6, 8, 12, 16, 18, 20, 24, ... (OEIS A005153)

  Let h(m) = minimum number of divisors of m needed such that every n < m
  can be represented as a sum of distinct elements from those divisors.

  Questions:
  1. Are there infinitely many practical m where h(m) < (log log m)^O(1)?
  2. Is h(n!) < n^o(1), or even h(n!) < (log n)^O(1)?

  Known Results:
  - Erdős: h(n!) < n
  - Vose (1985): ∃ infinitely many practical m with h(m) ≪ (log m)^(1/2)
  - Stewart-Sierpiński: Complete characterization via prime factorization

  References:
  - Srinivasan (1948): Original definition
  - Stewart (1954), Sierpiński (1955): Characterization
  - Vose (1985): Bounds on h(m)
  - OEIS A005153
-/

import Mathlib.Tactic

open Set Finset Function Nat

namespace Erdos18

/- ## Divisor Operations -/

/-- The set of divisors of n. -/
def divisors (n : ℕ) : Finset ℕ := n.divisors

/-- Sum of a subset of divisors. -/
def divisorSubsetSum (n : ℕ) (S : Finset ℕ) : ℕ := S.sum id

/-- A number k is representable by divisors of m if k equals a sum of
    distinct divisors of m. -/
def IsRepresentable (k m : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ divisors m ∧ S.sum id = k

/- ## Practical Numbers -/

/--
**Practical Number**: A positive integer m is practical if every positive
integer k < m can be expressed as a sum of distinct divisors of m.

Also called "panarithmic numbers". Defined by Srinivasan (1948).
-/
def IsPractical (m : ℕ) : Prop :=
  m ≥ 1 ∧ ∀ k : ℕ, 1 ≤ k → k < m → IsRepresentable k m

/-- The set of practical numbers. -/
def PracticalNumbers : Set ℕ := { m | IsPractical m }

/- ## Basic Examples -/

/-- 1 is trivially practical (no k in range [1, 0)). -/
theorem one_practical : IsPractical 1 := by
  constructor
  · omega
  · intro k hk1 hkm
    omega

/-- 2 is practical: only need to represent 1, and 1 divides 2. -/
theorem two_practical : IsPractical 2 := by
  constructor
  · omega
  · intro k hk1 hkm
    interval_cases k
    exact ⟨{1}, by simp [divisors], rfl⟩

/- ## Non-Practical Numbers -/

/- ## Stewart-Sierpiński Characterization -/

/- ## The h(m) Function -/

/--
**h(m)**: The minimum number of divisors of m needed such that every
positive integer k < m can be represented as a sum of distinct elements
from those divisors.

For practical m, h(m) ≤ d(m) where d(m) is the number of divisors.
The question is how small h(m) can be.
-/
noncomputable def h (m : ℕ) : ℕ :=
  sInf { s : ℕ | ∃ S : Finset ℕ, S ⊆ divisors m ∧ S.card = s ∧
    ∀ k, 1 ≤ k → k < m → ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = k }

/- ## Known Bounds on h(m) -/

/- ## The Main Conjectures -/

/--
**Erdős Problem #18, Part 1**:
Are there infinitely many practical m where h(m) < (log log m)^O(1)?

This asks whether h(m) can be doubly-logarithmically bounded
for infinitely many m.
-/
def conjecture_part1 : Prop :=
  ∃ C : ℝ, C > 0 ∧
  Set.Infinite { m : ℕ | IsPractical m ∧
    (h m : ℝ) < (Real.log (Real.log m))^C }

/--
**Erdős Problem #18, Part 2** (Prize: $250):
Is h(n!) < n^o(1)?

This asks whether h(n!) grows slower than any positive power of n.
Even stronger: is h(n!) < (log n)^O(1)?
-/
def conjecture_part2_weak : Prop :=
  ∀ ε : ℝ, ε > 0 →
  ∃ N : ℕ, ∀ n ≥ N, (h n.factorial : ℝ) < n^ε

def conjecture_part2_strong : Prop :=
  ∃ C : ℝ, C > 0 ∧
  ∃ N : ℕ, ∀ n ≥ N, (h n.factorial : ℝ) < (Real.log n)^C

/- ## Density of Practical Numbers -/

/-- Count of practical numbers up to x. -/
noncomputable def practicalCount (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun m => @Decidable.decide (IsPractical m) (Classical.dec _)) |>.card

/- ## Properties of Practical Numbers -/

/- ## Goldbach-Type Results for Practical Numbers -/

/- ## Connection to Egyptian Fractions -/

/- ## The OEIS Sequence -/

/-- First several practical numbers (OEIS A005153). -/
def knownPracticalNumbers : List ℕ :=
  [1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, 32, 36, 40, 42, 48]

/- ## Why This Problem is Hard -/

end Erdos18

/-
  ## Summary

  **Problem Status: OPEN**

  Erdős Problem #18 asks about the function h(m) for practical numbers:
  the minimum number of divisors needed to represent all k < m.

  **Definition**: m is practical if every k < m is a sum of distinct divisors of m.

  **Key Question**: Is h(n!) < n^o(1)? (Prize: $250)

  **Known Results**:
  - Erdős: h(n!) < n
  - Vose (1985): Infinitely many m with h(m) ≪ √(log m)
  - Stewart-Sierpiński: Complete characterization of practical numbers

  **Related Facts**:
  - Practical numbers have density 0
  - Practical Goldbach: every even n is sum of two practical numbers
  - All factorials and primorials are practical

  **Why Hard**:
  - Finding minimum representing subsets is computationally difficult
  - Requires understanding fine structure of divisors of n!

  References:
  - Srinivasan (1948): Definition
  - Stewart, Sierpiński (1954-55): Characterization
  - Vose (1985): Bounds
  - OEIS A005153
-/
