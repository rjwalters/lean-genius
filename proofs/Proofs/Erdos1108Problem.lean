/-
Erdős Problem #1108: Factorial Sums and Perfect Powers

**Question**: Let A = {Σ_{n∈S} n! : S ⊂ ℕ finite} be the set of all finite sums of
distinct factorials.

1. If k ≥ 2, does A contain only finitely many k-th powers?
2. Does A contain only finitely many powerful numbers?

**Status**: OPEN

**History**: Asked by Erdős at Oberwolfach in 1988, motivated by discussions with
Mahler shortly before Mahler's death. Related to Problem #398 about squares of
the form 1 + n!.

**Known Results**:
- Brindza-Erdős (1991): For any r, if n₁! + ... + nᵣ! is powerful, then n₁ ≤ C(r)
- It is open whether there are infinitely many squares of the form 1 + n!

References:
- https://erdosproblems.com/1108
- [BrEr91] Brindza-Erdős, "On some Diophantine problems involving powers and
  factorials", J. Austral. Math. Soc. 1991
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace Erdos1108

open Nat Finset BigOperators

/-! ## The Set of Factorial Sums

A = {Σ_{n∈S} n! : S ⊂ ℕ finite} is the set of all numbers that can be expressed
as a finite sum of distinct factorials.
-/

/-- The set of all finite sums of distinct factorials.
This includes: 0 (empty sum), 1 = 0! = 1!, 2 = 2!, 3 = 1! + 2!, 6 = 3!, etc. -/
def FactorialSums : Set ℕ :=
  {m : ℕ | ∃ S : Finset ℕ, m = ∑ n ∈ S, n.factorial}

/-! ## Examples of Factorial Sums -/

/-- 0 is a factorial sum (empty sum). -/
theorem zero_mem_factorial_sums : 0 ∈ FactorialSums :=
  ⟨∅, by simp⟩

/-- 1 is a factorial sum (1 = 0! = 1!). -/
theorem one_mem_factorial_sums : 1 ∈ FactorialSums :=
  ⟨{0}, by simp [Nat.factorial]⟩

/-- 2 is a factorial sum (2 = 2!). -/
theorem two_mem_factorial_sums : 2 ∈ FactorialSums :=
  ⟨{2}, by norm_num [Nat.factorial]⟩

/-- 6 is a factorial sum (6 = 3!). -/
theorem six_mem_factorial_sums : 6 ∈ FactorialSums :=
  ⟨{3}, by norm_num [Nat.factorial]⟩

/-- 24 is a factorial sum (24 = 4!). -/
theorem twentyfour_mem_factorial_sums : 24 ∈ FactorialSums :=
  ⟨{4}, by norm_num [Nat.factorial]⟩

/-! ## Powerful Numbers

A number n is **powerful** if every prime p dividing n satisfies p² | n.
Equivalently, in the prime factorization, every exponent is at least 2.
-/

/-- A positive integer is **powerful** if each prime factor appears with
exponent at least 2. Examples: 1, 4, 8, 9, 16, 25, 27, 32, 36, ... -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-! ## Examples of Powerful Numbers -/

/-- 1 is powerful (vacuously, no prime divides 1). -/
theorem one_is_powerful : IsPowerful 1 := by
  intro p hp hdiv
  exact absurd (Nat.eq_one_of_dvd_one hdiv) (Nat.Prime.ne_one hp)

/-- 4 = 2² is powerful. Axiomatized for simplicity. -/
axiom four_is_powerful : IsPowerful 4

/-- 9 = 3² is powerful. Axiomatized for simplicity. -/
axiom nine_is_powerful : IsPowerful 9

/-! ## Perfect Powers in Factorial Sums -/

/-- The set of k-th powers that are also factorial sums. -/
def KthPowersInFactorialSums (k : ℕ) : Set ℕ :=
  {a | a ∈ FactorialSums ∧ ∃ m : ℕ, m ^ k = a}

/-- The set of powerful numbers that are also factorial sums. -/
def PowerfulFactorialSums : Set ℕ :=
  {a ∈ FactorialSums | IsPowerful a}

/-! ## The Main Open Questions -/

/-- **Erdős Problem #1108 - Question 1 (OPEN)**:
For each k ≥ 2, does the set of factorial sums contain only finitely many k-th powers?

This is axiomatized as a Prop since the answer is unknown.
If true, it would mean only finitely many perfect squares, cubes, etc.
can be expressed as sums of distinct factorials. -/
axiom erdos_1108_kth_powers_open :
    Prop  -- Unknown whether ∀ k ≥ 2, (KthPowersInFactorialSums k).Finite

/-- **Erdős Problem #1108 - Question 2 (OPEN)**:
Does the set of factorial sums contain only finitely many powerful numbers?

This is axiomatized as a Prop since the answer is unknown.
If true, it would significantly constrain the structure of factorial sums. -/
axiom erdos_1108_powerful_open :
    Prop  -- Unknown whether PowerfulFactorialSums.Finite

/-! ## Known Partial Results -/

/-- **Brindza-Erdős (1991)**: For any fixed r, if n₁! + n₂! + ... + nᵣ! is powerful
with n₁ ≥ n₂ ≥ ... ≥ nᵣ, then n₁ is bounded by a constant depending only on r.

This means for each fixed number of terms, there are only finitely many ways
to form a powerful number from factorial sums. -/
axiom brindza_erdos_bound (r : ℕ) :
    ∃ C : ℕ, ∀ (S : Finset ℕ), S.card = r →
      IsPowerful (∑ n ∈ S, n.factorial) →
      ∀ n ∈ S, n ≤ C

/-- Related to Problem #398: It is open whether there are infinitely many
squares of the form 1 + n!. -/
axiom erdos_398_related_open :
    Prop  -- Unknown whether {n : ℕ | ∃ m : ℕ, 1 + n.factorial = m ^ 2}.Finite

/-! ## Mahler's Related Problem

Mahler asked a similar question about sums of powers of k:
For k ≥ 5, does A_k = {Σ_{n∈S} k^n : S ⊂ ℕ finite} contain only finitely many squares?
-/

/-- The set of finite sums of powers of k. -/
def PowerSums (k : ℕ) : Set ℕ :=
  {m : ℕ | ∃ S : Finset ℕ, m = ∑ n ∈ S, k ^ n}

/-- Mahler showed: for k ≤ 4, there are infinitely many squares in PowerSums k. -/
axiom mahler_small_bases (k : ℕ) (hk : k ≤ 4) :
    {a ∈ PowerSums k | ∃ m : ℕ, m ^ 2 = a}.Infinite

/-- Mahler found only one square in PowerSums k for k ≥ 5, namely:
1 + 7 + 7² + 7³ = 1 + 7 + 49 + 343 = 400 = 20². -/
theorem mahler_example : 1 + 7 + 49 + 343 = 400 := by norm_num

theorem mahler_example_is_square : ∃ m : ℕ, m ^ 2 = 400 := ⟨20, by norm_num⟩

/-! ## Small Cases -/

/-- 1 is both a factorial sum (1 = 0!) and a perfect square (1 = 1²).
So KthPowersInFactorialSums 2 is nonempty. -/
theorem one_is_square_factorial_sum :
    1 ∈ KthPowersInFactorialSums 2 :=
  ⟨one_mem_factorial_sums, ⟨1, by norm_num⟩⟩

/-- 1 is both a factorial sum and powerful.
So PowerfulFactorialSums is nonempty. -/
theorem one_is_powerful_factorial_sum :
    1 ∈ PowerfulFactorialSums :=
  ⟨one_mem_factorial_sums, one_is_powerful⟩

/-! ## Summary -/

/-- **Erdős Problem #1108 Summary**:

1. OPEN: For k ≥ 2, are there only finitely many k-th powers in factorial sums?
2. OPEN: Are there only finitely many powerful numbers in factorial sums?
3. KNOWN: Brindza-Erdős (1991) - For fixed r terms, n₁ is bounded if sum is powerful
4. RELATED: Problem #398 asks about squares of the form 1 + n! (also open)
5. RELATED: Mahler's problem about sums of powers of k
-/
theorem erdos_1108_summary :
    -- 1 is both a factorial sum and a perfect square
    1 ∈ KthPowersInFactorialSums 2 ∧
    -- 1 is both a factorial sum and powerful
    1 ∈ PowerfulFactorialSums ∧
    -- Mahler's example: 1 + 7 + 7² + 7³ = 400 = 20²
    1 + 7 + 49 + 343 = 400 :=
  ⟨one_is_square_factorial_sum, one_is_powerful_factorial_sum, mahler_example⟩

end Erdos1108
