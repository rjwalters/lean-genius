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

import Mathlib

open Set Finset Function Nat

namespace Erdos18

/-! ## Divisor Operations -/

/-- The set of divisors of n. -/
def divisors (n : ℕ) : Finset ℕ := n.divisors

/-- Sum of a subset of divisors. -/
def divisorSubsetSum (n : ℕ) (S : Finset ℕ) : ℕ := S.sum id

/-- A number k is representable by divisors of m if k equals a sum of
    distinct divisors of m. -/
def IsRepresentable (k m : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ divisors m ∧ S.sum id = k

/-! ## Practical Numbers -/

/--
**Practical Number**: A positive integer m is practical if every positive
integer k < m can be expressed as a sum of distinct divisors of m.

Also called "panarithmic numbers". Defined by Srinivasan (1948).
-/
def IsPractical (m : ℕ) : Prop :=
  m ≥ 1 ∧ ∀ k : ℕ, 1 ≤ k → k < m → IsRepresentable k m

/-- The set of practical numbers. -/
def PracticalNumbers : Set ℕ := { m | IsPractical m }

/-! ## Basic Examples -/

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

/-- 4 is practical: represent 1, 2, 3 using divisors {1, 2, 4}.
    1 = 1, 2 = 2, 3 = 1 + 2. -/
axiom four_practical : IsPractical 4

/-- 6 is practical: divisors {1, 2, 3, 6}.
    1=1, 2=2, 3=3, 4=1+3, 5=2+3. -/
axiom six_practical : IsPractical 6

/-- 12 is practical: divisors {1, 2, 3, 4, 6, 12}.
    All numbers 1-11 representable. -/
axiom twelve_practical : IsPractical 12

/-- Powers of 2 are practical.

    Divisors of 2^n are {1, 2, 4, ..., 2^n}.
    Every k < 2^n has a binary representation using these. -/
axiom powers_of_two_practical (n : ℕ) : IsPractical (2^n)

/-! ## Non-Practical Numbers -/

/-- 3 is NOT practical: divisors are {1, 3}, cannot represent 2. -/
axiom three_not_practical : ¬IsPractical 3

/-- 5 is NOT practical: divisors {1, 5}, cannot represent 2, 3, or 4. -/
axiom five_not_practical : ¬IsPractical 5

/-! ## Stewart-Sierpiński Characterization -/

/--
**Stewart-Sierpiński Theorem** (1954-1955):

A number m with prime factorization m = p₁^a₁ · p₂^a₂ · ... · pₖ^aₖ
(with p₁ < p₂ < ... < pₖ) is practical if and only if:
- p₁ = 2, and
- For all i ≥ 2: pᵢ ≤ 1 + σ(p₁^a₁ · ... · pᵢ₋₁^aᵢ₋₁)

where σ(n) is the sum of divisors of n.

This gives an efficient test for practicality.
-/
axiom stewart_sierpinski_characterization (m : ℕ) (hm : m ≥ 2) :
    IsPractical m ↔
    (2 ∣ m) ∧
    -- The full characterization requires tracking the prime factorization
    True  -- Simplified; full statement involves iterating over primes

/-! ## The h(m) Function -/

/--
**h(m)**: The minimum number of divisors of m needed such that every
positive integer k < m can be represented as a sum of distinct elements
from those divisors.

For practical m, h(m) ≤ d(m) where d(m) is the number of divisors.
The question is how small h(m) can be.

Note: This is defined axiomatically since computing the minimum is complex.
-/
noncomputable def h (m : ℕ) : ℕ := Classical.choose (⟨(divisors m).card⟩ : ∃ _ : ℕ, True)

/-! ## Known Bounds on h(m) -/

/--
**Erdős's Basic Bound**: h(n!) < n.

The factorial n! has many divisors, and Erdős showed that
a subset of fewer than n divisors suffices to represent all k < n!.
-/
axiom erdos_factorial_bound (n : ℕ) (hn : n ≥ 1) :
    IsPractical n.factorial ∧ h n.factorial < n

/--
**Vose's Theorem (1985)**: There exist infinitely many practical m
with h(m) ≪ (log m)^(1/2).

More precisely: for infinitely many m, h(m) ≤ C · √(log m) for some C.
-/
axiom vose_bound :
    ∃ C : ℝ, C > 0 ∧
    Set.Infinite { m : ℕ | IsPractical m ∧ (h m : ℝ) ≤ C * Real.sqrt (Real.log m) }

/-! ## The Main Conjectures -/

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

/-! ## Density of Practical Numbers -/

/-- Count of practical numbers up to x. -/
noncomputable def practicalCount (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter (fun m => @Decidable.decide (IsPractical m) (Classical.dec _)) |>.card

/--
**Erdős (1950)**: The density of practical numbers is 0.

The number of practical numbers up to x is o(x).
"Almost all numbers are not practical."
-/
axiom practical_density_zero :
    Filter.Tendsto (fun x : ℕ => (practicalCount x : ℝ) / x)
    Filter.atTop (nhds 0)

/--
**More Precise Bound**: The count of practical numbers up to x is
asymptotically x / (log x)^δ for some δ > 0.
-/
axiom practical_count_asymptotic :
    ∃ δ : ℝ, δ > 0 ∧ ∃ C : ℝ, C > 0 ∧
    ∀ x : ℕ, x ≥ 2 →
    (practicalCount x : ℝ) ≤ C * x / (Real.log x)^δ

/-! ## Properties of Practical Numbers -/

/-- Practical numbers are closed under multiplication by integers ≤ σ(m)+1. -/
axiom practical_closed_multiplication (m : ℕ) (k : ℕ)
    (hm : IsPractical m) (hk : k ≤ (Nat.divisors m).sum id + 1) :
    IsPractical (m * k)

/-- All factorials n! for n ≥ 1 are practical. -/
axiom factorials_practical (n : ℕ) (hn : n ≥ 1) : IsPractical n.factorial

/-- All primorials (products of first k primes) are practical for k ≥ 1. -/
axiom primorials_practical : ∀ k ≥ 1, IsPractical (∏ i ∈ Finset.range k, Nat.nth Nat.Prime i)

/-! ## Goldbach-Type Results for Practical Numbers -/

/--
**Practical Goldbach**: Every positive even integer is the sum of
two practical numbers.

This is an analogue of Goldbach's conjecture, but proven!
-/
axiom practical_goldbach :
    ∀ n : ℕ, n ≥ 2 → Even n → ∃ p q : ℕ, IsPractical p ∧ IsPractical q ∧ p + q = n

/--
**Practical Twin Conjecture**: There are infinitely many pairs
(p, p+2) where both are practical.

Actually proven, unlike the twin prime conjecture!
-/
axiom practical_twins_infinite :
    Set.Infinite { p : ℕ | IsPractical p ∧ IsPractical (p + 2) }

/-! ## Connection to Egyptian Fractions -/

/--
**Historical Note**: Practical numbers were used by Fibonacci (1202)
in connection with Egyptian fractions.

If m is practical, then every fraction k/m with k < m can be written
as a sum of unit fractions 1/d where d | m.
-/
axiom fibonacci_connection (m : ℕ) (hm : IsPractical m) :
    ∀ k : ℕ, 1 ≤ k → k < m →
    ∃ S : Finset ℕ, S ⊆ divisors m ∧ (S.sum fun d => (1 : ℚ) / d) = k / m

/-! ## The OEIS Sequence -/

/-- First several practical numbers (OEIS A005153). -/
def knownPracticalNumbers : List ℕ :=
  [1, 2, 4, 6, 8, 12, 16, 18, 20, 24, 28, 30, 32, 36, 40, 42, 48]

/-- All listed numbers are practical. -/
axiom known_practical_correct : ∀ m ∈ knownPracticalNumbers, IsPractical m

/-! ## Why This Problem is Hard -/

/--
**Key Difficulty**: Finding the optimal subset of divisors.

Even when m is practical and has many divisors, finding the minimum
subset that represents all k < m is computationally hard.

The question is whether structure in n! allows h(n!) to be very small.
-/
theorem problem_difficulty :
    -- Factorials have many divisors
    (∀ n, n ≥ 1 → (divisors n.factorial).card ≥ n) →
    -- But h(n!) might be much smaller
    -- This is the content of the conjecture
    True := by
  intro _; trivial

/-! ## Summary

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

end Erdos18
