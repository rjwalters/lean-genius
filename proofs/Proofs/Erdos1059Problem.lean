/-
Erdős Problem #1059: Primes Minus Factorials All Composite

Are there infinitely many primes p such that p - k! is composite
for each k with 1 ≤ k! < p?

Key Results:
- Examples: p = 101 and p = 211 satisfy the condition
- Counterexample: p = 89 does not (89 - 6 = 83 which is prime)
- Related OEIS: A064152

References:
- Guy [Gu04], Problem A2
- https://erdosproblems.com/1059

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-
## Core Definitions
-/

/-- The condition that for every k with k! < n, the number n - k! is not prime
    and is at least 2 (i.e., composite in the usual sense). -/
def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ k : ℕ, Nat.factorial k < n → ¬(n - Nat.factorial k).Prime ∧ n - Nat.factorial k ≥ 2

/-
## Concrete Examples

The factorials are: 0! = 1, 1! = 1, 2! = 2, 3! = 6, 4! = 24, 5! = 120, 6! = 720.

For p = 101, factorials < 101 are {0!=1, 1!=1, 2!=2, 3!=6, 4!=24}:
  101 - 1 = 100 = 4 × 25 (composite)
  101 - 2 = 99 = 9 × 11 (composite)
  101 - 6 = 95 = 5 × 19 (composite)
  101 - 24 = 77 = 7 × 11 (composite)

For p = 211, factorials < 211 are {0!=1, 1!=1, 2!=2, 3!=6, 4!=24, 5!=120}:
  211 - 1 = 210 = 2 × 105 (composite)
  211 - 2 = 209 = 11 × 19 (composite)
  211 - 6 = 205 = 5 × 41 (composite)
  211 - 24 = 187 = 11 × 17 (composite)
  211 - 120 = 91 = 7 × 13 (composite)

For p = 89, factorials < 89 are {0!=1, 1!=1, 2!=2, 3!=6, 4!=24}:
  89 - 6 = 83 (prime!) so 89 fails.
-/

-- Helper: factorial grows fast, so k! < n implies k is small
private theorem factorial_lt_bound (k : ℕ) (h : Nat.factorial k < 101) : k ≤ 4 := by
  by_contra hk
  push_neg at hk
  have h5 : Nat.factorial 5 ≤ Nat.factorial k := Nat.factorial_le (by omega)
  simp [Nat.factorial] at h5
  omega

private theorem factorial_lt_bound_211 (k : ℕ) (h : Nat.factorial k < 211) : k ≤ 5 := by
  by_contra hk
  push_neg at hk
  have h6 : Nat.factorial 6 ≤ Nat.factorial k := Nat.factorial_le (by omega)
  simp [Nat.factorial] at h6
  omega

/-- p = 101 satisfies the property: 101 - k! is composite for all k! < 101. -/
theorem example_101 : AllFactorialSubtractionsComposite 101 := by
  intro k hk
  have hle := factorial_lt_bound k hk
  interval_cases k <;> simp [Nat.factorial] <;> decide

/-- p = 211 satisfies the property: 211 - k! is composite for all k! < 211. -/
theorem example_211 : AllFactorialSubtractionsComposite 211 := by
  intro k hk
  have hle := factorial_lt_bound_211 k hk
  interval_cases k <;> simp [Nat.factorial] <;> native_decide

/-- p = 89 does NOT satisfy the property: 89 - 3! = 89 - 6 = 83 is prime. -/
theorem counterexample_89 : ¬AllFactorialSubtractionsComposite 89 := by
  intro h
  have h3 := h 3 (by simp [Nat.factorial])
  simp [Nat.factorial] at h3
  exact h3 (by decide)

/-
## Main Conjecture
-/

/-- **Erdős Problem #1059** (OPEN): There are infinitely many primes p
    such that p - k! is composite for every k with 1 ≤ k! < p.
    Stated as a definition since this is an open conjecture. -/
def ErdosProblem1059 : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ AllFactorialSubtractionsComposite p}

/-
## Structural Observations
-/

/-- Factorials grow super-exponentially: for n ≥ 2 there exists l
    such that l! < n ≤ (l+1)!, and only l+1 factorials are less than n. -/
theorem factorial_count_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ l : ℕ, Nat.factorial l < n ∧ n ≤ Nat.factorial (l + 1) := by
  -- Find the smallest m with m! ≥ n
  have h_exists : ∃ m : ℕ, n ≤ Nat.factorial m := ⟨n, Nat.self_le_factorial n⟩
  have hm_val := Nat.find_spec h_exists
  have hm_pos : Nat.find h_exists ≥ 1 := by
    by_contra h
    push_neg at h
    have : Nat.find h_exists = 0 := by omega
    rw [this] at hm_val
    simp [Nat.factorial] at hm_val
    omega
  refine ⟨Nat.find h_exists - 1, ?_, ?_⟩
  · -- (find - 1)! < n by minimality
    have := Nat.find_min h_exists (by omega : Nat.find h_exists - 1 < Nat.find h_exists)
    omega
  · -- n ≤ find! = (find-1+1)!
    rwa [Nat.sub_add_cancel hm_pos]

/-
## Erdős's Alternative Approach
-/

/-- Erdős suggested it may be easier to prove: there exist infinitely many n
    with l! < n ≤ (l+1)! such that all prime factors of n exceed l,
    and n - k! is composite for all 1 ≤ k ≤ l. -/

/-
## Verified Examples Summary

We have proved:
- 101 is an example: all factorial subtractions are composite (theorem)
- 211 is an example: all factorial subtractions are composite (theorem)
- 89 is NOT an example: 89 - 6 = 83 is prime (theorem)

Both 101 and 211 are prime (verifiable by decide), confirming they
are witnesses for the conjecture.
-/

/-- 101 is prime -/
theorem prime_101 : Nat.Prime 101 := by decide

/-- 211 is prime -/
theorem prime_211 : Nat.Prime 211 := by native_decide

/-- 101 and 211 are both witnesses for the conjecture -/
theorem two_witnesses :
    (101 : ℕ).Prime ∧ AllFactorialSubtractionsComposite 101 ∧
    (211 : ℕ).Prime ∧ AllFactorialSubtractionsComposite 211 :=
  ⟨prime_101, example_101, prime_211, example_211⟩
