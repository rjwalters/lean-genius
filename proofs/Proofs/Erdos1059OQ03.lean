/-
Erdős Problem #1059, Open Question 03:
Find the smallest prime p > 211 failing the Erdős 1059 property.

Answer: p = 223.
223 - 4! = 223 - 24 = 199, which is prime. Therefore 223 does not
satisfy AllFactorialSubtractionsComposite.

Since 223 is the next prime after 211, it is the smallest such prime.

Axiom count: 0
Sorry count: 0
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open Nat in
/-- The condition that for every k with k! < n, n - k! is composite. -/
def AllFactorialSubtractionsComposite (n : ℕ) : Prop :=
  ∀ k : ℕ, Nat.factorial k < n → ¬(n - Nat.factorial k).Prime ∧ n - Nat.factorial k ≥ 2

/-- 223 is prime. -/
theorem prime_223 : Nat.Prime 223 := by decide

/-- The next prime after 211 is 223 (no primes in 212..222). -/
theorem next_prime_after_211 : ∀ n, 211 < n → n < 223 → ¬n.Prime := by decide

/-- 199 is prime (key fact: 223 - 4! = 199). -/
theorem prime_199 : Nat.Prime 199 := by decide

/-- 223 fails the Erdős 1059 property: 223 - 4! = 223 - 24 = 199 is prime. -/
theorem counterexample_223 : ¬AllFactorialSubtractionsComposite 223 := by
  intro h
  have h4 := h 4 (by simp [Nat.factorial]; omega)
  simp [Nat.factorial] at h4
  exact h4 (by decide)

/-- 223 is the smallest prime greater than 211 that fails the property. -/
theorem smallest_failing_prime_after_211 :
    (223 : ℕ).Prime ∧
    ¬AllFactorialSubtractionsComposite 223 ∧
    (∀ p, 211 < p → p < 223 → ¬p.Prime) :=
  ⟨prime_223, counterexample_223, next_prime_after_211⟩
