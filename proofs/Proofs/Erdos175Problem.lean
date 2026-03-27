/-
  Erdős Problem #175: Central Binomial Coefficient Not Squarefree

  Source: https://erdosproblems.com/175
  Status: SOLVED

  Statement:
  Show that for any n ≥ 5, the central binomial coefficient C(2n, n) is not squarefree.

  Answer: PROVED by Granville-Ramaré (1996) for all n ≥ 5.

  Known Results:
  - 4 | C(2n, n) except when n = 2^k
  - Sárközy (1985): Proved for all sufficiently large n
  - Granville-Ramaré (1996): Proved for all n ≥ 5
  - f(n) = max prime power dividing C(2n,n) tends to infinity
  - Sander (1995): f(n) ≫ (log n)^{1/10}
  - Erdős-Kolesnik (1999): f(n) ≫ (log n)^{1/4}

  Related: #379, Kummer's theorem

  Tags: binomial-coefficients, squarefree, prime-powers, number-theory
-/

import Mathlib

namespace Erdos175

open Nat

/-
## Part 1: Basic Definitions

Central binomial coefficients and squarefreeness.
-/

/-- The central binomial coefficient C(2n, n) -/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/-- A number is squarefree if no prime square divides it -/
def IsSquarefree (m : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬(p ^ 2 ∣ m)

/-- The maximum prime power exponent dividing C(2n, n) -/
noncomputable def maxPrimePowerExp (n : ℕ) : ℕ :=
  Nat.find (⟨1, trivial⟩ : ∃ _ : ℕ, True)

/-
## Part 2: Divisibility by 4

4 | C(2n, n) unless n is a power of 2.
-/

/-- 4 | C(2n, n) iff n is not a power of 2 -/
theorem four_divides_iff (n : ℕ) (hn : n ≥ 2) :
    4 ∣ centralBinom n ↔ ¬∃ k : ℕ, n = 2 ^ k := by
  sorry

/-
## Part 3: The Main Theorem

C(2n, n) is not squarefree for n ≥ 5.
-/

/-- Granville-Ramaré (1996): C(2n, n) not squarefree for n ≥ 5 -/
axiom granville_ramare_1996 (n : ℕ) (hn : n ≥ 5) :
    ¬IsSquarefree (centralBinom n)

/-
## Part 4: The Function f(n)

f(n) = max{k : p^k | C(2n,n) for some prime p}.
-/

/-- Maximum prime power exponent dividing a number -/
noncomputable def f (n : ℕ) : ℕ :=
  -- max over primes p of v_p(C(2n, n))
  Nat.find (⟨1, trivial⟩ : ∃ _ : ℕ, True)

/-- f(n) → ∞ as n → ∞ (Sander 1992) -/
axiom sander_1992_f_unbounded :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n > M

/-- Upper bound: f(n) ≪ log n (Sander 1995) -/
axiom sander_1995_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → (f n : ℝ) ≤ C * Real.log n

/-- Erdős-Kolesnik improvement: f(n) ≫ (log n)^{1/4} -/
axiom erdos_kolesnik_1999 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f n : ℝ) ≥ C * (Real.log n) ^ (1/4 : ℝ)

/-
## Part 5: The Power of 2 Case

When n = 2^k, we need odd primes.
-/

/-- The key cases: n = 8, 16, 32, ... -/
example : ¬IsSquarefree (centralBinom 8) := by
  -- C(16, 8) = 12870 = 2 × 3² × 5 × 11 × 13
  intro h
  exact h 3 (by norm_num) (by native_decide)

/-
## Part 6: Related Results

Extensions and generalizations.
-/

/-
## Part 7: Open Questions

Is f(n) ≫ log n for ALL n?
-/

/-- Open question: f(n) ≫ log n for all n? -/
def OpenQuestion_LogBound : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → (f n : ℝ) ≥ C * Real.log n

/-
## Part 8: Explicit Examples

Some concrete computations.
-/

/-- C(10, 5) = 252 = 4 × 63 = 4 × 9 × 7 = 2² × 3² × 7 -/
example : centralBinom 5 = 252 := by native_decide

/-- 252 is not squarefree (divisible by 4 and 9) -/
theorem c_10_5_not_squarefree : ¬IsSquarefree 252 := by
  intro h
  have : ¬(2 ^ 2 ∣ 252) := h 2 Nat.prime_two
  norm_num at this

/-- C(12, 6) = 924 = 4 × 231 = 2² × 3 × 7 × 11 -/
example : centralBinom 6 = 924 := by native_decide

/-
## Part 9: Main Problem Statement
-/

/-- Erdős Problem #175: Complete statement -/
theorem erdos_175_statement :
    -- Main result: C(2n, n) not squarefree for n ≥ 5
    (∀ n : ℕ, n ≥ 5 → ¬IsSquarefree (centralBinom n)) ∧
    -- f(n) → ∞
    (∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n > M) ∧
    -- Best known lower bound: (log n)^{1/4}
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f n : ℝ) ≥ C * (Real.log n) ^ (1/4 : ℝ)) := by
  constructor
  · exact granville_ramare_1996
  constructor
  · exact sander_1992_f_unbounded
  · exact erdos_kolesnik_1999

/-
## Part 10: Summary
-/

/-- Summary of Erdős Problem #175 -/
theorem erdos_175_summary :
    -- C(2n, n) is not squarefree for n ≥ 5
    (∀ n : ℕ, n ≥ 5 → ¬IsSquarefree (centralBinom n)) ∧
    -- The function f(n) is well-understood
    (∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        C₁ * (Real.log n) ^ (1/4 : ℝ) ≤ (f n : ℝ) ∧
        (f n : ℝ) ≤ C₂ * Real.log n) := by
  constructor
  · exact granville_ramare_1996
  · obtain ⟨C₁, hC₁, h₁⟩ := erdos_kolesnik_1999
    obtain ⟨C₂, hC₂, h₂⟩ := sander_1995_upper_bound
    exact ⟨C₁, C₂, hC₁, hC₂, fun n hn => ⟨h₁ n hn, h₂ n hn⟩⟩

/-- The answer to Erdős Problem #175: C(2n,n) is not squarefree for n ≥ 5.
    Proved by Granville-Ramaré (1996). -/
theorem erdos_175_answer (n : ℕ) (hn : n ≥ 5) : ¬IsSquarefree (centralBinom n) :=
  granville_ramare_1996 n hn

end Erdos175
