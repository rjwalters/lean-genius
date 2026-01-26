/-!
# Erdős Problem #1135: The Collatz Conjecture

Define f : ℕ → ℕ by f(n) = n/2 if n is even, f(n) = (3n+1)/2 if n is odd.

Conjecture (Collatz): For every m ≥ 1, there exists k ≥ 1 with f^k(m) = 1.

Known:
- Verified computationally for all m up to 2^68 (Barina, 2020)
- Tao (2019): Almost all orbits attain values below any function tending to ∞
- Krasikov–Lagarias (2003): The set of n ≤ x reaching 1 has density ≥ x^{0.84}
- Erdős called such problems "hopeless" and offered $500

Status: OPEN. Prize: $500 (informal estimate by Erdős).

Reference: https://erdosproblems.com/1135
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic

/-! ## Definitions -/

/-- The Collatz function: f(n) = n/2 if even, (3n+1)/2 if odd. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- Iterated application of the Collatz function. -/
def collatzIter : ℕ → ℕ → ℕ
  | 0, m => m
  | k + 1, m => collatz (collatzIter k m)

/-- The Collatz orbit of m reaches 1. -/
def ReachesOne (m : ℕ) : Prop :=
  ∃ k : ℕ, collatzIter k m = 1

/-! ## Basic Properties -/

/-- collatz 1 = 2, and collatz 2 = 1, forming the cycle 1 → 2 → 1. -/
theorem collatz_one : collatz 1 = 2 := by decide

theorem collatz_two : collatz 2 = 1 := by decide

/-- 1 reaches 1 trivially. -/
theorem one_reaches_one : ReachesOne 1 := ⟨0, rfl⟩

/-! ## Partial Results -/

/-- Tao (2019): For almost all m, the orbit goes below any function tending to ∞.
    Formally: for every f : ℕ → ℝ with f(n) → ∞, the density of
    {m : m ≤ x, min orbit(m) ≤ f(m)} approaches 1. -/
axiom tao_almost_all :
  ∀ (g : ℕ → ℝ), (∀ M : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → M ≤ g n) →
    ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (Finset.card ((Finset.range x).filter
        (fun m => ∃ k : ℕ, (collatzIter k (m + 1) : ℝ) ≤ g (m + 1))) : ℝ)
      ≥ (1 - ε) * x

/-- Krasikov–Lagarias (2003): The number of m ≤ x that reach 1 is at least x^{0.84}. -/
axiom krasikov_lagarias (x : ℕ) (hx : 2 ≤ x) :
  (Finset.card ((Finset.range x).filter (fun m => ReachesOne (m + 1))) : ℝ)
  ≥ (x : ℝ) ^ (0.84 : ℝ)

/-! ## The Conjecture -/

/-- Erdős Problem #1135 (Collatz Conjecture): Every positive integer
    eventually reaches 1 under iteration of the Collatz function. -/
axiom erdos_1135_collatz_conjecture :
  ∀ m : ℕ, 1 ≤ m → ReachesOne m
