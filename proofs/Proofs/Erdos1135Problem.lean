/-
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

/- ## Definitions -/

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

/- ## Basic Properties -/

/-- collatz 1 = 2, and collatz 2 = 1, forming the cycle 1 → 2 → 1. -/
theorem collatz_one : collatz 1 = 2 := by decide

theorem collatz_two : collatz 2 = 1 := by decide

/-- 1 reaches 1 trivially. -/
theorem one_reaches_one : ReachesOne 1 := ⟨0, rfl⟩

/- ## Structural Properties -/

/-- Composition: k iterations starting from collatz m equals k+1 iterations from m. -/
theorem collatzIter_collatz (k m : ℕ) :
    collatzIter k (collatz m) = collatzIter (k + 1) m := by
  induction k with
  | zero => simp [collatzIter]
  | succ n ih => simp [collatzIter, ih]

/-- The Collatz function preserves positivity. -/
theorem collatz_pos {m : ℕ} (hm : 0 < m) : 0 < collatz m := by
  unfold collatz; split_ifs with h
  · exact Nat.div_pos (by omega) (by omega)
  · exact Nat.div_pos (by omega) (by omega)

/-- Even case: collatz m = m / 2. -/
theorem collatz_even_eq (m : ℕ) (h : m % 2 = 0) : collatz m = m / 2 := by
  simp [collatz, h]

/-- Odd case: collatz m = (3m + 1) / 2. -/
theorem collatz_odd_eq (m : ℕ) (h : m % 2 ≠ 0) : collatz m = (3 * m + 1) / 2 := by
  simp [collatz, h, if_neg]

/-- An even step always reduces: collatz m < m for even m > 0. -/
theorem collatz_even_lt (m : ℕ) (hm : 0 < m) (h : m % 2 = 0) : collatz m < m := by
  rw [collatz_even_eq m h]; exact Nat.div_lt_self hm (by omega)

/-- If collatz m reaches 1, then m reaches 1. -/
theorem reachesOne_of_collatz {m : ℕ} (h : ReachesOne (collatz m)) : ReachesOne m := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + 1, by rw [← collatzIter_collatz]; exact hk⟩

/- ## Concrete Verifications -/

theorem two_reaches_one : ReachesOne 2 := ⟨1, by native_decide⟩
theorem three_reaches_one : ReachesOne 3 := ⟨5, by native_decide⟩
theorem four_reaches_one : ReachesOne 4 := ⟨2, by native_decide⟩
theorem five_reaches_one : ReachesOne 5 := ⟨4, by native_decide⟩
theorem six_reaches_one : ReachesOne 6 := ⟨6, by native_decide⟩
theorem seven_reaches_one : ReachesOne 7 := ⟨11, by native_decide⟩

/- ## Partial Results -/

/-- Tao (2019): For almost all m, the orbit goes below any function tending to ∞.
    Formally: for every f : ℕ → ℝ with f(n) → ∞, the density of
    {m : m ≤ x, min orbit(m) ≤ f(m)} approaches 1. -/
/-- Krasikov–Lagarias (2003): The number of m ≤ x that reach 1 is at least x^{0.84}. -/
/- ## The Conjecture -/

/-- Erdős Problem #1135 (Collatz Conjecture): Every positive integer
    eventually reaches 1 under iteration of the Collatz function. -/
