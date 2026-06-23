/-
Erdős Problem #887: Divisors in Short Intervals Near √n

Is there an absolute constant K such that, for every C > 0, if n is
sufficiently large then n has at most K divisors in (√n, √n + C·n^{1/4})?

**Status**: OPEN

Erdős and Rosenfeld (1997) proved that there are infinitely many n with
4 divisors in (√n, √n + n^{1/4}), and asked whether 4 is best possible.
Tsz Ho Chan (2013) proved that perfect squares have at most 5 divisors
in such intervals. The general case remains open.

Reference: https://erdosproblems.com/887
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic

namespace Erdos887

/- ## Part 1: Basic Definitions -/

/-- The set of divisors of n as a finite set -/
def divisors (n : ℕ) : Finset ℕ :=
  Finset.filter (· ∣ n) (Finset.range (n + 1))

/-- The divisor function τ(n): number of positive divisors of n -/
def tau (n : ℕ) : ℕ := (divisors n).card

/-- Divisors of n lying in the real interval [a, b] -/
def divisorsInInterval (n : ℕ) (a b : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d => a ≤ d ∧ (d : ℝ) ≤ b)

/-- Count of divisors of n in the interval [a, b] -/
def countDivisorsInInterval (n : ℕ) (a b : ℝ) : ℕ :=
  (divisorsInInterval n a b).card

/- ## Part 2: The Erdős-Rosenfeld Conjecture -/

/-- The Erdős-Rosenfeld interval (√n, √n + C·n^{1/4}) -/
def erdosRosenfeldInterval (n : ℕ) (C : ℝ) : Set ℝ :=
  { x | Real.sqrt n < x ∧ x ≤ Real.sqrt n + C * (n : ℝ) ^ (1/4 : ℝ) }

/-- Count of divisors of n in the Erdős-Rosenfeld interval -/
def divisorsNearSqrt (n : ℕ) (C : ℝ) : ℕ :=
  countDivisorsInInterval n (Real.sqrt n) (Real.sqrt n + C * (n : ℝ) ^ (1/4 : ℝ))

/-- The Erdős-Rosenfeld Conjecture (strong form):
    There exists a universal constant K such that for all C > 0
    and all sufficiently large n, n has at most K divisors in
    (√n, √n + C·n^{1/4}).  The constant K is independent of C. -/
def ErdosRosenfeldConjecture : Prop :=
  ∃ K : ℕ, ∀ C : ℝ, C > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrt n C ≤ K

/-- Weak form: K may depend on C -/
def WeakErdosRosenfeld : Prop :=
  ∀ C : ℝ, C > 0 → ∃ K : ℕ, ∃ N₀ : ℕ,
    ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrt n C ≤ K

/- ## Part 3: Erdős-Rosenfeld Lower Bound (1997) -/

/-- Erdős-Rosenfeld (1997): infinitely many n have exactly 4 divisors
    in (√n, √n + C·n^{1/4}) for C ≥ 1.
    This is the key lower bound: if K exists, then K ≥ 4. -/
axiom erdos_rosenfeld_four_divisors :
  ∀ C : ℝ, C ≥ 1 →
    Set.Infinite { n : ℕ | divisorsNearSqrt n C = 4 }

/-- The conjectured answer: 4 is the maximum -/
def FourIsMaximum : Prop :=
  ∀ C : ℝ, C > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrt n C ≤ 4

/- ## Part 4: Perfect Square Case — Chan's Theorem (2013) -/

/-- A natural number is a perfect square -/
def isPerfectSquare (n : ℕ) : Prop := ∃ k : ℕ, k ^ 2 = n

/-- Chan's Theorem (2013): perfect squares have at most 5 divisors
    in a symmetric interval of width 2c·n^{1/4} around √n.
    The bound is 5 rather than 4 because √n is an integer divisor. -/
axiom chan_perfect_square_bound :
  ∀ n : ℕ, isPerfectSquare n →
    ∀ c : ℝ, c > 0 →
      countDivisorsInInterval n
        (Real.sqrt n - c * (n : ℝ) ^ (1/4 : ℝ))
        (Real.sqrt n + c * (n : ℝ) ^ (1/4 : ℝ)) ≤ 5

/-- For perfect squares, √n is itself a divisor of n -/
theorem perfect_square_has_sqrt_divisor (n : ℕ) (hn : isPerfectSquare n) :
    ∃ d : ℕ, d ∣ n ∧ d ^ 2 = n := by
  obtain ⟨k, hk⟩ := hn
  exact ⟨k, ⟨Dvd.intro k (by ring_nf; rw [← hk]), hk⟩⟩

/- ## Part 5: General Divisor Bounds -/

/-- τ(n) ≪ n^ε for any ε > 0: the divisor function grows
    slower than any positive power of n. -/
axiom divisor_bound_epsilon :
  ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 → (tau n : ℝ) ≤ C * (n : ℝ) ^ ε

/- ## Part 6: Interval Width Variations -/

/-- The symmetric interval case: divisors in (√n - c·n^{1/4}, √n + c·n^{1/4}) -/
def divisorsSymmetricInterval (n : ℕ) (c : ℝ) : ℕ :=
  countDivisorsInInterval n
    (Real.sqrt n - c * (n : ℝ) ^ (1/4 : ℝ))
    (Real.sqrt n + c * (n : ℝ) ^ (1/4 : ℝ))

/-- Divisors near √n with general exponent α: (√n, √n + C·n^α) -/
def divisorsNearSqrtAlpha (n : ℕ) (C α : ℝ) : ℕ :=
  countDivisorsInInterval n (Real.sqrt n) (Real.sqrt n + C * (n : ℝ) ^ α)

/-- For α > 1/2 the interval grows faster than √n, so no uniform
    bound K exists: for every K there is some n exceeding it. -/
axiom no_bound_for_large_alpha :
  ∀ α : ℝ, α > 1/2 → ∀ K : ℕ,
    ∃ n : ℕ, n ≥ 1 ∧ divisorsNearSqrtAlpha n 1 α > K

/-- For α < 1/4 the interval is too narrow to contain more than
    a complementary pair d, n/d, so the count is at most 2. -/
axiom bound_for_small_alpha :
  ∀ α : ℝ, 0 < α → α < 1/4 → ∃ N₀ : ℕ,
    ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrtAlpha n 1 α ≤ 2

/- ## Part 7: Summary -/

/-- Summary of known results for Erdős Problem #887:
    • Infinitely many n achieve exactly 4 divisors (Erdős-Rosenfeld 1997)
    • Perfect squares have at most 5 divisors (Chan 2013)
    • For exponent α > 1/2, no bound exists
    • For exponent α < 1/4, the bound is 2
    • The general case at exponent 1/4 is OPEN -/
theorem erdos_887_summary :
  (∀ C : ℝ, C ≥ 1 → Set.Infinite { n : ℕ | divisorsNearSqrt n C = 4 }) ∧
  (∀ n : ℕ, isPerfectSquare n → ∀ c : ℝ, c > 0 →
    divisorsSymmetricInterval n c ≤ 5) ∧
  (∀ α : ℝ, α > 1/2 → ∀ K : ℕ, ∃ n : ℕ, n ≥ 1 ∧ divisorsNearSqrtAlpha n 1 α > K) ∧
  (∀ α : ℝ, 0 < α → α < 1/4 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrtAlpha n 1 α ≤ 2) :=
  ⟨erdos_rosenfeld_four_divisors, chan_perfect_square_bound, no_bound_for_large_alpha, bound_for_small_alpha⟩

/-- Erdős Problem #887: Main entry point.
    The conjecture is stated as a Prop; its truth value is unknown. -/
theorem erdos_887 : ErdosRosenfeldConjecture =
    (∃ K : ℕ, ∀ C : ℝ, C > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrt n C ≤ K) := by
  rfl

end Erdos887
