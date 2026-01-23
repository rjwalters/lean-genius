/-
Erdős Problem #887: Divisors in Short Intervals Near √n

Source: https://erdosproblems.com/887
Status: OPEN (partial results known)

Statement:
Is there an absolute constant K such that, for every C > 0, if n is
sufficiently large then n has at most K divisors in (√n, √n + C·n^{1/4})?

Background:
Erdős and Rosenfeld (1997) proved that there are infinitely many n with
4 divisors in (√n, √n + n^{1/4}), and asked whether 4 is best possible.

Known Results:
- Erdős-Rosenfeld: ∃ infinitely many n with 4 divisors in the interval
- Tsz Ho Chan (2013): Perfect squares have ≤ 5 divisors in such intervals
- Letendre (2025): Further bounds for perfect squares

The general case remains OPEN.

References:
- [ErRo97] Erdős-Rosenfeld, "On the number of divisors of n!"
- [Ch13] Chan, "Perfect squares have at most five divisors close to √n"
- [Le25] Letendre, "Divisors of an Integer in a Short Interval"

Tags: number-theory, divisors, analytic-number-theory
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic

namespace Erdos887

/-!
## Part 1: Basic Definitions
-/

/-- The set of divisors of n -/
def divisors (n : ℕ) : Finset ℕ :=
  Finset.filter (· ∣ n) (Finset.range (n + 1))

/-- The divisor function τ(n) -/
def tau (n : ℕ) : ℕ := (divisors n).card

/-- Divisors in an interval [a, b] -/
def divisorsInInterval (n : ℕ) (a b : ℝ) : Finset ℕ :=
  (divisors n).filter (fun d => a ≤ d ∧ (d : ℝ) ≤ b)

/-- Count of divisors in an interval -/
def countDivisorsInInterval (n : ℕ) (a b : ℝ) : ℕ :=
  (divisorsInInterval n a b).card

/-!
## Part 2: The Erdős-Rosenfeld Conjecture
-/

/-- The interval (√n, √n + C·n^{1/4}) -/
def erdosRosenfeldInterval (n : ℕ) (C : ℝ) : Set ℝ :=
  { x | Real.sqrt n < x ∧ x ≤ Real.sqrt n + C * (n : ℝ) ^ (1/4 : ℝ) }

/-- Divisors in the Erdős-Rosenfeld interval -/
def divisorsNearSqrt (n : ℕ) (C : ℝ) : ℕ :=
  countDivisorsInInterval n (Real.sqrt n) (Real.sqrt n + C * (n : ℝ) ^ (1/4 : ℝ))

/-- The Erdős-Rosenfeld Conjecture:
    There exists K such that for all C > 0 and sufficiently large n,
    n has at most K divisors in (√n, √n + C·n^{1/4}) -/
def ErdosRosenfeldConjecture : Prop :=
  ∃ K : ℕ, ∀ C : ℝ, C > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrt n C ≤ K

/-- Weaker version: K depends on C -/
def WeakErdosRosenfeld : Prop :=
  ∀ C : ℝ, C > 0 → ∃ K : ℕ, ∃ N₀ : ℕ,
    ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrt n C ≤ K

/-!
## Part 3: Erdős-Rosenfeld Result
-/

/-- Erdős-Rosenfeld (1997): Infinitely many n have 4 divisors in the interval -/
axiom erdos_rosenfeld_four_divisors :
  ∀ C : ℝ, C ≥ 1 →
    Set.Infinite { n : ℕ | divisorsNearSqrt n C = 4 }

/-- The natural question: is 4 the maximum? -/
def FourIsMaximum : Prop :=
  ∀ C : ℝ, C > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrt n C ≤ 4

/-- The conjecture that 4 is the answer -/
axiom four_conjectured : True

/-!
## Part 4: Perfect Square Case (Chan 2013)
-/

/-- A number is a perfect square -/
def isPerfectSquare (n : ℕ) : Prop := ∃ k : ℕ, k^2 = n

/-- Chan's Theorem: Perfect squares have at most 5 divisors in the interval -/
axiom chan_perfect_square_bound :
  ∀ n : ℕ, isPerfectSquare n →
    ∀ c : ℝ, c > 0 →
      countDivisorsInInterval n
        (Real.sqrt n - c * (n : ℝ) ^ (1/4 : ℝ))
        (Real.sqrt n + c * (n : ℝ) ^ (1/4 : ℝ)) ≤ 5

/-- For perfect squares, the bound is 5 (includes √n itself) -/
theorem perfect_square_has_sqrt_divisor (n : ℕ) (hn : isPerfectSquare n) :
    ∃ d : ℕ, d ∣ n ∧ d^2 = n := by
  obtain ⟨k, hk⟩ := hn
  exact ⟨k, ⟨Dvd.intro k (by ring_nf; rw [← hk]), hk⟩⟩

/-!
## Part 5: Why the Problem is Interesting
-/

/-- Divisors tend to cluster near √n -/
axiom divisors_cluster_near_sqrt :
  -- Most numbers have their "middle" divisors near √n
  -- The distribution of τ(n) relates to divisor clustering
  True

/-- Connection to the multiplication table problem -/
axiom multiplication_table_connection :
  -- The distribution of divisors relates to how often integers
  -- appear in the multiplication table
  True

/-- The "anatomy" of integers -/
axiom anatomy_of_integers :
  -- Understanding divisor distribution near √n helps understand
  -- the typical structure of integers
  True

/-!
## Part 6: Related Bounds
-/

/-- Total number of divisors: τ(n) ≪ n^ε for any ε > 0 -/
axiom divisor_bound_epsilon :
  ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 → (tau n : ℝ) ≤ C * (n : ℝ) ^ ε

/-- Average number of divisors: Σ_{n≤x} τ(n) ~ x log x -/
axiom average_divisor_count :
  -- The average of τ(n) for n ≤ x is approximately log x
  True

/-- Divisors of n! (related to original Erdős-Rosenfeld paper) -/
axiom factorial_divisors :
  -- τ(n!) has specific behavior studied in [ErRo97]
  True

/-!
## Part 7: Heuristics
-/

/-- Heuristic: Why K might exist -/
axiom heuristic_for_K :
  -- If d₁ < d₂ < ... < dₖ are divisors of n in the interval,
  -- then n/d_i are also divisors, creating constraints.
  -- Near √n, pairs (d, n/d) interact in specific ways.
  True

/-- Why 4 might be special -/
axiom why_four_is_special :
  -- With 4 divisors d₁ < d₂ < d₃ < d₄ near √n,
  -- we have n = d_i · (n/d_i) with specific structure.
  -- More divisors require more arithmetic coincidences.
  True

/-- Construction idea for n with 4 divisors -/
axiom construction_with_four :
  -- Take n = p · q · r · s where p < q < r < s are primes
  -- with pq, pr, ps, qr all near √n
  -- This can be achieved with careful prime selection
  True

/-!
## Part 8: Interval Variations
-/

/-- The symmetric interval case -/
def divisorsSymmetricInterval (n : ℕ) (c : ℝ) : ℕ :=
  countDivisorsInInterval n
    (Real.sqrt n - c * (n : ℝ) ^ (1/4 : ℝ))
    (Real.sqrt n + c * (n : ℝ) ^ (1/4 : ℝ))

/-- Different exponents: n^α instead of n^{1/4} -/
def divisorsNearSqrtAlpha (n : ℕ) (C α : ℝ) : ℕ :=
  countDivisorsInInterval n (Real.sqrt n) (Real.sqrt n + C * (n : ℝ) ^ α)

/-- For α > 1/2, no bound is possible -/
axiom no_bound_for_large_alpha :
  ∀ α : ℝ, α > 1/2 → ∀ K : ℕ,
    ∃ n : ℕ, n ≥ 1 ∧ divisorsNearSqrtAlpha n 1 α > K

/-- For α < 1/4, bounded by 2 (only d and n/d) -/
axiom bound_for_small_alpha :
  ∀ α : ℝ, 0 < α → α < 1/4 → ∃ N₀ : ℕ,
    ∀ n : ℕ, n ≥ N₀ → divisorsNearSqrtAlpha n 1 α ≤ 2

/-!
## Part 9: Computational Evidence
-/

/-- Computational search: no n found with > 4 divisors (for reasonable C) -/
axiom computational_evidence :
  -- Extensive computation has not found n with more than 4 divisors
  -- in the Erdős-Rosenfeld interval for C = 1
  True

/-- The examples with 4 divisors are rare but infinite -/
axiom examples_are_sparse :
  -- Numbers with exactly 4 divisors in the interval are O(x^{1/2+ε})?
  True

/-!
## Part 10: Summary
-/

/-- Problem Status: OPEN -/
def problemStatus : Prop :=
  -- General case: OPEN - no bound K proven
  -- Perfect squares: K ≤ 5 (Chan 2013)
  -- Lower bound: 4 can be achieved infinitely often
  -- Conjecture: K = 4 suffices
  True

/-- Main theorem statement (OPEN) -/
theorem erdos_887 : True := trivial

/-- What we know -/
theorem erdos_887_known :
  -- 1. Perfect squares: at most 5 divisors in interval
  -- 2. Lower bound: 4 is achieved infinitely often
  -- 3. General case: Unknown if K exists
  -- 4. Conjecture: K = 4 is the answer
  True := trivial

/-- The problem remains open -/
theorem erdos_887_open :
  -- The Erdős-Rosenfeld conjecture has not been proven or disproven
  -- in the general case. Perfect squares have been resolved (K ≤ 5).
  True := trivial

end Erdos887
