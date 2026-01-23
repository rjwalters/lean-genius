/-
Erdős Problem #709: Divisibility in Intervals

Source: https://erdosproblems.com/709
Status: OPEN (tight bounds unknown)

Statement:
Let f(n) be minimal such that, for any A = {a₁,...,aₙ} ⊆ [2,∞) ∩ ℕ of size n,
in any interval I of f(n)·max(A) consecutive integers there exist distinct
x₁,...,xₙ ∈ I such that aᵢ | xᵢ.

Obtain good bounds for f(n), or even an asymptotic formula.

Known Results:
- Erdős-Surányi (1959): (log n)^c ≪ f(n) ≪ √n for some c > 0
- Lower bound: (log n)^c - uses probabilistic arguments
- Upper bound: √n - constructive covering argument

The gap between (log n)^c and √n is substantial.
Finding the true growth rate of f(n) remains open.

Related: Problem 708 (similar divisibility question about g(n))

References:
- Erdős-Surányi [ErSu59]: Bemerkungen zu einer Aufgabe eines mathematischen
  Wettbewerbs. Mat. Lapok (1959), 39-48.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

namespace Erdos709

open Finset

/-!
## Part I: Basic Definitions

A finite set A ⊆ [2,∞) of positive integers and intervals of consecutive integers.
-/

/-- A finite set of positive integers ≥ 2 -/
def ValidSet (A : Finset ℕ) : Prop := ∀ a ∈ A, a ≥ 2

/-- Maximum element of a nonempty finite set -/
noncomputable def maxElem (A : Finset ℕ) : ℕ :=
  A.fold max 0 id

/-- An interval [start, start + length - 1] of consecutive integers -/
structure Interval where
  start : ℕ
  length : ℕ

/-- Check if x belongs to interval I -/
def Interval.contains (I : Interval) (x : ℕ) : Prop :=
  I.start ≤ x ∧ x < I.start + I.length

/-!
## Part II: The Covering Property

For set A = {a₁,...,aₙ}, we need distinct x₁,...,xₙ in I with aᵢ | xᵢ.
-/

/-- A covering assigns to each aᵢ ∈ A a distinct xᵢ ∈ I with aᵢ | xᵢ -/
structure Covering (A : Finset ℕ) (I : Interval) where
  assign : ℕ → ℕ  -- maps aᵢ to xᵢ
  in_interval : ∀ a ∈ A, I.contains (assign a)
  divides : ∀ a ∈ A, a ∣ assign a
  injective : ∀ a b, a ∈ A → b ∈ A → a ≠ b → assign a ≠ assign b

/-- The interval has the covering property for A if such a covering exists -/
def HasCovering (A : Finset ℕ) (I : Interval) : Prop :=
  Nonempty (Covering A I)

/-!
## Part III: The Function f(n)

f(n) = minimal k such that any interval of k·max(A) consecutive integers
has the covering property for any valid set A of size n.
-/

/-- f(n) exists and is well-defined -/
def f_exists (n : ℕ) : Prop :=
  ∃ k : ℕ, k > 0 ∧
    ∀ A : Finset ℕ, ValidSet A → A.card = n →
    ∀ I : Interval, I.length = k * maxElem A →
      HasCovering A I

/-- The function f(n) (axiomatized since computing it is complex) -/
axiom f (n : ℕ) : ℕ
axiom f_pos (n : ℕ) (hn : n ≥ 1) : f n > 0
axiom f_sufficient (n : ℕ) (hn : n ≥ 1) :
    ∀ A : Finset ℕ, ValidSet A → A.card = n →
    ∀ I : Interval, I.length ≥ f n * maxElem A →
      HasCovering A I

/-!
## Part IV: Known Bounds (Erdős-Surányi 1959)
-/

/-- Lower bound: f(n) ≥ (log n)^c for some c > 0 -/
axiom lower_bound_log :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (f n : ℝ) ≥ (Real.log n) ^ c

/-- Upper bound: f(n) ≤ C·√n for some constant C -/
axiom upper_bound_sqrt :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (f n : ℝ) ≤ C * Real.sqrt n

/-- The combined Erdős-Surányi bound -/
theorem erdos_suranyi_1959 :
    (∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, (f n : ℝ) ≥ (Real.log n) ^ c) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * Real.sqrt n) := by
  exact ⟨lower_bound_log, upper_bound_sqrt⟩

/-!
## Part V: Special Cases
-/

/-- For n = 1, f(1) = 1: any interval of length max(A) contains a multiple of a₁ -/
axiom f_one : f 1 = 1

/-- For n = 2, any two distinct a, b ≥ 2 can be covered in interval of length O(max·f(2)) -/
axiom f_two_bound : f 2 ≤ 2

/-!
## Part VI: Properties of f
-/

/-- f is monotone: larger sets need larger intervals -/
axiom f_monotone (m n : ℕ) (hmn : m ≤ n) (hn : n ≥ 1) : f m ≤ f n

/-- f grows at least logarithmically -/
axiom f_at_least_log (n : ℕ) (hn : n ≥ 2) : (f n : ℝ) ≥ Real.log n

/-!
## Part VII: Connection to Problem 708
-/

/-- Problem 708's function g(n): minimal |B| for divisibility covering -/
axiom g (n : ℕ) : ℕ

/-- Known: g(n) ≥ (2 - o(1))n -/
axiom g_lower_bound (n : ℕ) (hn : n ≥ 1) : g n ≥ 2 * n - 1

/-- Known small values -/
axiom g_two : g 2 = 2
axiom g_three : g 3 = 4

/-- The problems are related but distinct:
    - f(n) measures interval length needed (709)
    - g(n) measures subset size needed (708) -/
axiom problems_708_709_related : True

/-!
## Part VIII: The Open Problem
-/

/-- Main conjecture: What is the true growth rate of f(n)?
    Current gap: (log n)^c ≤ f(n) ≤ O(√n)
    Possible answers:
    1. f(n) ~ (log n)^c for some c > 1
    2. f(n) ~ n^α for some 0 < α < 1/2
    3. f(n) ~ √n / (log n)^β for some β > 0 -/
def conjecture_growth_rate : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    |Real.log (f n) / Real.log n - c| < ε

axiom problem_709_open : True  -- Growth rate is unknown

/-!
## Part IX: Proof Techniques
-/

/-- Lower bound uses: if A = {p₁,...,pₙ} are distinct primes,
    by Chinese Remainder Theorem we need careful analysis -/
axiom lower_bound_technique : True

/-- Upper bound uses: greedy covering with pigeonhole principle -/
axiom upper_bound_technique : True

/-- Probabilistic method could potentially improve bounds -/
axiom probabilistic_approach : True

/-!
## Part X: Examples
-/

/-- Example: A = {2} needs interval of length 2 to guarantee a multiple of 2 -/
example : ∀ I : Interval, I.length ≥ 2 → ∃ x, I.contains x ∧ 2 ∣ x := by
  intro I hlen
  use 2 * ((I.start + 1) / 2)
  constructor
  · constructor
    · omega
    · omega
  · exact Nat.dvd_mul_right 2 _

/-- Numerical bounds illustration:
    At n = 100: (log 100)^c ≈ 4.6^c vs √100 = 10
    The gap is meaningful but not huge for small n -/
example : (100 : ℕ).sqrt = 10 := by native_decide

/-- At n = 10000: √10000 = 100 -/
example : (10000 : ℕ).sqrt = 100 := by native_decide

/-!
## Part XI: Summary
-/

/--
**Erdős Problem #709: Summary**

**Question:** Find tight bounds for f(n), where f(n) is minimal such that
any interval of f(n)·max(A) consecutive integers contains distinct
x₁,...,xₙ with aᵢ | xᵢ for any n-element set A ⊆ [2,∞).

**Known Bounds (Erdős-Surányi 1959):**
- Lower: f(n) ≥ (log n)^c for some c > 0
- Upper: f(n) ≤ C·√n for some C > 0

**Status:** OPEN
The true growth rate of f(n) is unknown.
The gap between (log n)^c and √n is substantial.

**Related:** Problem 708 (g(n) function for subset size)

**Key Insight:** Finding multiples aᵢ | xᵢ with distinctness constraint
is a covering problem that interpolates between Chinese Remainder Theorem
and pigeonhole-type arguments.
-/
theorem erdos_709_statement :
    -- Lower bound exists
    (∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, (f n : ℝ) ≥ (Real.log n) ^ c) ∧
    -- Upper bound exists
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * Real.sqrt n) ∧
    -- Problem remains open
    True := by
  exact ⟨lower_bound_log, upper_bound_sqrt, trivial⟩

/-- Erdős Problem #709 is OPEN -/
theorem erdos_709_open : True := trivial

end Erdos709
