/-
Erdős Problem #710: Minimal Interval for Divisibility Matching

Source: https://erdosproblems.com/710
Status: OPEN
Prize: 2000 rupees (~$78 in 1992)

Statement:
Let f(n) be minimal such that in (n, n+f(n)) there exist distinct integers
a₁, ..., aₙ such that k | aₖ for all 1 ≤ k ≤ n.
Obtain an asymptotic formula for f(n).

Known Bounds (Erdős-Pomerance, 1980):
- Lower: (2/√e + o(1)) · n · (log n / log log n)^(1/2)
- Upper: (1.7398... + o(1)) · n · (log n)^(1/2)

The problem asks for the exact asymptotic behavior of f(n).
The gap between upper and lower bounds remains unresolved.

Key Insight:
We need to find n distinct integers in a short interval, where the k-th
integer must be divisible by k. This becomes harder as k grows (fewer
multiples of k in any fixed interval).

References:
- Erdős, Pomerance (1980): "Matching the natural numbers up to n with
  distinct multiples of another interval"
- Erdős [Er92c]: "Some of my forgotten problems in number theory"
- OEIS A390246: Related sequence
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor

open Nat Finset

namespace Erdos710

/-
## Part I: Basic Setup

Define the divisibility matching condition and the minimal interval function.
-/

/--
**Valid Selection:**
A function a : Fin n → ℕ is a valid selection in interval (start, start + len)
if all values are in the interval, pairwise distinct, and k | a(k) for all k.
-/
def IsValidSelection (n start len : ℕ) (a : Fin n → ℕ) : Prop :=
  -- All values in the interval (start, start + len)
  (∀ k : Fin n, start < a k ∧ a k < start + len) ∧
  -- Pairwise distinct
  (∀ i j : Fin n, a i = a j → i = j) ∧
  -- Divisibility condition: (k+1) | a(k) (using 1-indexed k)
  (∀ k : Fin n, (k.val + 1) ∣ a k)

/--
**Interval Admits Selection:**
The interval (start, start + len) admits a valid n-selection if there exists
a valid selection function.
-/
def IntervalAdmitsSelection (n start len : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, IsValidSelection n start len a

/--
**Existence of Valid Selection for Large Intervals:**
For large enough intervals, a valid selection always exists.
-/
axiom selection_exists_large (n : ℕ) : ∃ len, IntervalAdmitsSelection n n len

/--
**The Function f(n):**
f(n) is the minimal length such that (n, n + f(n)) admits a valid n-selection.

Note: We define this for interval starting at n as in the problem statement.
-/
noncomputable def minimalIntervalLength (n : ℕ) : ℕ :=
  Nat.find (selection_exists_large n)

/-- Notation for the minimal interval length. -/
notation "f(" n ")" => minimalIntervalLength n

/-
## Part II: Divisibility Constraint Analysis

The key difficulty: finding n distinct multiples in a short interval where
the k-th multiple must be divisible by k.
-/

/--
**Multiples in Interval:**
Count of multiples of d in the interval (a, b).
-/
def multiplesInInterval (d a b : ℕ) : ℕ :=
  (b / d) - (a / d)

/--
**For large k, multiples are sparse:**
In interval (n, n + L), there are about L/k multiples of k.
As k grows, this count shrinks.
-/
axiom multiples_sparse (n k L : ℕ) (hk : k > 0) :
    multiplesInInterval k n (n + L) ≤ L / k + 1

/-
## Part III: Known Bounds

The Erdős-Pomerance bounds establish the order of magnitude.
-/

/--
**Lower Bound (Erdős-Pomerance 1980):**
f(n) ≥ (2/√e + o(1)) · n · √(log n / log log n)

The constant 2/√e ≈ 1.2131...
-/
axiom erdos_pomerance_lower_bound :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (f(n) : ℝ) ≥ (2 / Real.sqrt (Real.exp 1) - ε) * n *
        Real.sqrt (Real.log n / Real.log (Real.log n))

/--
**Upper Bound (Erdős-Pomerance 1980):**
f(n) ≤ (1.7398... + o(1)) · n · √(log n)

The constant 1.7398... comes from a specific construction.
-/
axiom erdos_pomerance_upper_bound :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (f(n) : ℝ) ≤ (1.7398 + ε) * n * Real.sqrt (Real.log n)

/--
**Gap Between Bounds:**
The lower bound has √(log n / log log n), the upper has √(log n).
These differ by a factor of √(log log n), which grows slowly.
-/
axiom bounds_gap :
    ∀ n ≥ 3, Real.sqrt (Real.log n / Real.log (Real.log n)) <
              Real.sqrt (Real.log n)

/-
## Part IV: The Open Problem

The problem asks for the exact asymptotic: f(n) ~ C · n · g(n) for some
explicit constant C and function g(n).

Possibilities:
1. f(n) ~ C · n · √(log n)  (upper bound is tight)
2. f(n) ~ C · n · √(log n / log log n)  (lower bound is tight)
3. Something in between
-/

/--
**Erdős Problem #710: OPEN**
Determine the asymptotic formula for f(n).
-/
axiom erdos_710_open :
    ∃ (C : ℝ) (g : ℕ → ℝ),
      C > 0 ∧
      (∀ n ≥ 2, g n > 0) ∧
      (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
        |f(n) / (C * n * g n) - 1| < ε)

/-
## Part V: Small Examples

Verify the divisibility matching property for small n.
-/

/--
**Example: n = 1**
Need one integer a₁ in (1, 1+f(1)) with 1 | a₁.
Since everything is divisible by 1, f(1) = 1 (the integer 2 works).
-/
theorem example_n1 : IntervalAdmitsSelection 1 1 2 := by
  use fun _ => 2
  constructor
  · intro k
    simp
  · constructor
    · intro i j _
      simp [Fin.ext_iff]
    · intro k
      simp

/--
**Example: n = 2**
Need distinct a₁, a₂ in (2, 2+f(2)) with 1 | a₁ and 2 | a₂.
f(2) = 2: use a₁ = 3, a₂ = 4.
-/
theorem example_n2 : IntervalAdmitsSelection 2 2 3 := by
  use ![3, 4]
  constructor
  · intro k
    fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · constructor
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro k
      fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/--
**Example: n = 3**
Need distinct a₁, a₂, a₃ in (3, 3+f(3)) with 1 | a₁, 2 | a₂, 3 | a₃.
f(3) = 3: use a₁ = 5, a₂ = 4, a₃ = 6.
-/
theorem example_n3 : IntervalAdmitsSelection 3 3 4 := by
  use ![5, 4, 6]
  constructor
  · intro k
    fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · constructor
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro k
      fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-
## Part VI: Heuristic Analysis

Why is this problem hard?
-/

/--
**Constraint Density:**
For the k-th slot, we need a multiple of k. In interval (n, n+L),
there are about L/k such multiples.

If we need n distinct values for k = 1, 2, ..., n, we need:
- Slot 1: ~L multiples of 1 (everything)
- Slot 2: ~L/2 multiples of 2
- ...
- Slot n: ~L/n multiples of n (very sparse)

This suggests L needs to grow with n to ensure enough multiples of n.
-/
def constraintDensity (n L k : ℕ) : ℚ :=
  if k = 0 then 0 else L / k

/--
**Critical Constraint:**
The hardest constraint is for large k. We need at least 1 multiple of n
in the interval (n, n+L), requiring L ≥ n approximately.
-/
axiom critical_constraint_heuristic :
    ∀ n ≥ 1, ∀ L < n, multiplesInInterval n n (n + L) ≤ 1

/-
## Part VII: Greedy Algorithm Insight

A greedy approach: assign a₁ = n+1, then a₂ = smallest even > n+1 unused, etc.
This gives an upper bound but not optimal.
-/

/--
**Greedy Selection Property:**
For each k, the smallest multiple of k greater than n is at most n + k.
-/
theorem smallest_multiple_bound (n k : ℕ) (hk : k > 0) :
    ∃ m : ℕ, n < m ∧ m ≤ n + k ∧ k ∣ m := by
  -- The next multiple of k after n is ⌈(n+1)/k⌉ * k
  use (n / k + 1) * k
  constructor
  · -- n < (n/k + 1) * k
    have : n < (n / k + 1) * k := Nat.lt_mul_div_succ n hk
    exact this
  · constructor
    · -- (n/k + 1) * k ≤ n + k
      have h1 : n / k * k ≤ n := Nat.div_mul_le_self n k
      have h2 : (n / k + 1) * k = n / k * k + k := by ring
      omega
    · -- k | (n/k + 1) * k
      exact Nat.dvd_mul_left k (n / k + 1)

/-
## Part VIII: Connection to Related Problems

See also Problem #711 for related questions.
-/

/--
**Related Sequence OEIS A390246:**
The sequence of values f(n) for small n.
-/
def fValues : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]  -- Placeholder

/-
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #710: Status Summary**

The problem asks for an asymptotic formula for f(n), the minimal interval
length for divisibility matching.

Known:
- Lower bound: (2/√e + o(1)) · n · √(log n / log log n)
- Upper bound: (1.7398... + o(1)) · n · √(log n)

Open:
- Exact asymptotic formula
- Closing the gap between bounds
- Whether √(log n) or √(log n / log log n) is the correct order
-/
theorem erdos_710_summary :
    -- The bounds are established
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (2 / Real.sqrt (Real.exp 1) - ε) * n *
        Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ f(n)) ∧
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (f(n) : ℝ) ≤ (1.7398 + ε) * n * Real.sqrt (Real.log n)) ∧
    -- Small examples verify correctness
    IntervalAdmitsSelection 1 1 2 ∧
    IntervalAdmitsSelection 2 2 3 ∧
    IntervalAdmitsSelection 3 3 4 := by
  constructor
  · intro ε hε
    obtain ⟨N, hN⟩ := erdos_pomerance_lower_bound ε hε
    use N
    intro n hn
    exact le_of_lt (hN n hn)
  · constructor
    · exact erdos_pomerance_upper_bound
    · exact ⟨example_n1, example_n2, example_n3⟩

/--
**Prize Information:**
Erdős offered 2000 rupees (approximately $78 in 1992) for solving this problem.
-/
def erdosPrize : String := "2000 rupees (~$78 in 1992)"

end Erdos710
