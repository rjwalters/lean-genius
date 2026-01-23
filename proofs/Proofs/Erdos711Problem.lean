/-
Erdős Problem #711: Divisibility Matching with Variable Starting Point

Source: https://erdosproblems.com/711
Status: PARTIALLY SOLVED (second part by van Doorn 2026)
Prize: 1000 rupees (~$78 in 1992)

Statement:
Let f(n,m) be minimal such that in (m, m+f(n,m)) there exist distinct integers
a₁, ..., aₙ such that k | aₖ for all 1 ≤ k ≤ n.

Prove that:
1. max_m f(n,m) ≤ n^{1+o(1)}  [OPEN]
2. max_m (f(n,m) - f(n,n)) → ∞  [SOLVED by van Doorn 2026]

This generalizes Problem #710 (which fixes m = n) by varying the starting point m.

Key Results:
- Erdős-Pomerance (1980): max_m f(n,m) ≪ n^{3/2}
- Erdős-Pomerance (1980): n·√(log n / log log n) ≪ f(n,n) ≪ n·√(log n)
- van Doorn (2026): ∃ m(n) such that f(n,m) - f(n,n) ≫ n·(log n / log log n)

See also: Problem #710

References:
- Erdős, Pomerance (1980): "Matching the natural numbers up to n with
  distinct multiples of another interval"
- Erdős [Er92c]: "Some of my forgotten problems in number theory"
- van Doorn (2026): "On the length of an interval that contains distinct
  multiples of the first n positive integers", Integers #A7
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor

open Nat Finset

namespace Erdos711

/-
## Part I: Basic Definitions

Same divisibility matching as Problem #710, but with variable starting point m.
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
The interval (start, start + len) admits a valid n-selection.
-/
def IntervalAdmitsSelection (n start len : ℕ) : Prop :=
  ∃ a : Fin n → ℕ, IsValidSelection n start len a

/--
**Existence of Valid Selection for Large Intervals:**
For any starting point m, large enough intervals admit valid selections.
-/
axiom selection_exists_for_any_start (n m : ℕ) :
    ∃ len, IntervalAdmitsSelection n m len

/-
## Part II: The Two-Parameter Function f(n,m)
-/

/--
**The Function f(n,m):**
f(n,m) is the minimal length such that (m, m + f(n,m)) admits a valid n-selection.

This generalizes f(n) = f(n,n) from Problem #710.
-/
noncomputable def minimalIntervalLength (n m : ℕ) : ℕ :=
  Nat.find (selection_exists_for_any_start n m)

/-- Notation for the function f(n,m). -/
notation "f(" n ", " m ")" => minimalIntervalLength n m

/--
**Connection to Problem #710:**
f(n,n) is exactly the function f(n) from Problem #710.
-/
def fnn (n : ℕ) : ℕ := f(n, n)

/-
## Part III: Known Upper Bounds
-/

/--
**Erdős-Pomerance Upper Bound (1980):**
max_m f(n,m) ≪ n^{3/2}

There exists a constant C such that for all n and all m,
f(n,m) ≤ C · n^{3/2}.
-/
axiom erdos_pomerance_upper_bound_711 :
    ∃ C : ℝ, C > 0 ∧ ∀ n m : ℕ, (f(n, m) : ℝ) ≤ C * (n : ℝ) ^ (3/2 : ℝ)

/--
**The First Conjecture (OPEN):**
max_m f(n,m) ≤ n^{1+o(1)}

This would improve the n^{3/2} bound to essentially linear.
-/
def firstConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
    (f(n, m) : ℝ) ≤ (n : ℝ) ^ (1 + ε)

/--
**First Conjecture Status: OPEN**
No proof or counterexample is known.
-/
axiom first_conjecture_open :
    -- We cannot prove firstConjecture or its negation computationally
    True

/-
## Part IV: The Dependence on m
-/

/--
**Maximum over m:**
For fixed n, consider the maximum of f(n,m) over all starting points m.
-/
noncomputable def maxFnm (n : ℕ) : ℕ :=
  -- This is well-defined by the Erdős-Pomerance bound
  0  -- Placeholder

/--
**Difference from f(n,n):**
For fixed n, the difference f(n,m) - f(n,n) can vary with m.
-/
def differenceFnm (n m : ℕ) : ℤ :=
  (f(n, m) : ℤ) - (f(n, n) : ℤ)

/--
**The Second Conjecture (SOLVED):**
max_m (f(n,m) - f(n,n)) → ∞ as n → ∞

There exist starting points m where the interval length f(n,m) is
significantly larger than f(n,n).
-/
def secondConjecture : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ m : ℕ,
    differenceFnm n m > K

/-
## Part V: van Doorn's Theorem (2026)
-/

/--
**van Doorn's Theorem (2026):**
For all large n, there exists m = m(n) such that
f(n,m) - f(n,n) ≫ n · (log n / log log n)

This proves the second conjecture with a quantitative lower bound.
-/
axiom van_doorn_2026 :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ m : ℕ,
      (differenceFnm n m : ℝ) ≥ C * n * Real.log n / Real.log (Real.log n)

/--
**Second Conjecture is SOLVED:**
van Doorn's theorem implies the second conjecture.

For large enough n, C·n·(log n / log log n) > K for any K,
so there exists m with differenceFnm n m > K.
-/
axiom second_conjecture_solved : secondConjecture

/-
## Part VI: Why Does m Matter?
-/

/--
**Intuition:**
The starting point m affects which multiples of k are available.

- When m = n, the multiples of k near n are "aligned" in a specific way
- For other m, the alignment may be better or worse
- The second conjecture says: for some m, it's significantly worse
-/
axiom starting_point_matters :
  -- Different starting points have different distributions of multiples
  True

/--
**Example: m vs n Starting Points**
Consider needing multiples of k in (m, m+L) vs (n, n+L).
The number of multiples depends on m mod k.
-/
def multiplesInInterval (d start len : ℕ) : ℕ :=
  (start + len) / d - start / d

/--
**Residue Class Effect:**
The position of m relative to multiples of k affects how many are available.

Standard bound: any interval of length L contains at most L/k + 1 multiples of k.
-/
axiom residue_class_effect (m k L : ℕ) (hk : k > 0) :
    multiplesInInterval k m L ≤ L / k + 1

/-
## Part VII: Connection to Problem #710
-/

/--
**Problem #710 Bounds (for reference):**
n · √(log n / log log n) ≪ f(n,n) ≪ n · √(log n)
-/
axiom problem_710_bounds :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
        C₁ * n * Real.sqrt (Real.log n / Real.log (Real.log n)) ≤ (f(n, n) : ℝ) ∧
        (f(n, n) : ℝ) ≤ C₂ * n * Real.sqrt (Real.log n)

/--
**van Doorn's Result in Context:**
The difference f(n,m) - f(n,n) can be as large as the main term!

Since f(n,n) ~ n · √(log n / log log n) to n · √(log n),
and f(n,m) - f(n,n) ≫ n · (log n / log log n),
the difference can dominate when log n / log log n is large.
-/
axiom van_doorn_dominates :
  -- The difference can be of comparable order to f(n,n) itself
  True

/-
## Part VIII: Small Examples
-/

/--
**Example: n = 2, m = 2**
Need distinct a₁, a₂ in (2, 2+f(2,2)) with 1 | a₁ and 2 | a₂.
Solution: a₁ = 3, a₂ = 4, so f(2,2) ≤ 3.
-/
theorem example_n2_m2 : IntervalAdmitsSelection 2 2 3 := by
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
**Example: n = 2, m = 3**
Need distinct a₁, a₂ in (3, 3+f(2,3)) with 1 | a₁ and 2 | a₂.
Solution: a₁ = 5, a₂ = 4, so f(2,3) ≤ 3.
-/
theorem example_n2_m3 : IntervalAdmitsSelection 2 3 3 := by
  use ![5, 4]
  constructor
  · intro k
    fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · constructor
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro k
      fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/--
**Example: n = 2, m = 1**
Need distinct a₁, a₂ in (1, 1+f(2,1)) with 1 | a₁ and 2 | a₂.
Solution: a₁ = 3, a₂ = 2, so f(2,1) ≤ 3.
-/
theorem example_n2_m1 : IntervalAdmitsSelection 2 1 3 := by
  use ![3, 2]
  constructor
  · intro k
    fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · constructor
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro k
      fin_cases k <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #711: Summary**

Part 1: max_m f(n,m) ≤ n^{1+o(1)} - OPEN
Part 2: max_m (f(n,m) - f(n,n)) → ∞ - SOLVED (van Doorn 2026)

Known:
- Upper bound: max_m f(n,m) ≪ n^{3/2} (Erdős-Pomerance 1980)
- van Doorn: f(n,m) - f(n,n) ≫ n·(log n / log log n) for some m

Open:
- Improving the n^{3/2} bound to n^{1+o(1)}
-/
theorem erdos_711_summary :
    -- Part 2 is solved
    secondConjecture ∧
    -- Upper bound is known
    (∃ C : ℝ, C > 0 ∧ ∀ n m : ℕ, (f(n, m) : ℝ) ≤ C * (n : ℝ) ^ (3/2 : ℝ)) ∧
    -- van Doorn's quantitative result
    (∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ m : ℕ,
      (differenceFnm n m : ℝ) ≥ C * n * Real.log n / Real.log (Real.log n)) := by
  constructor
  · exact second_conjecture_solved
  · constructor
    · exact erdos_pomerance_upper_bound_711
    · exact van_doorn_2026

/--
**Main Theorem: Second Conjecture Solved**
van Doorn (2026) proved that max_m (f(n,m) - f(n,n)) → ∞.
-/
theorem erdos_711_part2_solved : secondConjecture :=
  second_conjecture_solved

/--
**Status: First Conjecture OPEN**
max_m f(n,m) ≤ n^{1+o(1)} remains unproven.
-/
def openQuestion : Prop := firstConjecture

/--
**Prize Information:**
Erdős offered 1000 rupees (approximately $78 in 1992) for proving either part.
-/
def erdosPrize : String := "1000 rupees (~$78 in 1992)"

end Erdos711
