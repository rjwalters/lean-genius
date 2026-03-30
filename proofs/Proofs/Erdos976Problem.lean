/-
Erdős Problem #976: Greatest Prime Divisor of Polynomial Products

Source: https://erdosproblems.com/976
Status: OPEN (main conjectures)

Statement:
Let f ∈ ℤ[x] be an irreducible polynomial of degree d ≥ 2.
Let F_f(n) = max{p prime : p | f(m) for some 1 ≤ m ≤ n}.
Equivalently, F_f(n) = greatest prime divisor of ∏_{m=1}^n f(m).

Question: Is F_f(n) ≫ n^{1+c} for some c > 0? Or even ≫ n^d?

Known Bounds:
- Nagell-Ricci (1922): F_f(n) ≫ n log n
- Erdős (1952): F_f(n) ≫ n(log n)^{log log log n}
- Tenenbaum (1990): F_f(n) ≫ n exp((log n)^c) for some c > 0

The polynomial growth conjectures (n^{1+c} or n^d) remain OPEN.

References:
- Nagell-Ricci [Na22]: Initial bound
- Erdős [Er52c]: Improved iterated log bound
- Erdős-Schinzel [ErSc90]: Weaker intermediate bound
- Tenenbaum [Te90]: Current best rigorous bound
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Polynomial.Basic

namespace Erdos976

/-
## Part I: Basic Definitions
-/

/--
**Irreducible polynomial over ℤ:**
A polynomial that cannot be factored into polynomials of smaller degree.
-/
def isIrreducible (f : Polynomial ℤ) : Prop :=
  f.degree ≥ 1 ∧ ∀ g h : Polynomial ℤ, f = g * h → g.degree = 0 ∨ h.degree = 0

/--
**Degree of polynomial:**
The highest power of x with nonzero coefficient.
-/
def polyDegree (f : Polynomial ℤ) : ℕ := f.natDegree

/--
**Greatest prime divisor:**
P(n) = max{p prime : p | n}, with P(1) = 1 by convention.
-/
def greatestPrimeDivisor (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else Nat.factors n |>.maximum? |>.getD 1

/--
**The function F_f(n):**
F_f(n) = greatest prime dividing any f(m) for 1 ≤ m ≤ n.
Equivalently, greatest prime divisor of ∏_{m=1}^n f(m).
-/
def F_f (f : Polynomial ℤ) (n : ℕ) : ℕ :=
  (List.range n).map (fun m => greatestPrimeDivisor (f.eval (m + 1)).natAbs)
    |>.maximum? |>.getD 1

/-
## Part II: Known Lower Bounds
-/

/--
**Nagell-Ricci bound (1922):**
F_f(n) ≫ n log n for any irreducible f of degree ≥ 2.
-/
/--
**Erdős bound (1952):**
F_f(n) ≫ n(log n)^{log log log n}.
Improved the Nagell-Ricci bound using sieve methods.
-/
/--
**Tenenbaum bound (1990):**
F_f(n) ≫ n exp((log n)^c) for some c > 0.
Currently the best rigorous bound.
-/
axiom tenenbaum_bound (f : Polynomial ℤ) :
    isIrreducible f → polyDegree f ≥ 2 →
    ∃ C c : ℝ, C > 0 ∧ c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (F_f f n : ℝ) ≥ C * n * Real.exp ((Real.log n) ^ c)

/-
## Part III: The Main Conjectures
-/

/--
**First conjecture: polynomial growth with exponent > 1:**
F_f(n) ≫ n^{1+c} for some c > 0.
-/
def conjecture_polynomial_growth (f : Polynomial ℤ) : Prop :=
  isIrreducible f → polyDegree f ≥ 2 →
  ∃ C c : ℝ, C > 0 ∧ c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (F_f f n : ℝ) ≥ C * (n : ℝ) ^ (1 + c)

/--
**Stronger conjecture: growth like n^d:**
F_f(n) ≫ n^d where d = deg(f).
-/
def conjecture_degree_growth (f : Polynomial ℤ) : Prop :=
  isIrreducible f → polyDegree f ≥ 2 →
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (F_f f n : ℝ) ≥ C * (n : ℝ) ^ (polyDegree f)

/-
## Part IV: Upper Bounds
-/

/--
**Trivial upper bound:**
F_f(n) ≤ max_{1≤m≤n} |f(m)| ≈ n^d for polynomial of degree d.
-/
/-
## Part V: Computational Examples
-/

/-- P(n) = greatest prime factor of n. -/
def P (n : ℕ) : ℕ := greatestPrimeDivisor n

/--
**Examples of greatest prime divisor:**
Computational verification of P(n) for small values.
-/
example : greatestPrimeDivisor 1 = 1 := by rfl
example : greatestPrimeDivisor 2 = 2 := by native_decide
example : greatestPrimeDivisor 6 = 3 := by native_decide  -- 6 = 2 · 3
example : greatestPrimeDivisor 30 = 5 := by native_decide  -- 30 = 2 · 3 · 5
example : greatestPrimeDivisor 60 = 5 := by native_decide  -- 60 = 2² · 3 · 5
example : greatestPrimeDivisor 210 = 7 := by native_decide  -- 210 = 2 · 3 · 5 · 7
example : greatestPrimeDivisor 100 = 5 := by native_decide  -- 100 = 2² · 5²

/--
**Numerical comparison of bounds:**
At n = 1000, for degree d = 2:
- Nagell-Ricci (n log n): ~6908
- Conjectured (n^2): 1,000,000
-/
example : (1000 : ℕ) * 7 = 7000 := by native_decide  -- ≈ n log n
example : (1000 : ℕ) ^ 2 = 1000000 := by native_decide  -- n^d for d=2

/-
## Part VI: Summary
-/

/--
**Summary of Erdős Problem #976:**

PROBLEM: For irreducible f ∈ ℤ[x] of degree d ≥ 2,
let F_f(n) = greatest prime dividing ∏_{m=1}^n f(m).
Is F_f(n) ≫ n^{1+c} for some c > 0? Or ≫ n^d?

STATUS: OPEN (for the main conjectures)

KNOWN BOUNDS:
1. F_f(n) ≫ n log n (Nagell-Ricci 1922)
2. F_f(n) ≫ n(log n)^{log log log n} (Erdős 1952)
3. F_f(n) ≫ n exp((log n)^c) (Tenenbaum 1990) — BEST KNOWN
-/
theorem erdos_976_status :
    ∀ f : Polynomial ℤ, isIrreducible f → polyDegree f ≥ 2 →
    ∃ C c : ℝ, C > 0 ∧ c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (F_f f n : ℝ) ≥ C * n * Real.exp ((Real.log n) ^ c) := by
  intro f h_irred h_deg
  exact tenenbaum_bound f h_irred h_deg

end Erdos976
