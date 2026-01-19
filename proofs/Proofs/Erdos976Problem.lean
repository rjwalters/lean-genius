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
axiom nagell_ricci_bound (f : Polynomial ℤ) :
    isIrreducible f → polyDegree f ≥ 2 →
    ∃ C > 0, ∀ n : ℕ, n ≥ 2 → (F_f f n : ℝ) ≥ C * n * Real.log n

/--
**Erdős bound (1952):**
F_f(n) ≫ n(log n)^{log log log n}.
Improved the Nagell-Ricci bound using sieve methods.
-/
axiom erdos_1952_bound (f : Polynomial ℤ) :
    isIrreducible f → polyDegree f ≥ 2 →
    ∃ C > 0, ∀ n : ℕ, n ≥ 16 →
      (F_f f n : ℝ) ≥ C * n * Real.log n ^ Real.log (Real.log (Real.log n))

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

/--
**Status of conjectures:**
Both conjectures remain OPEN.
-/
axiom conjectures_open : True

/-
## Part IV: Special Cases
-/

/--
**Linear case is trivial:**
For degree 1 polynomials, the problem is equivalent to
studying prime factors in arithmetic progressions (Dirichlet).
-/
axiom linear_case : True

/--
**Quadratic polynomials:**
For f(x) = x² + 1 or similar, the question connects to
Gaussian primes and their distribution.
-/
axiom quadratic_case : True

/--
**Example: f(x) = x² - 2:**
The product ∏(m² - 2) involves primes ≡ ±1 (mod 8)
by quadratic reciprocity.
-/
axiom example_x2_minus_2 : True

/--
**Cyclotomic polynomials:**
For Φ_n(x), there are special results due to
the algebraic structure of roots of unity.
-/
axiom cyclotomic_case : True

/-
## Part V: Proof Techniques
-/

/--
**Sieve methods:**
Erdős's improvements used sieve techniques to count
integers with large prime factors.
-/
axiom sieve_methods : True

/--
**Large sieve:**
Tenenbaum's proof uses sophisticated large sieve inequalities.
-/
axiom large_sieve : True

/--
**Algebraic number theory:**
The distribution of prime divisors of f(m) relates to
splitting of primes in the number field ℚ[x]/(f).
-/
axiom algebraic_connection : True

/--
**Chebotarev density theorem:**
Primes dividing f(m) for some m have positive density
determined by the Galois group of f.
-/
axiom chebotarev : True

/-
## Part VI: Related Functions
-/

/--
**P(n) = greatest prime factor of n:**
The classical greatest prime factor function.
P(∏f(m)) is what we're studying.
-/
def P (n : ℕ) : ℕ := greatestPrimeDivisor n

/--
**Comparison with P(n!):**
P(n!) grows like n (the largest prime ≤ n).
For polynomial products, growth should be faster.
-/
axiom comparison_factorial : True

/--
**Smoothness:**
An integer is y-smooth if all prime factors are ≤ y.
The problem asks: how non-smooth is ∏f(m)?
-/
axiom smoothness_connection : True

/-
## Part VII: Historical Notes
-/

/--
**Erdős's unpublished claim:**
In 1965, Erdős claimed a proof of F_f(n) ≫ n exp((log n)^c)
but said it was "fairly complicated" and never published.
The proof was later found to be flawed.
-/
axiom erdos_flawed_claim : True

/--
**Erdős-Schinzel 1990:**
Published a weaker bound, apparently unaware of Erdős's
earlier flawed claim or its issues.
-/
axiom erdos_schinzel_1990 : True

/--
**Tenenbaum's contribution:**
Finally provided a rigorous proof of the stronger bound
that Erdős had claimed.
-/
axiom tenenbaum_contribution : True

/-
## Part VIII: Upper Bounds
-/

/--
**Trivial upper bound:**
F_f(n) ≤ max_{1≤m≤n} |f(m)| ≈ n^d for polynomial of degree d.
-/
axiom trivial_upper_bound (f : Polynomial ℤ) :
    isIrreducible f → polyDegree f ≥ 2 →
    ∃ C : ℝ, ∀ n : ℕ, (F_f f n : ℝ) ≤ C * (n : ℝ) ^ (polyDegree f)

/--
**Gap between bounds:**
Current lower bound: n exp((log n)^c)
Conjectured: n^{1+c} or n^d
Upper bound: n^d
The gap is significant!
-/
axiom gap_in_bounds : True

/-
## Part IX: Summary
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
3. F_f(n) ≫ n exp((log n)^c) (Tenenbaum 1990) - BEST KNOWN

The gap between current bounds and the conjectures is huge.
The polynomial growth conjecture (n^{1+c}) remains unproved.

KEY INSIGHTS:
1. Connected to prime distribution in polynomial values
2. Algebraic number theory (splitting of primes)
3. Sieve methods and large sieve inequalities
4. The degree d should control the growth rate

A fundamental problem connecting analytic and algebraic number theory.
-/
theorem erdos_976_status :
    -- Current best bound: Tenenbaum's result
    ∀ f : Polynomial ℤ, isIrreducible f → polyDegree f ≥ 2 →
    ∃ C c : ℝ, C > 0 ∧ c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (F_f f n : ℝ) ≥ C * n * Real.exp ((Real.log n) ^ c) := by
  intro f h_irred h_deg
  exact tenenbaum_bound f h_irred h_deg

/--
**Problem status:**
Erdős Problem #976 is OPEN for the main conjectures.
-/
theorem erdos_976_open : True := trivial

end Erdos976
