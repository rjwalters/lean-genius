/-
Erdős Problem #144: Propinquity of Divisors

Source: https://erdosproblems.com/144
Status: SOLVED (Maier-Tenenbaum 1984)
Prize: $250 (Tenenbaum reported receiving $650)

Statement:
The density of integers which have two divisors d₁, d₂ such that
d₁ < d₂ < 2d₁ exists and equals 1.

Stronger Version:
For any constant c > 1, the density of integers with divisors
d₁ < d₂ < c·d₁ also equals 1.

Resolution:
Maier and Tenenbaum proved YES to both versions in 1984.
The threshold β = log 3 - 1 separates density 1 from density 0
for the refined version with d₂ < d₁(1 + (log n)^{-β}).

Historical Note:
Erdős initially claimed a proof in 1964 but retracted it in 1979.
Erdős and Hall proved the complementary result (density 0 for β > log 3 - 1).

References:
- Maier-Tenenbaum [MaTe84]: Complete proof of density 1
- Erdős-Hall [ErHa79]: Density 0 for β > log 3 - 1
- Erdős [Er79]: Posed stronger version with c > 1
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics

namespace Erdos144

/-
## Part I: Basic Definitions
-/

/--
**Natural density of a set:**
d(A) = lim_{n→∞} |A ∩ {1,...,n}| / n.
-/
def naturalDensity (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N,
    |((Finset.filter (· ∈ A) (Finset.range n)).card : ℝ) / n - d| < ε

/--
**Close divisors property:**
An integer n has "close divisors" if there exist divisors d₁ < d₂
with d₂ < 2d₁.
-/
def hasCloseDivisors (n : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁

/--
**c-close divisors property:**
For constant c > 1, n has c-close divisors if there exist
divisors d₁ < d₂ with d₂ < c·d₁.
-/
def hasCloseDivisorsC (c : ℝ) (n : ℕ) : Prop :=
  c > 1 ∧ ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ (d₂ : ℝ) < c * d₁

/--
**The set of integers with close divisors:**
A = {n ∈ ℕ : n has two divisors d₁ < d₂ < 2d₁}.
-/
def closeDivisorsSet : Set ℕ := {n | hasCloseDivisors n}

/--
**The set with c-close divisors:**
A_c = {n ∈ ℕ : n has divisors d₁ < d₂ < c·d₁}.
-/
def closeDivisorsSetC (c : ℝ) : Set ℕ := {n | hasCloseDivisorsC c n}

/-
## Part II: The Main Theorem
-/

/--
**Erdős Problem #144 (Basic Version):**
The density of integers with close divisors equals 1.
-/
def erdos_144_conjecture : Prop :=
  naturalDensity closeDivisorsSet 1

/--
**Erdős Problem #144 (Strong Version):**
For any c > 1, the density of integers with c-close divisors equals 1.
-/
def erdos_144_strong_conjecture (c : ℝ) : Prop :=
  c > 1 → naturalDensity (closeDivisorsSetC c) 1

/--
**Maier-Tenenbaum Theorem (1984):**
The conjecture is true: density equals 1.
-/
axiom maier_tenenbaum_theorem : erdos_144_conjecture

/--
**Maier-Tenenbaum Strong Theorem:**
For any c > 1, the density of c-close divisors equals 1.
-/
axiom maier_tenenbaum_strong : ∀ c : ℝ, erdos_144_strong_conjecture c

/-
## Part III: The Threshold β = log 3 - 1
-/

/--
**The critical exponent:**
β* = log 3 - 1 ≈ 0.0986 is the threshold.
-/
def criticalExponent : ℝ := Real.log 3 - 1

/--
**Refined close divisors with log factor:**
n has (β)-close divisors if there exist d₁ < d₂ with
d₂ < d₁(1 + (log n)^{-β}).
-/
def hasRefinedCloseDivisors (β : ℝ) (n : ℕ) : Prop :=
  n ≥ 2 ∧ ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧
    (d₂ : ℝ) < d₁ * (1 + (Real.log n) ^ (-β))

/--
**The set with (β)-close divisors:**
-/
def refinedCloseDivisorsSet (β : ℝ) : Set ℕ :=
  {n | hasRefinedCloseDivisors β n}

/--
**Erdős-Hall Theorem (1979):**
If β > log 3 - 1, the density of (β)-close divisors equals 0.
-/
axiom erdos_hall_theorem (β : ℝ) :
    β > criticalExponent →
    naturalDensity (refinedCloseDivisorsSet β) 0

/--
**Maier-Tenenbaum Refined Theorem:**
If β < log 3 - 1, the density of (β)-close divisors equals 1.
-/
axiom maier_tenenbaum_refined (β : ℝ) :
    β < criticalExponent →
    naturalDensity (refinedCloseDivisorsSet β) 1

/--
**Phase transition at β* = log 3 - 1:**
The density jumps from 0 to 1 at the critical exponent.
-/
theorem phase_transition :
    (∀ β > criticalExponent, naturalDensity (refinedCloseDivisorsSet β) 0) ∧
    (∀ β < criticalExponent, naturalDensity (refinedCloseDivisorsSet β) 1) := by
  exact ⟨erdos_hall_theorem, maier_tenenbaum_refined⟩

/-
## Part IV: Examples and Intuition
-/

/--
**Example: Prime powers have no close divisors:**
If n = p^k (prime power), consecutive divisors are p^j and p^{j+1},
so d₂/d₁ = p ≥ 2. Hence prime powers fail the close divisors test.
-/
axiom prime_powers_fail : ∀ p k : ℕ, Nat.Prime p → k ≥ 1 →
    ¬hasCloseDivisors (p ^ k)

/--
**Example: 6 has close divisors:**
6 = 2 · 3, divisors are 1, 2, 3, 6.
We have 2 < 3 < 2 · 2 = 4. So d₁ = 2, d₂ = 3 works.
-/
example : hasCloseDivisors 6 := by
  use 2, 3
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/--
**Example: 12 has close divisors:**
12 = 2² · 3, divisors are 1, 2, 3, 4, 6, 12.
We have 3 < 4 < 6 = 2 · 3. So d₁ = 3, d₂ = 4 works.
-/
example : hasCloseDivisors 12 := by
  use 3, 4
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num

/--
**Intuition: Most integers are "lumpy":**
Most integers have many prime factors, making divisors cluster.
The more prime factors, the more divisors, the more likely close pairs exist.
-/
axiom intuition_many_primes : True

/-
## Part V: Erdős's Retracted Claim
-/

/--
**Erdős's 1964 claim (later retracted):**
Originally claimed density 1 for β < log 3 - 1 in [Er64h],
but the proof had an error. Retracted in [ErHa79].
-/
axiom erdos_1964_retracted_claim : True

/--
**The correction in 1979:**
Erdős and Hall fixed the record by proving the complementary
result (density 0 for β > log 3 - 1).
-/
axiom erdos_hall_1979_correction : True

/--
**The final resolution:**
Maier and Tenenbaum completed the picture by proving
density 1 for β < log 3 - 1, vindicating the original conjecture.
-/
axiom maier_tenenbaum_1984_completion : True

/-
## Part VI: Proof Techniques
-/

/--
**Divisor distribution:**
The proof uses the distribution of divisors of typical integers.
Most divisors cluster around n^{1/2} by the divisor function properties.
-/
axiom divisor_distribution_technique : True

/--
**Erdős-Kac theorem connection:**
The number of prime factors follows approximately a normal distribution.
This contributes to the density 1 result - most integers have many factors.
-/
axiom erdos_kac_connection : True

/--
**Probabilistic arguments:**
The proof uses probabilistic number theory to show "generic"
integers have close divisors.
-/
axiom probabilistic_methods : True

/--
**Moment calculations:**
Higher moments of divisor counts are used to bound exceptional sets.
-/
axiom moment_calculations : True

/-
## Part VII: Related Problems
-/

/--
**Problem 449: Divisor ratio function:**
Related problem about the ratio d_{i+1}/d_i of consecutive divisors.
-/
axiom related_problem_449 : True

/--
**Problem 884: Divisor gaps:**
Studies the distribution of gaps between consecutive divisors.
-/
axiom related_problem_884 : True

/--
**Guy's Problem E3:**
This problem is discussed as Problem E3 in Richard Guy's
"Unsolved Problems in Number Theory".
-/
axiom guy_problem_E3 : True

/-
## Part VIII: The Prize
-/

/--
**The original prize:**
Erdős offered $250 for the solution.
-/
axiom original_prize : True

/--
**The actual payment:**
Tenenbaum reported that they received $650, suggesting
additional prizes for the stronger versions.
-/
axiom actual_payment : True

/-
## Part IX: Summary
-/

/--
**Summary of Erdős Problem #144:**

PROBLEM: Does the density of integers with close divisors
(d₁ < d₂ < 2d₁) exist and equal 1?

STATUS: SOLVED (YES) by Maier-Tenenbaum 1984
Prize: $250 (reportedly $650 paid)

KEY RESULTS:
1. Density equals 1 for any c > 1 (not just c = 2)
2. Threshold β* = log 3 - 1 for refined version
3. β < β* ⟹ density 1 (Maier-Tenenbaum)
4. β > β* ⟹ density 0 (Erdős-Hall)

KEY INSIGHTS:
1. Most integers have "clustered" divisors
2. Phase transition at β* = log 3 - 1 ≈ 0.0986
3. Erdős's original 1964 proof was flawed but conjecture correct
4. Probabilistic number theory essential for proof

A beautiful result connecting divisor theory and density.
-/
theorem erdos_144_status :
    -- The main conjecture is proven
    erdos_144_conjecture ∧
    -- The strong version for all c > 1 is also proven
    (∀ c > 1, erdos_144_strong_conjecture c) := by
  constructor
  · exact maier_tenenbaum_theorem
  · intro c hc
    exact maier_tenenbaum_strong c

/--
**Problem resolved:**
Erdős Problem #144 was solved affirmatively by Maier-Tenenbaum.
-/
theorem erdos_144_solved : True := trivial

end Erdos144
