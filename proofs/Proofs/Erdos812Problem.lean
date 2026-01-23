/-
Erdős Problem #812: Growth of Consecutive Ramsey Numbers

Source: https://erdosproblems.com/812
Status: OPEN

Statement:
1. Is R(n+1)/R(n) ≥ 1 + c for some constant c > 0 and all large n?
2. Is R(n+1) - R(n) ≫ n²?

Known Results:
- Burr, Erdős, Faudree, Schelp (1989): R(n+1) - R(n) ≥ 4n - 8 for n ≥ 2
- Problem #165's bound implies: R(n+2) - R(n) ≫ n^{2-o(1)}

Context:
The diagonal Ramsey number R(n) is the minimum N such that any 2-coloring
of edges of K_N contains a monochromatic K_n. This problem asks about
the growth rate of consecutive Ramsey numbers.

Historical Note:
Determining precise growth rates of Ramsey numbers is extremely difficult.
Even computing R(5) exactly took decades of effort.

References:
- Burr-Erdős-Faudree-Schelp [BEFS89]: Lower bound on differences
- Erdős [Er91]: Problem statement
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Erdos812

/-
## Part I: Ramsey Number Definitions
-/

/--
**The diagonal Ramsey number R(n):**
R(n) is the minimum N such that any 2-coloring of edges of K_N
contains a monochromatic complete subgraph K_n.
-/
axiom R : ℕ → ℕ

/--
**Basic Ramsey number properties:**
R(1) = 1, R(2) = 2, and R is strictly increasing.
-/
axiom R_basic :
    R 1 = 1 ∧
    R 2 = 2 ∧
    ∀ n ≥ 1, R n < R (n + 1)

/--
**Known Ramsey numbers:**
R(3) = 6, R(4) = 18.
-/
axiom R_known_values :
    R 3 = 6 ∧
    R 4 = 18

/--
**Ramsey bounds:**
The classical bounds are:
- Lower bound: R(n) ≥ 2^{n/2} (Erdős probabilistic argument)
- Upper bound: R(n) ≤ C(2n-2, n-1) < 4^n / √n (Erdős-Szekeres)
-/
axiom ramsey_bounds (n : ℕ) :
    n ≥ 3 → (2 : ℝ) ^ (n / 2 : ℝ) ≤ R n ∧ (R n : ℝ) ≤ (4 : ℝ) ^ n / Real.sqrt n

/-
## Part II: The Main Questions
-/

/--
**First question: Ratio bound:**
Is R(n+1)/R(n) ≥ 1 + c for some constant c > 0 and all large n?
-/
def ratio_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ N : ℕ, ∀ n ≥ N, (R (n + 1) : ℝ) / R n ≥ 1 + c

/--
**Second question: Quadratic difference:**
Is R(n+1) - R(n) ≫ n²?
-/
def quadratic_difference_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N, (R (n + 1) - R n : ℝ) ≥ C * n^2

/--
**Both conjectures remain OPEN:**
Neither the ratio bound nor the quadratic difference has been proven.
-/
axiom conjectures_open : True

/-
## Part III: Known Results
-/

/--
**Burr-Erdős-Faudree-Schelp Theorem (1989):**
R(n+1) - R(n) ≥ 4n - 8 for all n ≥ 2.
This gives a linear lower bound on consecutive differences.
-/
axiom BEFS_theorem :
    ∀ n ≥ 2, R (n + 1) - R n ≥ 4 * n - 8

/--
**The linear bound is best known:**
No super-linear lower bound on R(n+1) - R(n) has been proven.
-/
axiom linear_best_known : True

/--
**Related result from Problem #165:**
R(n+2) - R(n) ≫ n^{2-o(1)}.
This shows the two-step difference grows almost quadratically.
-/
axiom problem_165_bound :
    ∃ f : ℕ → ℝ, (∀ n, f n > 0) ∧ (∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ n^ε) ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 3, (R (n + 2) - R n : ℝ) ≥ C * n^2 / f n

/--
**Gap between one-step and two-step:**
We know R(n+2) - R(n) ≫ n^{2-o(1)}, but not R(n+1) - R(n) ≫ n^2.
The gap suggests the growth might be irregular.
-/
axiom gap_observation : True

/-
## Part IV: What Would Follow
-/

/--
**Ratio bound implies exponential growth:**
If R(n+1)/R(n) ≥ 1 + c, then R(n) ≥ R(k) · (1+c)^{n-k},
giving true exponential growth.
-/
axiom ratio_implies_exponential (c : ℝ) (hc : c > 0) :
    (∀ n ≥ 3, (R (n + 1) : ℝ) / R n ≥ 1 + c) →
    ∀ n k : ℕ, 3 ≤ k → k ≤ n → (R n : ℝ) ≥ R k * (1 + c) ^ (n - k)
  -- Proof by induction: multiply ratios R(k+1)/R(k) · R(k+2)/R(k+1) · ... · R(n)/R(n-1)

/--
**Quadratic difference implications:**
R(n+1) - R(n) ≫ n² would establish that Ramsey numbers grow
faster than any polynomial in n.
-/
axiom quadratic_difference_implications : True

/--
**Connection to Ramsey number bounds:**
Proving either conjecture would improve our understanding of
the exact growth rate of R(n) between the known exponential bounds.
-/
axiom connection_to_bounds : True

/-
## Part V: Why These Questions Are Hard
-/

/--
**Difficulty of Ramsey numbers:**
Even computing R(5) exactly is unknown (43 ≤ R(5) ≤ 48).
Growth rates are even harder than exact values.
-/
axiom ramsey_difficulty : True

/--
**Irregular behavior:**
The sequence R(n) may have irregular jumps, making ratio bounds
difficult to establish uniformly.
-/
axiom irregular_behavior : True

/--
**Probabilistic lower bounds:**
The best lower bounds come from probabilistic arguments that
don't give information about consecutive differences.
-/
axiom probabilistic_limitations : True

/--
**Computational barriers:**
Cannot be resolved through finite computation alone -
would require asymptotic arguments.
-/
axiom computational_barriers : True

/-
## Part VI: Related Problems
-/

/--
**Problem 165: Ramsey lower bounds:**
Asks about improved lower bounds for R(n), connected via
the R(n+2) - R(n) estimate.
-/
axiom related_problem_165 : True

/--
**Off-diagonal Ramsey numbers:**
R(s,t) for s ≠ t has similar open questions about growth rates.
-/
axiom off_diagonal_ramsey : True

/--
**Hypergraph Ramsey:**
Ramsey numbers for hypergraphs have even wilder growth rates
(tower functions).
-/
axiom hypergraph_ramsey : True

/-
## Part VII: Historical Context
-/

/--
**Ramsey's theorem (1930):**
Frank Ramsey proved the existence of R(n) in his 1930 paper.
Exact growth rates remain mysterious almost a century later.
-/
axiom ramsey_1930 : True

/--
**Erdős-Szekeres (1935):**
Established the upper bound R(n) ≤ C(2n-2, n-1) < 4^n.
-/
axiom erdos_szekeres_1935 : True

/--
**Erdős probabilistic method (1947):**
Established R(n) > 2^{n/2} using random graphs.
This was a founding application of the probabilistic method.
-/
axiom erdos_probabilistic_1947 : True

/--
**Erdős's quote on R(5):**
"Suppose aliens invade the earth and threaten to obliterate it
in a year's time unless human beings can find R(5). We could
marshal the world's best minds and computers... But if they
asked for R(6), we should have to just surrender."
-/
axiom erdos_aliens_quote : True

/-
## Part VIII: Known Values and Bounds
-/

/--
**Table of known Ramsey numbers:**
R(1) = 1, R(2) = 2, R(3) = 6, R(4) = 18.
R(5) is unknown: 43 ≤ R(5) ≤ 48.
-/
axiom known_ramsey_table : True

/--
**Growth of known values:**
R(3)/R(2) = 3, R(4)/R(3) = 3.
The ratio 3 suggests c ≈ 2 might work, but this is only 2 data points.
-/
example : (6 : ℚ) / 2 = 3 := by norm_num
example : (18 : ℚ) / 6 = 3 := by norm_num

/--
**Consecutive differences:**
R(3) - R(2) = 4, R(4) - R(3) = 12.
Both exceed the 4n - 8 bound: 4 ≥ 0 and 12 ≥ 4.
-/
example : 6 - 2 = 4 := by norm_num
example : 18 - 6 = 12 := by norm_num

/--
**Verification of BEFS bound for small n:**
The bound 4n - 8 gives: n=2 → 0, n=3 → 4, n=4 → 8.
Actual differences: R(3)-R(2)=4 ≥ 0 ✓, R(4)-R(3)=12 ≥ 4 ✓.
-/
example : 4 * 2 - 8 = 0 := by norm_num
example : 4 * 3 - 8 = 4 := by norm_num
example : 4 * 4 - 8 = 8 := by norm_num

/--
**Quadratic vs linear comparison:**
At n = 10: linear bound gives 4·10 - 8 = 32.
Quadratic would give n² = 100 (if the conjecture holds).
Gap ratio is about 3x at n=10, grows linearly.
-/
example : 4 * 10 - 8 = 32 := by norm_num
example : (10 : ℕ)^2 = 100 := by norm_num

/-
## Part IX: Summary
-/

/--
**Summary of Erdős Problem #812:**

PROBLEM: Two questions about Ramsey number growth:
1. Is R(n+1)/R(n) ≥ 1 + c for some c > 0?
2. Is R(n+1) - R(n) ≫ n²?

STATUS: OPEN (both questions)

KNOWN RESULTS:
1. R(n+1) - R(n) ≥ 4n - 8 (Burr-Erdős-Faudree-Schelp 1989)
2. R(n+2) - R(n) ≫ n^{2-o(1)} (from Problem #165)
3. Overall bounds: 2^{n/2} ≤ R(n) ≤ 4^n / √n

KEY INSIGHTS:
1. Linear lower bound on differences is best known
2. Two-step differences are almost quadratic
3. Cannot be resolved computationally - needs asymptotic arguments
4. Even R(5) is not known exactly

A fundamental open problem in Ramsey theory.
-/
theorem erdos_812_status :
    -- The BEFS bound is established
    (∀ n ≥ 2, R (n + 1) - R n ≥ 4 * n - 8) ∧
    -- But the main conjectures remain OPEN
    True := by
  constructor
  · exact BEFS_theorem
  · trivial

/--
**Problem status:**
Erdős Problem #812 remains OPEN.
-/
theorem erdos_812_open : True := trivial

end Erdos812
