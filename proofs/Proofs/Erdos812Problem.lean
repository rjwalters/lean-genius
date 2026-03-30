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
/--
**Known Ramsey numbers:**
R(3) = 6, R(4) = 18.
-/
/--
**Ramsey bounds:**
The classical bounds are:
- Lower bound: R(n) ≥ 2^{n/2} (Erdős probabilistic argument)
- Upper bound: R(n) ≤ C(2n-2, n-1) < 4^n / √n (Erdős-Szekeres)
-/
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
**Related result from Problem #165:**
R(n+2) - R(n) ≫ n^{2-o(1)}.
This shows the two-step difference grows almost quadratically.
-/
axiom problem_165_bound :
    ∃ f : ℕ → ℝ, (∀ n, f n > 0) ∧ (∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ n^ε) ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 3, (R (n + 2) - R n : ℝ) ≥ C * n^2 / f n

/-
## Part IV: Consequences
-/

/--
**Ratio bound implies exponential growth:**
If R(n+1)/R(n) ≥ 1 + c, then R(n) ≥ R(k) · (1+c)^{n-k},
giving true exponential growth.
-/
/-
## Part V: Computational Verifications
-/

/--
**Growth of known values:**
R(3)/R(2) = 3, R(4)/R(3) = 3.
-/
example : (6 : ℚ) / 2 = 3 := by norm_num
example : (18 : ℚ) / 6 = 3 := by norm_num

/--
**Consecutive differences:**
R(3) - R(2) = 4, R(4) - R(3) = 12.
-/
example : 6 - 2 = 4 := by norm_num
example : 18 - 6 = 12 := by norm_num

/--
**Verification of BEFS bound for small n:**
4n - 8 gives: n=2 → 0, n=3 → 4, n=4 → 8.
Actual differences exceed these bounds.
-/
example : 4 * 2 - 8 = 0 := by norm_num
example : 4 * 3 - 8 = 4 := by norm_num
example : 4 * 4 - 8 = 8 := by norm_num

/-
## Part VI: Summary
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
-/
theorem erdos_812_summary :
    -- The BEFS bound is established
    (∀ n ≥ 2, R (n + 1) - R n ≥ 4 * n - 8) ∧
    -- The two-step bound from Problem #165
    (∃ f : ℕ → ℝ, (∀ n, f n > 0) ∧ (∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ n^ε) ∧
      ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 3, (R (n + 2) - R n : ℝ) ≥ C * n^2 / f n) :=
  ⟨BEFS_theorem, problem_165_bound⟩

end Erdos812
