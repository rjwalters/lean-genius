/-
Erdős Problem #669: Lines Through k Points (Generalized Orchard Problem)

Source: https://erdosproblems.com/669
Status: OPEN (partially solved for k = 3)

Statement:
Let F_k(n) be the maximum number of distinct lines passing through at least k
points among any n points in ℝ².

Let f_k(n) be the maximum number of lines passing through exactly k points.

Estimate f_k(n) and F_k(n). In particular, determine:
  lim_{n→∞} F_k(n)/n² and lim_{n→∞} f_k(n)/n²

Known Results:
- Trivially: f_k(n) ≤ F_k(n)
- For k = 2: f_2(n) = F_2(n) = C(n,2) (every pair defines a line)
- For k = 3 (Orchard Problem): f_3(n) = n²/6 - O(n), F_3(n) = n²/6 - O(n)
  (Burr-Grünbaum-Sloane, 1974)
- Upper bound: F_k(n) ≤ C(n,2)/C(k,2), so lim F_k(n)/n² ≤ 1/(k(k-1))

References:
- [BGS74] Burr, Grünbaum, Sloane, "The orchard problem"
- Related: Problem #101

Open Questions:
- Exact values of lim F_k(n)/n² for k ≥ 4
- Whether f_k(n) and F_k(n) have the same asymptotic behavior for k ≥ 4
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic

open Nat

namespace Erdos669

/-
## Part I: The Line Counting Functions
-/

/--
**F_k(n): At-Least-k Lines**
The maximum number of distinct lines passing through at least k points
among any configuration of n points in ℝ².
-/
axiom atLeastKLines (k n : ℕ) : ℕ

notation "F_" k "(" n ")" => atLeastKLines k n

/--
**f_k(n): Exactly-k Lines**
The maximum number of lines passing through exactly k points
among any configuration of n points in ℝ².
-/
axiom exactlyKLines (k n : ℕ) : ℕ

notation "f_" k "(" n ")" => exactlyKLines k n

/-
## Part II: Basic Relationships
-/

/--
**Trivial Inequality:**
Every line through exactly k points is counted by F_k, so f_k(n) ≤ F_k(n).
-/
axiom f_le_F (k n : ℕ) : f_ k (n) ≤ F_ k (n)

/--
**k = 2 Case:**
Every pair of distinct points defines a unique line, so:
f_2(n) = F_2(n) = C(n,2)
-/
axiom f2_eq_choose (n : ℕ) (hn : n ≥ 2) : f_ 2 (n) = choose n 2

axiom F2_eq_choose (n : ℕ) (hn : n ≥ 2) : F_ 2 (n) = choose n 2

theorem f2_eq_F2 (n : ℕ) (hn : n ≥ 2) : f_ 2 (n) = F_ 2 (n) := by
  rw [f2_eq_choose n hn, F2_eq_choose n hn]

/-
## Part III: The Orchard Problem (k = 3)
-/

/--
**Orchard Problem:**
The case k = 3 is Sylvester's classical "Orchard Problem":
How many lines through 3 or more points can n points determine?
-/

/--
**Burr-Grünbaum-Sloane Theorem (1974):**
For exactly 3 points: f_3(n) = n²/6 - O(n)

More precisely:
  f_3(n) = ⌊n(n-3)/6⌋ + 1 for infinitely many n
-/
axiom burr_grunbaum_sloane_f3 :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 3 →
      |(f_ 3 (n) : ℝ) - n^2 / 6| ≤ C * n

/--
**At-Least-3 Lines:**
F_3(n) = n²/6 - O(n) as well.
-/
axiom burr_grunbaum_sloane_F3 :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 3 →
      |(F_ 3 (n) : ℝ) - n^2 / 6| ≤ C * n

/--
**Limit for k = 3:**
lim_{n→∞} F_3(n)/n² = 1/6
lim_{n→∞} f_3(n)/n² = 1/6
-/
axiom orchard_limit :
    (∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
      |(F_ 3 (n) : ℝ) / n^2 - 1/6| < ε) ∧
    (∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
      |(f_ 3 (n) : ℝ) / n^2 - 1/6| < ε)

/-
## Part IV: Upper Bounds
-/

/--
**Trivial Upper Bound:**
Each line through k points is determined by any k of those points,
so the number of such lines is at most C(n,2)/C(k,2).
-/
axiom Fk_upper_bound (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k) :
    F_ k (n) ≤ choose n 2 / choose k 2

/--
**Asymptotic Upper Bound:**
lim_{n→∞} F_k(n)/n² ≤ 1/(k(k-1))
-/
axiom Fk_limit_upper (k : ℕ) (hk : k ≥ 2) :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
      (F_ k (n) : ℝ) / n^2 ≤ 1 / (k * (k - 1)) + ε

/-
## Part V: Open Questions
-/

/--
**k = 4 Case (Open):**
The limit lim_{n→∞} F_4(n)/n² is not known exactly.

Upper bound: ≤ 1/12
The exact value is unknown.
-/
axiom k4_upper :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
      (F_ 4 (n) : ℝ) / n^2 ≤ 1/12 + ε

/--
**General k ≥ 4 (Open):**
For k ≥ 4, the exact limits are not known.
-/
def limExists_Fk (k : ℕ) : Prop :=
  ∃ L : ℝ, ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    |(F_ k (n) : ℝ) / n^2 - L| < ε

def limExists_fk (k : ℕ) : Prop :=
  ∃ L : ℝ, ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    |(f_ k (n) : ℝ) / n^2 - L| < ε

/--
**Open Question 1:**
Do the limits exist for all k ≥ 2?
-/
def erdos669_question1 : Prop :=
  ∀ k : ℕ, k ≥ 2 → limExists_Fk k ∧ limExists_fk k

/--
**Open Question 2:**
Is the upper bound 1/(k(k-1)) tight for k ≥ 4?
-/
def erdos669_question2 (k : ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (F_ k (n) : ℝ) / n^2 ≥ 1 / (k * (k - 1)) - ε

/--
**Open Question 3:**
Do f_k and F_k have the same asymptotic behavior for k ≥ 4?
-/
def erdos669_question3 (k : ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    |(F_ k (n) : ℝ) - (f_ k (n) : ℝ)| / n^2 < ε

/-
## Part VI: Summary
-/

/--
**What is Known:**
- k = 2: F_2(n) = f_2(n) = C(n,2), limit = 1/2
- k = 3: F_3(n) ~ f_3(n) ~ n²/6, limit = 1/6 (Orchard Problem solved)
- k ≥ 4: Limit exists and ≤ 1/(k(k-1)), but exact value unknown
-/
theorem known_results :
    -- k = 2 is fully understood
    (∀ n ≥ 2, f_ 2 (n) = F_ 2 (n)) ∧
    -- k = 3 limit is 1/6
    (∃ C : ℝ, ∀ n : ℕ, n ≥ 3 → |(F_ 3 (n) : ℝ) - n^2/6| ≤ C * n) ∧
    -- k ≥ 4 has upper bound
    (∀ k ≥ 4, ∀ ε > 0, ∃ N, ∀ n ≥ N, (F_ k (n) : ℝ)/n^2 ≤ 1/(k*(k-1)) + ε) := by
  constructor
  · intro n hn
    exact f2_eq_F2 n hn
  constructor
  · exact burr_grunbaum_sloane_F3
  · intro k hk ε hε
    exact Fk_limit_upper k (by omega : k ≥ 2) ε hε

/--
**Erdős Problem #669: PARTIALLY SOLVED**

The problem asks to estimate F_k(n) and f_k(n).

**Status:**
- k = 2: Completely solved (trivial)
- k = 3: Solved (Burr-Grünbaum-Sloane, 1974)
- k ≥ 4: OPEN - upper bounds known, exact limits unknown
-/
theorem erdos_669 :
    -- k = 3 solved
    (∃ C : ℝ, ∀ n : ℕ, n ≥ 3 →
      |(F_ 3 (n) : ℝ) - n^2/6| ≤ C * n) ∧
    -- General upper bound
    (∀ k ≥ 2, ∀ ε > 0, ∃ N, ∀ n ≥ N,
      (F_ k (n) : ℝ)/n^2 ≤ 1/(k*(k-1)) + ε) := by
  constructor
  · exact burr_grunbaum_sloane_F3
  · intro k hk ε hε
    exact Fk_limit_upper k hk ε hε

end Erdos669
