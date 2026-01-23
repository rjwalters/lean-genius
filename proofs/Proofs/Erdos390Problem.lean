/-
  Erdős Problem #390: Factorial Factorization with Large Factors

  Source: https://erdosproblems.com/390
  Status: OPEN

  Problem Statement:
  Let f(n) be the minimal m such that n! = a₁ · a₂ · ... · aₖ
  with n < a₁ < a₂ < ... < aₖ = m.

  Known Result (Erdős-Guy-Selfridge 1982):
    f(n) - 2n ≍ n / log(n)

  Question: Is there a constant c such that
    f(n) - 2n ~ c · n / log(n)?

  Mathematical Background:
  The problem asks about expressing n! as a product of distinct integers
  all strictly greater than n, and finding the minimal maximum factor.

  Key Insight:
  - For small n (like n = 1, 2), this may be impossible
  - For large n, n! is large enough to factor into such products
  - The minimal largest factor is roughly 2n, with a secondary term of n/log(n)

  References:
  - [EGS82] Erdős, Guy, Selfridge: "Another property of 239 and some related questions"
    Congr. Numer. (1982), 243-257

  Tags: number-theory, factorials, erdos-problem
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Erdos390

/-! ## Part I: The Function f(n)

We axiomatize f(n) as the minimal m such that n! can be written as a product
of distinct integers all > n, with largest factor = m.
-/

/-- f(n) is the minimal largest factor in any valid factorization of n!.
    A valid factorization writes n! = a₁ · a₂ · ... · aₖ with n < a₁ < ... < aₖ = m.

    We axiomatize f since the constructive definition requires complex machinery. -/
axiom f : ℕ → ℕ

/-- The function f is only meaningful for sufficiently large n. -/
axiom f_pos (n : ℕ) (hn : n ≥ 3) : f n > 0

/-! ## Part II: Known Bounds

Erdős, Guy, and Selfridge (1982) established:
  f(n) - 2n ≍ n / log(n)

This means there exist positive constants c₁, c₂ such that:
  c₁ · n / log(n) ≤ f(n) - 2n ≤ c₂ · n / log(n)  for large n
-/

/-- Lower bound: f(n) ≥ 2n for n ≥ 1.

    Proof idea: If n! = a₁ · ... · aₖ with all aᵢ > n, and aₖ = m is the largest,
    then the product of factors ≤ m is at most m^k.
    For the product to equal n!, we need m to be at least 2n. -/
axiom f_ge_2n (n : ℕ) (hn : 1 ≤ n) : f n ≥ 2 * n

/-- Upper bound: f(n) ≤ 2n + C · n/log(n) for some constant C.

    This is proved constructively by Erdős-Guy-Selfridge (1982). -/
axiom f_le_upper_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, C > 0 ∧ (f n : ℝ) ≤ 2 * n + C * n / Real.log n

/-- Lower bound: f(n) ≥ 2n + c · n/log(n) for some constant c.

    This shows the secondary term is necessary. -/
axiom f_ge_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : ℝ, c > 0 ∧ (f n : ℝ) ≥ 2 * n + c * n / Real.log n

/-! ## Part III: The Main Conjecture -/

/-- **Erdős Problem #390** (OPEN)

    Is there a constant c such that:
      lim_{n→∞} (f(n) - 2n) · log(n) / n = c

    The known bounds show this ratio is bounded between positive constants,
    but whether a specific limit exists is unknown.

    Note: The formulation uses the ratio (f(n) - 2n) · log(n) / n,
    which should converge to c if the conjecture holds. -/
def erdos_390 : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto (fun n : ℕ => ((f n : ℝ) - 2 * n) * Real.log n / n)
                   Filter.atTop (nhds c)

/-! ## Part IV: Related Observations -/

/-- The asymptotic notation: f(n) - 2n ≍ n / log(n).

    This is equivalent to saying:
    - f(n) - 2n = O(n / log n)  (upper bound)
    - f(n) - 2n = Ω(n / log n)  (lower bound)

    The existence of uniform constants C, c follows from the Erdős-Guy-Selfridge
    analysis. We axiomatize this since deriving uniform bounds from the per-n
    axioms above requires additional machinery. -/
axiom f_asymptotic_equiv :
    ∃ C c : ℝ, C > 0 ∧ c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        c * n / Real.log n ≤ (f n : ℝ) - 2 * n ∧
        (f n : ℝ) - 2 * n ≤ C * n / Real.log n

/-! ## Part V: Summary

**Problem Status**: OPEN

**What we know**:
1. f(n) exists for large n (valid factorizations exist)
2. f(n) ≥ 2n (trivial lower bound)
3. f(n) - 2n ≍ n/log(n) (Erdős-Guy-Selfridge 1982)

**What we don't know**:
- Does the limit lim_{n→∞} (f(n) - 2n) · log(n) / n exist?
- If so, what is its value?

**Formalization provides**:
- Axiomatization of f and its basic properties
- Statement of known bounds
- Formal statement of the conjecture
-/

#check f_ge_2n
#check f_le_upper_bound
#check f_ge_lower_bound
#check erdos_390

end Erdos390
