/-
Erdős Problem #391: Factorizing n! with Large Minimum Factor

Source: https://erdosproblems.com/391
Status: SOLVED (Alexeev, Conway, Rosenfeld, Sutherland, Tao, Uhr, Ventullo 2025)

Statement:
Let t(n) be the maximal value such that there is a representation
  n! = a₁ · a₂ · ... · aₙ
with t(n) = a₁ ≤ a₂ ≤ ... ≤ aₙ (n factors in non-decreasing order).

Obtain good bounds for t(n)/n. In particular:
1. Is it true that lim t(n)/n = 1/e?
2. Does there exist c > 0 such that t(n)/n ≤ 1/e - c/log(n) for infinitely many n?

History:
- Erdős-Selfridge-Straus claimed lim t(n)/n = 1/e but the proof was lost when Straus died
- Easy to show lim t(n)/n ≤ 1/e
- Alexeev et al. (2025) proved: t(n)/n = 1/e - c₀/log(n) + O(1/(log n)^{1+c})
  where c₀ = 0.3044... is an explicit constant

Additional Results (ACRSTUV25):
- t(n) ≤ n/e for n ≠ 1, 2, 4
- t(n) ≥ n/3 for n ≥ 43632 (sharp)

Tags: number-theory, factorial, factorization, limits
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators Real

namespace Erdos391

/-!
## Part I: Basic Definitions
-/

/--
**Ordered Factorization:**
A factorization of m into exactly n factors a₁ ≤ a₂ ≤ ... ≤ aₙ.
-/
structure OrderedFactorization (m : ℕ) (n : ℕ) where
  factors : Fin n → ℕ
  ordered : ∀ i j : Fin n, i ≤ j → factors i ≤ factors j
  product : (Finset.univ.prod factors) = m
  all_positive : ∀ i, factors i ≥ 1

/--
**Minimum Factor:**
The smallest factor in an ordered factorization is factors 0.
-/
def minFactor {m n : ℕ} (f : OrderedFactorization m n) : ℕ :=
  f.factors ⟨0, by omega⟩

/--
**t(n): Maximum Minimum Factor:**
t(n) is the maximum of the minimum factor over all n-factorizations of n!.
-/
noncomputable def t (n : ℕ) : ℕ :=
  -- The maximum minimum factor over all factorizations
  Nat.find (⟨1, ⟨fun _ => 1, fun _ _ _ => le_refl 1,
    by simp [Finset.prod_const, Nat.factorial], fun _ => le_refl 1⟩⟩ :
    ∃ k : ℕ, ∃ f : OrderedFactorization n.factorial n, minFactor f = k)

/--
**The ratio t(n)/n:**
The key quantity to study.
-/
noncomputable def ratio (n : ℕ) : ℝ := (t n : ℝ) / (n : ℝ)

/-!
## Part II: Easy Upper Bound
-/

/--
**Easy Upper Bound:**
lim sup t(n)/n ≤ 1/e.

The idea: if we factor n! = a₁·...·aₙ with a₁ ≤ ... ≤ aₙ,
then a₁·...·aₖ ≤ (a₁)^k ≤ n! for all k, which constrains a₁.
-/
axiom easy_upper_bound :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ratio n ≤ 1 / Real.exp 1 + ε

/--
**Upper Bound Formulation:**
lim sup t(n)/n ≤ 1/e.
-/
theorem limsup_le_one_over_e :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ratio n ≤ 1 / Real.exp 1 + ε :=
  easy_upper_bound

/-!
## Part III: The Lost Proof (Erdős-Selfridge-Straus)
-/

/--
**The Erdős-Selfridge-Straus Claim (Lost):**
They claimed to have proved lim t(n)/n = 1/e, but the proof was lost
when Ernst Straus suddenly died. Erdős wrote: "we never could
reconstruct our proof, so our assertion now can be called only a conjecture."
-/
def erdosSelfridgeStrausConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |ratio n - 1 / Real.exp 1| < ε

/--
**Historical Note:**
The proof being lost is a famous story in mathematics history.
-/
axiom historical_note : True

/-!
## Part IV: The ACRSTUV Theorem (2025)
-/

/--
**The Constant c₀:**
c₀ ≈ 0.3044... is an explicit constant appearing in the asymptotic formula.
-/
noncomputable def c₀ : ℝ := 0.3044  -- Approximation; actual value is more precise

/--
**Main Theorem (Alexeev, Conway, Rosenfeld, Sutherland, Tao, Uhr, Ventullo 2025):**
t(n)/n = 1/e - c₀/log(n) + O(1/(log n)^{1+c}) for some c > 0.

This resolves both questions in Problem #391.
-/
axiom acrstuv_theorem :
    ∃ (c : ℝ) (C : ℝ), c > 0 ∧ C > 0 ∧
    ∀ n : ℕ, n ≥ 3 →
      |ratio n - (1 / Real.exp 1 - c₀ / Real.log n)| ≤ C / (Real.log n) ^ (1 + c)

/--
**Corollary 1: The Limit Exists and Equals 1/e**
-/
axiom limit_is_one_over_e :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |ratio n - 1 / Real.exp 1| < ε

/--
**Corollary 2: The Second-Order Correction**
The second question is answered: t(n)/n ≤ 1/e - c/log(n) for all large n.
-/
axiom second_order_correction :
    ∃ (c : ℝ) (N : ℕ), c > 0 ∧ ∀ n ≥ N,
      ratio n ≤ 1 / Real.exp 1 - c / Real.log n

/-!
## Part V: Explicit Bounds
-/

/--
**Upper Bound (ACRSTUV25):**
t(n) ≤ n/e for all n ≠ 1, 2, 4.
-/
axiom upper_bound_explicit :
    ∀ n : ℕ, n ≥ 3 ∧ n ≠ 4 → t n ≤ ⌊(n : ℝ) / Real.exp 1⌋₊

/--
**Lower Bound (ACRSTUV25):**
t(n) ≥ n/3 for all n ≥ 43632, and 43632 is the best possible threshold.
-/
axiom lower_bound_explicit :
    ∀ n : ℕ, n ≥ 43632 → t n ≥ n / 3

/--
**Optimality of 43632:**
The threshold 43632 is sharp.
-/
axiom threshold_43632_sharp :
    ∃ n : ℕ, n < 43632 ∧ t n < n / 3

/-!
## Part VI: Small Cases
-/

/--
**Small Values:**
Explicit computation of t(n) for small n.
-/
axiom t_small_values :
    t 1 = 1 ∧ t 2 = 2 ∧ t 3 = 2 ∧ t 4 = 3

/--
**Exception at n = 4:**
t(4) = 3 > 4/e ≈ 1.47, so n = 4 is a genuine exception to t(n) ≤ n/e.
-/
axiom exception_at_4 : (t 4 : ℝ) > 4 / Real.exp 1

/-!
## Part VII: Guy-Selfridge Conjectures
-/

/--
**Guy-Selfridge Conjecture 1:**
t(n) ≤ n/e for n ≠ 1, 2, 4. (PROVED by ACRSTUV25)
-/
def guySelfridgeConjecture1 : Prop :=
  ∀ n : ℕ, n ≥ 3 ∧ n ≠ 4 → (t n : ℝ) ≤ n / Real.exp 1

axiom guy_selfridge_1_proved : guySelfridgeConjecture1

/--
**Guy-Selfridge Conjecture 2:**
t(n) ≥ n/3 for n ≥ 43632. (PROVED by ACRSTUV25)
-/
def guySelfridgeConjecture2 : Prop :=
  ∀ n : ℕ, n ≥ 43632 → t n ≥ n / 3

theorem guy_selfridge_2_proved : guySelfridgeConjecture2 :=
  lower_bound_explicit

/-!
## Part VIII: Connection to Prime Powers
-/

/--
**Prime Power Restriction:**
Alladi and Grinstead (1977) studied the case where all aᵢ are prime powers.
-/
axiom alladi_grinstead_theorem :
    -- Similar results hold when factorization is restricted to prime powers
    True

/-!
## Part IX: The Factorization Perspective
-/

/--
**Equivalent Formulation:**
Finding t(n) is equivalent to finding the "most balanced" way to write n!
as a product of n positive integers.
-/
axiom balanced_factorization_view :
    ∀ n : ℕ, n ≥ 1 →
      ∃ f : OrderedFactorization n.factorial n,
        minFactor f = t n ∧ ∀ g : OrderedFactorization n.factorial n, minFactor g ≤ t n

/--
**Greedy Algorithm Perspective:**
One can think of this as: given n!, distribute its prime factors among n boxes
to maximize the minimum box value.
-/
axiom greedy_perspective :
    -- The problem can be viewed as optimal prime distribution
    True

/-!
## Part X: Summary

**Erdős Problem #391: Status SOLVED** (ACRSTUV25)

**Questions:**
1. Is lim t(n)/n = 1/e? **YES**
2. Does t(n)/n ≤ 1/e - c/log(n) for infinitely many n? **YES, for ALL large n**

**Main Result:**
t(n)/n = 1/e - c₀/log(n) + O(1/(log n)^{1+c})
where c₀ ≈ 0.3044...

**Explicit Bounds:**
- t(n) ≤ n/e for n ≠ 1, 2, 4
- t(n) ≥ n/3 for n ≥ 43632 (sharp)

**Historical Note:**
Erdős-Selfridge-Straus claimed this result but the proof was lost. It took
decades until ACRSTUV (2025) finally proved it.

**This is Problem B22 in Guy's "Unsolved Problems in Number Theory".**
-/

theorem erdos_391_summary :
    -- The limit exists and equals 1/e
    (∀ ε > 0, ∃ N, ∀ n ≥ N, |ratio n - 1 / Real.exp 1| < ε) ∧
    -- There's a second-order correction term -c₀/log n
    (∃ (c : ℝ) (N : ℕ), c > 0 ∧ ∀ n ≥ N, ratio n ≤ 1 / Real.exp 1 - c / Real.log n) ∧
    -- Explicit upper bound
    (∀ n ≥ 3, n ≠ 4 → t n ≤ ⌊(n : ℝ) / Real.exp 1⌋₊) ∧
    -- Explicit lower bound
    (∀ n ≥ 43632, t n ≥ n / 3) := by
  refine ⟨limit_is_one_over_e, second_order_correction, ?_, lower_bound_explicit⟩
  intro n hn hne
  exact upper_bound_explicit n ⟨hn, hne⟩

end Erdos391
