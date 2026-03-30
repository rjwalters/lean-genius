/-
Erdős Problem #262: Irrationality Sequences

Source: https://erdosproblems.com/262
Status: SOLVED

Statement:
Suppose a₁ < a₂ < ... is a sequence of integers such that for all
integer sequences t_n ≥ 1, the sum Σ 1/(t_n · a_n) is irrational.
How slowly can a_n grow?

Answer: a_n must satisfy limsup (log₂ log₂ a_n)/n ≥ 1

Background:
- Example: a_n = 2^{2^n} is an irrationality sequence (Erdős 1975)
- Non-example: a_n = n! is NOT an irrationality sequence
- Necessary: a_n^{1/n} → ∞

Key Results:
- Erdős (1975): 2^{2^n} works
- Hančl (1991): limsup (log₂ log₂ a_n)/n ≥ 1 is necessary
- General condition: If a_n ≪ 2^{2^{n-F(n)}} with Σ 2^{-F(n)} < ∞, not irrationality seq

References:
- Erdős (1975): "Some problems and results on irrationality"
- Hančl (1991): "Expression of real numbers with infinite series"

Tags: irrationality, transcendence, number-theory, infinite-series
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Nat Real

namespace Erdos262

/- ## Part I: Basic Definitions -/

/--
**Strictly Increasing Sequence:**
a₁ < a₂ < a₃ < ...
-/
def IsStrictlyIncreasing (a : ℕ → ℕ) : Prop :=
  ∀ n m : ℕ, n < m → a n < a m

/--
**Positive Integer Sequence:**
t_n ≥ 1 for all n.
-/
def IsPositiveIntSequence (t : ℕ → ℕ) : Prop :=
  ∀ n, t n ≥ 1

/--
**The Weighted Sum:**
Σ_{n=1}^∞ 1/(t_n · a_n)
-/
noncomputable def weightedSum (a t : ℕ → ℕ) : ℝ :=
  ∑' n, (1 : ℝ) / ((t n : ℝ) * (a n : ℝ))

/- ## Part II: Irrationality Sequences -/

/--
**Irrationality Sequence:**
A sequence a_n such that for ALL positive integer sequences t_n,
the sum Σ 1/(t_n · a_n) is irrational.
-/
def IsIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  IsStrictlyIncreasing a ∧
  ∀ t : ℕ → ℕ, IsPositiveIntSequence t → Irrational (weightedSum a t)

/--
**The Main Question:**
How slowly can an irrationality sequence grow?
-/
def mainQuestion : Prop :=
  ∃ f : ℕ → ℕ, IsIrrationalitySequence f ∧
    ∀ g : ℕ → ℕ, IsIrrationalitySequence g →
      ∀ᶠ n in Filter.atTop, f n ≤ g n

/- ## Part III: Examples and Non-Examples -/

/--
**The Double Exponential Sequence:**
a_n = 2^{2^n}
-/
def doubleExp (n : ℕ) : ℕ := 2 ^ (2 ^ n)

/--
**Erdős (1975):**
The sequence a_n = 2^{2^n} is an irrationality sequence.
-/
axiom erdos_1975 : IsIrrationalitySequence doubleExp

/--
**The Factorial Sequence:**
a_n = n!
-/
def factorial_seq (n : ℕ) : ℕ := n.factorial

/--
**n! is NOT an irrationality sequence:**
There exists t_n such that Σ 1/(t_n · n!) is rational.
For example, with t_n = n+1, the series telescopes to a rational sum.
-/
axiom factorial_not_irrationality :
    ¬IsIrrationalitySequence factorial_seq

/- ## Part IV: Necessary Growth Condition -/

/--
**Root Growth:**
If a_n is an irrationality sequence, then a_n^{1/n} → ∞.
-/
/--
**Hančl's Theorem (1991):**
Any irrationality sequence must satisfy:
  limsup_{n→∞} (log₂ log₂ a_n) / n ≥ 1
-/
def hančl_condition (a : ℕ → ℕ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in Filter.atTop,
    Real.log (Real.log (a n)) / Real.log 2 / Real.log 2 / n ≥ 1 - ε

/--
**The Double Exponential Bound:**
For an irrationality sequence, we need roughly a_n ≥ 2^{2^{cn}} for some c > 0.
-/
/- ## Part V: Hančl's General Condition -/

/--
**Hančl's General Criterion:**
If a_n ≪ 2^{2^{n-F(n)}} where F(n) < n and Σ 2^{-F(n)} < ∞,
then a_n is NOT an irrationality sequence.
-/
/--
**Corollary: Slower Growth Fails**
If a_n grows slower than 2^{2^{n(1-ε)}} for some ε > 0, it's not an irrationality sequence.
-/
/- ## Part VI: The Spacing Property -/

/--
**The Spacing Property:**
a_{n+1}/a_n = 2^{2^{n+1}}/2^{2^n} = 2^{2^n(2-1)} = 2^{2^n}
grows super-exponentially. This huge gap between consecutive terms
prevents any choice of t_n from making the sum rational.
-/
/- ## Part VII: Summary -/

/--
**Erdős Problem #262: Summary**

**QUESTION:** How slowly can an irrationality sequence grow?

**ANSWER:** (Hančl 1991)
limsup_{n→∞} (log₂ log₂ a_n) / n ≥ 1 is NECESSARY.

**KNOWN:**
- Example: 2^{2^n} works (Erdős 1975)
- Non-example: n! fails
- Necessary: a_n^{1/n} → ∞
- Sharp: limsup (log log a_n)/n ≥ 1

**KEY INSIGHT:** Irrationality sequences must grow at least as fast
as doubly exponential (approximately 2^{2^n}). Slower growth allows
clever choices of t_n to make the sum rational.
-/
theorem erdos_262_summary :
    -- 2^{2^n} is an irrationality sequence (Erdős)
    IsIrrationalitySequence doubleExp ∧
    -- n! is NOT (counterexample)
    ¬IsIrrationalitySequence factorial_seq :=
  ⟨erdos_1975, factorial_not_irrationality⟩

end Erdos262
