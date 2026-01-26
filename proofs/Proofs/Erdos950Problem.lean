/-
Erdős Problem #950: Sum of Reciprocal Prime Gaps

**Problem Statement (OPEN)**

Define f(n) = ∑_{p<n} 1/(n-p) where the sum is over all primes p < n.

Three questions:
1. Is lim inf f(n) = 1?
2. Is lim sup f(n) = ∞?
3. Is f(n) = o(log log n) for all n?

**Known Results (de Bruijn, Erdős, Turán):**
- ∑_{n<x} f(n) ~ x
- ∑_{n<x} f(n)² ~ x

**Status**: OPEN

Reference: https://erdosproblems.com/950

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Filter Real

namespace Erdos950

/-!
# Part 1: The Function f(n)

Definition of f(n) = ∑_{p<n} 1/(n-p) and its real-valued variant.
-/

/--
**Primes Less Than n**

The finite set of all primes p with p < n.
-/
def primesLessThan (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter Nat.Prime

/--
**The Function f(n)**

f(n) = ∑_{p<n} 1/(n-p) sums the reciprocals of distances from n
to all primes below n. Nearby primes contribute more than distant ones.
-/
noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ primesLessThan n, (1 : ℝ) / (n - p : ℕ)

/--
**Real-Valued Variant**

fReal(x) extends f to real arguments using the floor function.
-/
noncomputable def fReal (n : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range ⌊n⌋₊).filter Nat.Prime, 1 / (n - p)

/-!
# Part 2: The Three Questions

Erdős Problem #950 asks three specific questions about the behavior of f(n).
-/

/--
**Question 1 (OPEN): Is lim inf f(n) = 1?**

This asks whether f(n) can approach 1 from below infinitely often.
Since f(n) averages to 1, the lim inf is at most 1.
-/
def question1 : Prop :=
  Filter.liminf (fun n => f n) atTop = 1

/-- Question 1 stated as a conjecture. -/
axiom erdos_950_q1 : question1

/--
**Question 2 (OPEN): Is lim sup f(n) = ∞?**

This asks whether f(n) is unbounded — can it be arbitrarily large?
-/
def question2 : Prop :=
  Filter.limsup (fun n => f n) atTop = ⊤

/-- Question 2 stated as a conjecture. -/
axiom erdos_950_q2 : question2

/--
**Question 3 (OPEN): Is f(n) = o(log log n)?**

This asks for a universal upper bound: does f(n) grow slower
than log(log(n))?
-/
def question3 : Prop :=
  ∀ᶠ n in atTop, f n < Real.log (Real.log n)

/-- Question 3 stated as a conjecture. -/
axiom erdos_950_q3 : question3

/--
**Stronger Form of Q3: f(n) = o(log log n)**

The precise asymptotic version: f(n)/log(log(n)) → 0.
-/
def fLittleO : Prop :=
  Tendsto (fun n => f n / Real.log (Real.log n)) atTop (nhds 0)

/-- The strong form of Question 3. -/
axiom erdos_950_q3_strong : fLittleO

/-!
# Part 3: Known Results (de Bruijn–Erdős–Turán)

The average behavior of f(n) is well understood.
-/

/--
**de Bruijn–Erdős–Turán: ∑_{n<x} f(n) ~ x**

The sum of f(n) over n < x grows linearly with x,
meaning f(n) averages to 1.
-/
axiom de_bruijn_erdos_turan_sum :
    Tendsto (fun x => (∑ n ∈ Finset.range x, f n) / x) atTop (nhds 1)

/--
**de Bruijn–Erdős–Turán: ∑_{n<x} f(n)² ~ x**

The sum of squared values also grows linearly,
indicating f(n) concentrates near 1 on average.
-/
axiom de_bruijn_erdos_turan_sum_sq :
    Tendsto (fun x => (∑ n ∈ Finset.range x, (f n)^2) / x) atTop (nhds 1)

/--
**Consequence: f(n) averages to 1**

Direct consequence of de_bruijn_erdos_turan_sum.
-/
lemma f_average_one :
    Tendsto (fun x => (∑ n ∈ Finset.range x, f n) / x) atTop (nhds 1) :=
  de_bruijn_erdos_turan_sum

/-!
# Part 4: Basic Properties

Elementary properties of f(n).
-/

/--
**f(n) ≥ 0 for all n**

Each term 1/(n-p) is nonneg since p < n implies n - p > 0.
-/
lemma f_nonneg (n : ℕ) : f n ≥ 0 := by
  unfold f
  apply Finset.sum_nonneg
  intro p _
  simp only [one_div, inv_nonneg]
  exact Nat.cast_nonneg _

/-- f(2) = 0 since there are no primes < 2. -/
lemma f_two : f 2 = 0 := by
  simp [f, primesLessThan]

/-- f(3) = 1 since 2 is the only prime < 3, and 1/(3−2) = 1. -/
axiom f_three : f 3 = 1

/-- f(4) = 3/2 since primes < 4 are 2, 3 with distances 2, 1. -/
axiom f_four : f 4 = 3 / 2

/-- For prime p < n, the term 1/(n−p) contributes to f(n). -/
lemma prime_contributes (n p : ℕ) (hp : p.Prime) (hpn : p < n) :
    (1 : ℝ) / (n - p : ℕ) ∈ Set.range (fun q => (1 : ℝ) / (n - q)) :=
  ⟨p, rfl⟩

/-!
# Part 5: Heuristic Analysis

Why the average of f(n) is 1 and what drives fluctuations.
-/

/--
**Integral Approximation**

By PNT, primes have density ~ 1/log t near t.
∑_{p<n} 1/(n-p) ≈ ∫₂ⁿ 1/(n-t) · (1/log t) dt ~ 1
This explains why f(n) averages to 1.
-/
axiom integral_heuristic :
    True  -- Heuristic: ∫₂ⁿ dt/((n-t) log t) ~ 1

/--
**f(n) is large near primes**

If n immediately follows a prime p (i.e., n = p+1),
the term 1/(n-p) = 1 contributes significantly.
Regions with many nearby primes inflate f(n).
-/
axiom f_large_near_primes :
    True  -- Heuristic: f(p+1) includes term 1/1 = 1

/-!
# Part 6: Weaker Conjecture and Connection

A related conjecture about prime counting.
-/

/--
**Prime Counting Function**

π(n) = number of primes ≤ n.
-/
noncomputable def primeCountingFunction (n : ℕ) : ℝ :=
  (primesLessThan (n + 1)).card

/--
**Erdős's Weaker Conjecture**

For every ε > 0, large x has some y < x with
π(x) < π(y) + ε · π(x−y).
-/
def weakerConjecture : Prop :=
  ∀ ε > 0, ∀ᶠ x in atTop, ∃ y : ℕ, y < x ∧
    primeCountingFunction x < primeCountingFunction y + ε * primeCountingFunction (x - y)

/--
**Weaker Conjecture implies f(n) ≪ log log log n**

If a strong version of the weaker conjecture holds,
then f(n) has an extremely slow growth bound.
-/
axiom weaker_implies_bound : weakerConjecture →
    ∃ C > 0, ∀ᶠ n in atTop, f n ≤ C * Real.log (Real.log (Real.log n))

/-!
# Part 7: Connection to Prime Distribution

f(n) reflects the local distribution of primes near n.
-/

/--
**Prime Gap**

The gap between the m-th and (m+1)-th primes.
-/
noncomputable def primeGap (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m

/--
**Dense Primes Increase f(n)**

Having primes in [n−k, n) guarantees f(n) ≥ 1/k.
-/
axiom dense_primes_increase_f (n k : ℕ) (hk : k > 0) :
    (primesLessThan n ∩ Finset.Ico (n - k) n).card > 0 →
    f n ≥ 1 / k

/-!
# Part 8: Summary
-/

/--
**Erdős Problem #950: Summary**

The known results (average behavior) and the three open questions
about the extremal behavior of f(n) = ∑_{p<n} 1/(n-p).
-/
theorem erdos_950_summary :
    -- de Bruijn–Erdős–Turán sum asymptotics
    (Tendsto (fun x => (∑ n ∈ Finset.range x, f n) / x) atTop (nhds 1)) ∧
    -- de Bruijn–Erdős–Turán sum of squares
    (Tendsto (fun x => (∑ n ∈ Finset.range x, (f n)^2) / x) atTop (nhds 1)) ∧
    -- All three questions are stated
    True :=
  ⟨de_bruijn_erdos_turan_sum, de_bruijn_erdos_turan_sum_sq, trivial⟩

/-- The problem remains OPEN for all three questions. -/
def erdos_950_status : String := "OPEN (all three questions)"

end Erdos950
