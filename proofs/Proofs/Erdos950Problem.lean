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

Reference: [Er77c]
Source: https://erdosproblems.com/950

Adapted from erdosproblems.com (Apache 2.0 License)
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

/-
## Part 1: The Function f(n)

Definition of f(n) = ∑_{p<n} 1/(n-p) and its real-valued variant.
-/

/-- The finite set of all primes p with p < n. -/
def primesLessThan (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter Nat.Prime

/-- f(n) = ∑_{p<n} 1/(n-p) sums the reciprocals of distances from n
    to all primes below n. Nearby primes contribute more than distant ones. -/
noncomputable def f (n : ℕ) : ℝ :=
  ∑ p ∈ primesLessThan n, (1 : ℝ) / (n - p : ℕ)

/-- fReal(x) extends f to real arguments using the floor function. -/
noncomputable def fReal (n : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range ⌊n⌋₊).filter Nat.Prime, 1 / (n - p)

/-
## Part 2: The Three Questions

Erdős Problem #950 asks three specific questions about the behavior of f(n).
-/

/-- Question 1 (OPEN): Is lim inf f(n) = 1?
    This asks whether f(n) can approach 1 from below infinitely often.
    Since f(n) averages to 1, the lim inf is at most 1. -/
def question1 : Prop :=
  Filter.liminf (fun n => f n) atTop = 1

/-- Question 1 stated as a conjecture. -/
/-- Question 2 (OPEN): Is f(n) unbounded (lim sup f(n) = ∞)?
    This asks whether f(n) can be arbitrarily large. -/
def question2 : Prop :=
  ∀ M : ℝ, ∃ᶠ n in atTop, M < f n

/-- Question 2 stated as a conjecture. -/
/-- Question 3 (OPEN): Is f(n) = o(log log n)?
    This asks for a universal upper bound: does f(n) grow slower
    than log(log(n))? -/
def question3 : Prop :=
  ∀ᶠ n in atTop, f n < Real.log (Real.log n)

/-- Question 3 stated as a conjecture. -/
/-- Stronger Form of Q3: f(n) = o(log log n).
    The precise asymptotic version: f(n)/log(log(n)) → 0. -/
def fLittleO : Prop :=
  Tendsto (fun n => f n / Real.log (Real.log n)) atTop (nhds 0)

/-- The strong form of Question 3. -/
/-
## Part 3: Known Results (de Bruijn–Erdős–Turán)

The average behavior of f(n) is well understood.
-/

/-- **de Bruijn–Erdős–Turán: ∑_{n<x} f(n) ~ x**
    The sum of f(n) over n < x grows linearly with x,
    meaning f(n) averages to 1. -/
axiom de_bruijn_erdos_turan_sum :
    Tendsto (fun x => (∑ n ∈ Finset.range x, f n) / x) atTop (nhds 1)

/-- **de Bruijn–Erdős–Turán: ∑_{n<x} f(n)² ~ x**
    The sum of squared values also grows linearly,
    indicating f(n) concentrates near 1 on average. -/
axiom de_bruijn_erdos_turan_sum_sq :
    Tendsto (fun x => (∑ n ∈ Finset.range x, (f n)^2) / x) atTop (nhds 1)

/-- Direct consequence of de_bruijn_erdos_turan_sum. -/
lemma f_average_one :
    Tendsto (fun x => (∑ n ∈ Finset.range x, f n) / x) atTop (nhds 1) :=
  de_bruijn_erdos_turan_sum

/-
## Part 4: Basic Properties

Elementary properties of f(n).
-/

/-- f(n) ≥ 0 for all n, since each term 1/(n-p) is nonneg
    (p < n implies n - p > 0). -/
lemma f_nonneg (n : ℕ) : f n ≥ 0 := by
  unfold f
  apply Finset.sum_nonneg
  intro p _
  simp only [one_div, inv_nonneg]
  exact Nat.cast_nonneg _

/-- f(2) = 0 since there are no primes < 2. -/
lemma f_two : f 2 = 0 := by
  unfold f primesLessThan
  have h : (Finset.range 2).filter Nat.Prime = ∅ := by
    ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
    intro ⟨hp_lt, hp_prime⟩; interval_cases p <;> simp_all [Nat.Prime]
  rw [h, Finset.sum_empty]

/-- f(3) = 1 since 2 is the only prime < 3, and 1/(3−2) = 1. -/
theorem f_three : f 3 = 1 := by
  unfold f primesLessThan
  have h : (Finset.range 3).filter Nat.Prime = {2} := by
    ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · intro ⟨hp_lt, hp_prime⟩; interval_cases p <;> simp_all [Nat.Prime]
    · intro h; subst h; exact ⟨by omega, by decide⟩
  rw [h, Finset.sum_singleton]; norm_num

/-- f(4) = 3/2 since primes < 4 are 2, 3 with distances 2, 1. -/
theorem f_four : f 4 = 3 / 2 := by
  unfold f primesLessThan
  have h : (Finset.range 4).filter Nat.Prime = {2, 3} := by
    ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro ⟨hp_lt, hp_prime⟩; interval_cases p <;> simp_all [Nat.Prime]
    · intro h; rcases h with rfl | rfl <;> exact ⟨by omega, by decide⟩
  rw [h, Finset.sum_pair (by omega : (2 : ℕ) ≠ 3)]; norm_num

/-
## Part 5: Weaker Conjecture and Connections
-/

/-- π(n) = number of primes ≤ n (as a real number). -/
noncomputable def primeCountingFunction (n : ℕ) : ℝ :=
  (primesLessThan (n + 1)).card

/-- **Erdős's Weaker Conjecture**: For every ε > 0, large x has some y < x
    with π(x) < π(y) + ε · π(x−y).
    This is 'perhaps not quite inaccessible' according to Erdős. -/
def weakerConjecture : Prop :=
  ∀ ε > 0, ∀ᶠ x in atTop, ∃ y : ℕ, y < x ∧
    primeCountingFunction x < primeCountingFunction y + ε * primeCountingFunction (x - y)

/-- If π(x) < π(y) + O((x-y)/log x) for all y < x - (log x)^C for some C > 0,
    then f(n) ≪ log log log n. This is a conditional bound on f(n). -/
/-
## Part 6: Connection to Prime Distribution
-/

/-- The gap between successive primes near n: min distance from n to the next prime. -/
noncomputable def maxPrimeGapBelow (n : ℕ) : ℕ :=
  if h : (primesLessThan n).Nonempty then
    n - (primesLessThan n).max' h
  else 0

/-- Having primes in [n−k, n) guarantees f(n) ≥ 1/k.
    Proof: some prime p has distance n-p ≤ k, so 1/(n-p) ≥ 1/k. -/
theorem dense_primes_increase_f (n k : ℕ) (_hk : k > 0) :
    (primesLessThan n ∩ Finset.Ico (n - k) n).card > 0 →
    f n ≥ 1 / k := by
  intro hcard
  have hne : (primesLessThan n ∩ Finset.Ico (n - k) n).Nonempty :=
    Finset.card_pos.mp hcard
  obtain ⟨p, hp⟩ := hne
  simp only [Finset.mem_inter, Finset.mem_Ico] at hp
  obtain ⟨hp_primes, hnk_le_p, hp_lt_n⟩ := hp
  -- p ∈ primesLessThan n, n - k ≤ p, p < n
  have hnp_pos : (0 : ℝ) < ↑(n - p) := by exact_mod_cast Nat.sub_pos_of_lt hp_lt_n
  have hnp_le_k : (n - p : ℕ) ≤ k := by omega
  unfold f
  calc (1 : ℝ) / ↑k
      ≤ 1 / ↑(n - p) := by
        apply one_div_le_one_div_of_le hnp_pos
        exact_mod_cast hnp_le_k
    _ ≤ ∑ q ∈ primesLessThan n, 1 / ↑(n - q) := by
        apply Finset.single_le_sum (fun q _ => div_nonneg one_pos.le (Nat.cast_nonneg _)) hp_primes

/-- The existence of c > 0 with ≫ n^c/log n primes in [n, n+n^c]
    implies lim inf f(n) > 0 (Erdős's observation). -/
/-- Erdős could not prove ∑_{p<x} f(p)² ~ π(x), where the sum is
    restricted to prime arguments. This remains open. -/
/-
## Part 7: Summary
-/

/-- Erdős Problem #950: Summary of known results. -/
theorem erdos_950_summary :
    -- de Bruijn–Erdős–Turán sum asymptotics
    (Tendsto (fun x => (∑ n ∈ Finset.range x, f n) / x) atTop (nhds 1)) ∧
    -- de Bruijn–Erdős–Turán sum of squares
    (Tendsto (fun x => (∑ n ∈ Finset.range x, (f n)^2) / x) atTop (nhds 1)) :=
  ⟨de_bruijn_erdos_turan_sum, de_bruijn_erdos_turan_sum_sq⟩

end Erdos950
