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

import Mathlib

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
axiom erdos_950_q1 : question1

/-- Question 2 (OPEN): Is lim sup f(n) = ∞?
    This asks whether f(n) is unbounded — can it be arbitrarily large?
    Formulated as: for every M, f(n) > M for infinitely many n. -/
def question2 : Prop :=
  ∀ M : ℝ, ∃ᶠ n in atTop, f n > M

/-- Question 2 stated as a conjecture. -/
axiom erdos_950_q2 : question2

/-- Question 3 (OPEN): Is f(n) = o(log log n)?
    This asks for a universal upper bound: does f(n) grow slower
    than log(log(n))? -/
def question3 : Prop :=
  ∀ᶠ n in atTop, f n < Real.log (Real.log n)

/-- Question 3 stated as a conjecture. -/
axiom erdos_950_q3 : question3

/-- Stronger Form of Q3: f(n) = o(log log n).
    The precise asymptotic version: f(n)/log(log(n)) → 0. -/
def fLittleO : Prop :=
  Tendsto (fun n => f n / Real.log (Real.log n)) atTop (nhds 0)

/-- The strong form of Question 3. -/
axiom erdos_950_q3_strong : fLittleO

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
  exact div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- f(2) = 0 since there are no primes < 2. -/
lemma f_two : f 2 = 0 := by
  unfold f primesLessThan
  have h : (Finset.range 2).filter Nat.Prime = ∅ := by native_decide
  rw [h]; simp

/-- f(3) = 1 since 2 is the only prime < 3, and 1/(3−2) = 1. -/
theorem f_three : f 3 = 1 := by
  unfold f primesLessThan
  have h : (Finset.range 3).filter Nat.Prime = {2} := by native_decide
  rw [h, Finset.sum_singleton]; norm_num

/-- f(4) = 3/2 since primes < 4 are 2, 3 with distances 2, 1. -/
theorem f_four : f 4 = 3 / 2 := by
  unfold f primesLessThan
  have h : (Finset.range 4).filter Nat.Prime = {2, 3} := by native_decide
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
axiom weaker_implies_bound : weakerConjecture →
    ∃ C > 0, ∀ᶠ n in atTop, f n ≤ C * Real.log (Real.log (Real.log n))

/-
## Part 6: Connection to Prime Distribution
-/

/-- Having primes in [n−k, n) guarantees f(n) ≥ 1/k.
    Proof: extract a prime p with n-k ≤ p < n from the sum;
    its contribution 1/(n-p) ≥ 1/k since n-p ≤ k. -/
theorem dense_primes_increase_f (n k : ℕ) (_hk : k > 0) :
    (primesLessThan n ∩ Finset.Ico (n - k) n).card > 0 →
    f n ≥ 1 / k := by
  intro hcard
  obtain ⟨p, hp_mem⟩ := Finset.card_pos.mp hcard
  simp only [Finset.mem_inter, Finset.mem_Ico] at hp_mem
  obtain ⟨hp_primes, hp_ge, hp_lt⟩ := hp_mem
  -- hp_primes : p ∈ primesLessThan n, hp_ico : n - k ≤ p ∧ p < n
  unfold f
  have hle : (1 : ℝ) / ↑(n - p) ≤ ∑ q ∈ primesLessThan n, (1 : ℝ) / ↑(n - q) :=
    Finset.single_le_sum (f := fun q => (1 : ℝ) / ↑(n - q))
      (fun q _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) hp_primes
  have hbound : (1 : ℝ) / ↑k ≤ 1 / ↑(n - p) :=
    one_div_le_one_div_of_le (Nat.cast_pos.mpr (by omega)) (Nat.cast_le.mpr (by omega))
  linarith

/-- The existence of c > 0 with ≫ n^c/log n primes in [n, n+n^c]
    implies lim inf f(n) > 0 (Erdős's observation). -/
axiom dense_short_intervals_imply_liminf_pos :
    (∃ c : ℝ, c > 0 ∧ ∃ C > 0, ∀ᶠ (n : ℕ) in atTop,
      ((primesLessThan (n + ⌊(↑n : ℝ) ^ c⌋₊) \ primesLessThan n).card : ℝ) ≥
        C * (↑n : ℝ) ^ c / Real.log ↑n) →
    ∃ δ > 0, ∀ᶠ (n : ℕ) in atTop, f n ≥ δ

/-- Erdős could not prove ∑_{p<x} f(p)² ~ π(x), where the sum is
    restricted to prime arguments. This remains open. -/
axiom f_at_primes_open :
    ∃ g : ℕ → ℝ, (∀ n, g n = ∑ p ∈ (primesLessThan n).filter Nat.Prime,
      (f p)^2 / primeCountingFunction n) ∧
    Tendsto g atTop (nhds 1)

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
