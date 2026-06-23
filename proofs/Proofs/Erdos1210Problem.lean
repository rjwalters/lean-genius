/-
# Erdős Problem #1210: Pairwise Coprime Weighted Harmonic Sum

Source: https://erdosproblems.com/1210 (T. F. Bloom, accessed 2026-06-13)

## Problem Statement (corrected)

Let A ⊆ [1,n) be a set of integers such that gcd(a,b) = 1 for all distinct
a,b ∈ A (pairwise coprime). Is it true that

  ∑_{a ∈ A} 1/(n - a) ≤ ∑_{p prime, p < n} 1/p + O(1)?

The right-hand side is the Mertens sum ∑_{p<n} 1/p = log log n + O(1); the "+O(1)"
is an additive constant **uniform in n and A**. Formally the conjecture asserts:

  ∃ C, ∀ n, ∀ pairwise-coprime A ⊆ [1,n),  ∑_{a∈A} 1/(n-a) ≤ ∑_{p<n} 1/p + C.

## Status: OPEN

Per the source, this is open and "cannot be resolved with a finite computation."

## Transcription note (why this file was revised)

An earlier formalization transcribed the right-hand side as ∑_{p<n} 1/(n-p)
**and dropped the +O(1) term**, yielding the *exact* inequality
∑_{a∈A} 1/(n-a) ≤ ∑_{p<n} 1/(n-p). That literal statement is FALSE: at n = 5,
A = {4} gives LHS = 1 while ∑_{p<5} 1/(5-p) = 5/6. The refutation is preserved
below (see `naive_statement_fails_at_five`) precisely to document that the
O(1) term is essential — with it, the n=5 discrepancy of 1/6 is absorbed by the
constant and there is no contradiction (`corrected_statement_consistent_at_five`).

In [Er80] Erdős notes he "did not state [this] quite correctly" in [Er77c]. The
reformulation he gives there concerns primes in an interval: if
n < q₁ < ⋯ < q_k ≤ m are the primes in (n,m], then
∑ 1/(qᵢ - n) < ∑_{p < m-n} 1/p + O(1). See also problems #460 and #950.

## References

- Erdős (1977), [Er77c, p.64]
- Erdős (1980), [Er80, p.112]
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos1210

open Nat BigOperators

/-
## Definitions
-/

/-- The primes below n: {p : ℕ | p.Prime ∧ p < n}. -/
def primesBelow (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter Nat.Prime

/-- A finset A is pairwise coprime if gcd(a,b) = 1 for all distinct a,b ∈ A. -/
def PairwiseCoprime (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b

/-- A finset A is valid for Erdős 1210: all elements in [1, n). -/
def ValidSubset (n : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a < n

/-- The corrected right-hand side: the sum of prime reciprocals ∑_{p<n} 1/p
    (the Mertens sum ~ log log n). NOTE: this is 1/p, **not** 1/(n-p). -/
noncomputable def primeReciprocalSum (n : ℕ) : ℝ :=
  ∑ p ∈ primesBelow n, (1 : ℝ) / (p : ℝ)

/-
## Basic Properties of Primes
-/

/-- Distinct primes are coprime. -/
theorem primes_coprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Nat.Coprime p q :=
  hp.coprime_iff_not_dvd.mpr fun h =>
    hne ((hq.eq_one_or_self_of_dvd p h).resolve_left hp.one_lt.ne')

/-- The primes below n form a pairwise coprime set. -/
theorem primesBelow_pairwiseCoprime (n : ℕ) : PairwiseCoprime (primesBelow n) := by
  intro a ha b hb hab
  simp only [primesBelow, Finset.mem_filter, Finset.mem_range] at ha hb
  exact primes_coprime ha.2 hb.2 hab

/-- The primes below n form a valid subset for Erdős 1210. -/
theorem primesBelow_valid (n : ℕ) : ValidSubset n (primesBelow n) := by
  intro p hp
  simp only [primesBelow, Finset.mem_filter, Finset.mem_range] at hp
  exact ⟨le_trans (by norm_num) hp.2.two_le, hp.1⟩

/-- 2 ∈ primesBelow n for n ≥ 3, so primesBelow n is nonempty. -/
theorem primesBelow_nonempty {n : ℕ} (hn : 3 ≤ n) : (primesBelow n).Nonempty :=
  ⟨2, by simp only [primesBelow, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, by decide⟩⟩

/-- Any pairwise coprime set has at most one even element (since any two even numbers share factor 2). -/
theorem pairwiseCoprime_at_most_one_even {A : Finset ℕ} (hA : PairwiseCoprime A) :
    (A.filter (fun a => 2 ∣ a)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  by_contra hab
  have hcop := hA a ha.1 b hb.1 hab
  have : 2 ∣ Nat.gcd a b := Nat.dvd_gcd ha.2 hb.2
  simp only [Nat.Coprime] at hcop
  rw [hcop] at this
  exact absurd this (by norm_num)

/-
## The Corrected Right-Hand Side
-/

/-- Each prime reciprocal 1/p is nonneg, so the prime-reciprocal sum is nonneg. -/
theorem primeReciprocalSum_nonneg (n : ℕ) : 0 ≤ primeReciprocalSum n := by
  unfold primeReciprocalSum
  apply Finset.sum_nonneg
  intro p _
  positivity

/-- The prime-reciprocal sum is positive for n ≥ 3 (it contains the term 1/2). -/
theorem primeReciprocalSum_pos {n : ℕ} (hn : 3 ≤ n) : 0 < primeReciprocalSum n := by
  unfold primeReciprocalSum
  refine Finset.sum_pos ?_ (primesBelow_nonempty hn)
  intro p hp
  simp only [primesBelow, Finset.mem_filter, Finset.mem_range] at hp
  exact div_pos one_pos (by exact_mod_cast hp.2.pos)

/-
## The Main Conjecture (Open)

The conjecture is an asymptotic inequality with an additive O(1) constant that
is uniform over both n and the pairwise-coprime set A. We axiomatize it with an
explicit existential constant C — the honest formalization of "+O(1)".
-/

/-- **Erdős Problem 1210 (Open)**. There is an absolute constant C such that for
    every n ≥ 3 and every pairwise coprime A ⊆ {1,…,n-1},

      ∑_{a ∈ A} 1/(n-a) ≤ ∑_{p prime, p < n} 1/p + C.

    Equivalently, the weighted harmonic sum over any pairwise coprime set is
    bounded by the Mertens sum (~ log log n) up to an additive constant. -/
axiom erdos_1210 :
    ∃ C : ℝ, ∀ (n : ℕ), 3 ≤ n → ∀ (A : Finset ℕ),
      ValidSubset n A → PairwiseCoprime A →
      ∑ a ∈ A, (1 : ℝ) / ((n : ℝ) - a) ≤ primeReciprocalSum n + C

/-
## Consequences
-/

/-- Re-statement of the conjecture: a single uniform constant works for all n, A. -/
theorem erdos_1210_uniform_bound :
    ∃ C : ℝ, ∀ (n : ℕ), 3 ≤ n → ∀ (A : Finset ℕ),
      ValidSubset n A → PairwiseCoprime A →
      ∑ a ∈ A, (1 : ℝ) / ((n : ℝ) - a) ≤ primeReciprocalSum n + C :=
  erdos_1210

/-- The empty set has sum 0, trivially bounded by the (nonneg) prime-reciprocal
    sum — this holds unconditionally, with no need for the O(1) constant. -/
theorem erdos_1210_empty (n : ℕ) (hn : 3 ≤ n) :
    (0 : ℝ) ≤ primeReciprocalSum n :=
  le_of_lt (primeReciprocalSum_pos hn)

/-
## Why the O(1) Term Is Essential (machine-checked)

The naive "exact" inequality (constant C = 0, with the further mis-transcription
of the right-hand side as ∑ 1/(n-p)) is FALSE. The minimal witness is n = 5,
A = {4}:

  - 4 ∈ [1, 5), so `ValidSubset 5 {4}` holds; {4} is trivially pairwise coprime.
  - ∑_{a ∈ {4}} 1/(5 - a) = 1/(5-4) = 1.
  - ∑_{p prime, p < 5} 1/p = 1/2 + 1/3 = 5/6   (and ∑ 1/(5-p) = 1/3 + 1/2 = 5/6 too).
  - 1 > 5/6, so the C = 0 statement fails by exactly 1/6.

With the O(1) term any C ≥ 1/6 absorbs this gap, so the corrected conjecture is
not contradicted. The theorems below record both facts.
-/

/-- `primesBelow 5 = {2, 3}` (decidable equality of concrete Finsets). -/
theorem primesBelow_five : primesBelow 5 = ({2, 3} : Finset ℕ) := by
  unfold primesBelow
  decide

/-- The corrected right-hand side at n = 5 equals 5/6 (= 1/2 + 1/3). -/
theorem primeReciprocalSum_five : primeReciprocalSum 5 = 5 / 6 := by
  unfold primeReciprocalSum
  rw [primesBelow_five]
  rw [show ({2, 3} : Finset ℕ) = insert 2 {3} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- `{4}` satisfies the hypotheses of `erdos_1210` at n = 5. -/
theorem singleton_four_valid_at_five :
    ValidSubset 5 ({4} : Finset ℕ) ∧ PairwiseCoprime ({4} : Finset ℕ) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_singleton] at ha
    subst ha
    exact ⟨by norm_num, by norm_num⟩
  · intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    omega

/-- **The naive (C = 0) statement fails at n = 5, A = {4}**: the A-sum (= 1)
    strictly exceeds the prime-reciprocal sum (= 5/6). This is why an additive
    O(1) constant is required in the conjecture. -/
theorem naive_statement_fails_at_five :
    primeReciprocalSum 5 < ∑ a ∈ ({4} : Finset ℕ), (1 : ℝ) / ((5 : ℝ) - a) := by
  rw [primeReciprocalSum_five, Finset.sum_singleton]
  push_cast
  norm_num

/-- **The corrected (O(1)) statement is consistent at n = 5, A = {4}**: for any
    constant C ≥ 1/6, the A-sum is bounded by the prime-reciprocal sum plus C.
    The n = 5 case therefore imposes only the lower bound C ≥ 1/6 — no
    contradiction with the conjecture. -/
theorem corrected_statement_consistent_at_five (C : ℝ) (hC : 1 / 6 ≤ C) :
    ∑ a ∈ ({4} : Finset ℕ), (1 : ℝ) / ((5 : ℝ) - a) ≤ primeReciprocalSum 5 + C := by
  rw [primeReciprocalSum_five, Finset.sum_singleton]
  push_cast
  linarith

end Erdos1210
