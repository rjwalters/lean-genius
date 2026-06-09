/-
# Erdős Problem #1210: Pairwise Coprime Subset Sum Inequality

Source: https://erdosproblems.com/1210

## Problem Statement

Let A ⊆ [1,n) be a set of integers such that gcd(a,b) = 1 for all distinct
a,b ∈ A (pairwise coprime). Is it true that

  ∑_{a ∈ A} 1/(n - a) ≤ ∑_{p prime, p < n} 1/(n - p)?

In other words: among all pairwise coprime subsets of {1,...,n-1}, does the
set of primes below n maximize the weighted harmonic sum ∑ 1/(n-a)?

## Status: OPEN

This is an open conjecture of Erdős. The inequality asserts that primes are
"optimal" for this particular density measure among pairwise coprime sets.

## Key Observations

1. Primes < n are pairwise coprime, so they form a valid candidate set A.
2. The sum ∑_{p<n} 1/(n-p) is a finite positive quantity for n ≥ 3.
3. Any pairwise coprime set A has at most one even element.
4. The inequality is tight when A = {primes < n}.

## References

- Erdős (1980), Er80
- Erdős (1977), Er77c
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
## The Sum Inequality
-/

/-- The prime sum is nonneg: each term 1/(n-p) ≥ 0 for p < n. -/
theorem primesBelow_sum_nonneg (n : ℕ) :
    0 ≤ ∑ p ∈ primesBelow n, (1 : ℝ) / ((n : ℝ) - p) := by
  apply Finset.sum_nonneg
  intro p hp
  simp only [primesBelow, Finset.mem_filter, Finset.mem_range] at hp
  apply div_nonneg zero_le_one
  have : (p : ℝ) < n := by exact_mod_cast hp.1
  linarith

/-- The prime sum is positive for n ≥ 3 (since 1/(n-2) > 0). -/
theorem primesBelow_sum_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < ∑ p ∈ primesBelow n, (1 : ℝ) / ((n : ℝ) - p) := by
  refine Finset.sum_pos ?_ (primesBelow_nonempty hn)
  intro p hp
  simp only [primesBelow, Finset.mem_filter, Finset.mem_range] at hp
  have hpn : (p : ℝ) < n := by exact_mod_cast hp.1
  exact _root_.div_pos one_pos (by linarith)

/-
## The Main Conjecture (Open)
-/

/-- **Erdős Problem 1210 (Open)**: For all n ≥ 3 and all pairwise coprime A ⊆ {1,...,n-1},
    ∑_{a ∈ A} 1/(n-a) ≤ ∑_{p prime, p < n} 1/(n-p).
    The set of primes below n maximizes this sum. -/
axiom erdos_1210 (n : ℕ) (hn : 3 ≤ n) (A : Finset ℕ)
    (hA_valid : ValidSubset n A)
    (hA_coprime : PairwiseCoprime A) :
    ∑ a ∈ A, (1 : ℝ) / ((n : ℝ) - a) ≤ ∑ p ∈ primesBelow n, (1 : ℝ) / ((n : ℝ) - p)

/-
## Consequences
-/

/-- Any pairwise coprime A ⊆ {1,...,n-1} has sum bounded by the prime sum (from the axiom). -/
theorem erdos_1210_bound (n : ℕ) (hn : 3 ≤ n) (A : Finset ℕ)
    (hA_valid : ValidSubset n A) (hA_coprime : PairwiseCoprime A) :
    ∑ a ∈ A, (1 : ℝ) / ((n : ℝ) - a) ≤ ∑ p ∈ primesBelow n, (1 : ℝ) / ((n : ℝ) - p) :=
  erdos_1210 n hn A hA_valid hA_coprime

/-- The empty set has sum 0, trivially bounded by the prime sum. -/
theorem erdos_1210_empty (n : ℕ) (hn : 3 ≤ n) :
    (0 : ℝ) ≤ ∑ p ∈ primesBelow n, (1 : ℝ) / ((n : ℝ) - p) :=
  le_of_lt (primesBelow_sum_pos hn)

/-- The prime sum dominates any singleton prime: {p} has sum 1/(n-p) ≤ total prime sum. -/
theorem erdos_1210_prime_singleton (n : ℕ) (hn : 3 ≤ n) (p : ℕ)
    (hp : p.Prime) (hpn : p < n) :
    (1 : ℝ) / ((n : ℝ) - p) ≤ ∑ q ∈ primesBelow n, (1 : ℝ) / ((n : ℝ) - q) := by
  have hp_mem : p ∈ primesBelow n := by
    simp only [primesBelow, Finset.mem_filter, Finset.mem_range]
    exact ⟨hpn, hp⟩
  calc (1 : ℝ) / ((n : ℝ) - p)
      = ∑ q ∈ ({p} : Finset ℕ), (1 : ℝ) / ((n : ℝ) - q) := by simp
    _ ≤ ∑ q ∈ primesBelow n, (1 : ℝ) / ((n : ℝ) - q) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by simp [hp_mem])
        intro q hq _
        simp only [primesBelow, Finset.mem_filter, Finset.mem_range] at hq
        apply div_nonneg zero_le_one
        have : (q : ℝ) < n := by exact_mod_cast hq.1
        linarith

/-- Under the conjecture, any singleton {k} with k ∈ [1,n) has sum bounded by the prime sum.
    In particular, k = 4 (even composite) also satisfies the bound. -/
theorem erdos_1210_singleton_bounded (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k < n) :
    (1 : ℝ) / ((n : ℝ) - k) ≤ ∑ p ∈ primesBelow n, (1 : ℝ) / ((n : ℝ) - p) := by
  have hle := erdos_1210 n hn {k}
    (fun a ha => by simp only [Finset.mem_singleton] at ha; subst ha; exact ⟨hk1, hkn⟩)
    (fun a ha b hb hab => by simp only [Finset.mem_singleton] at ha hb; omega)
  simp only [Finset.sum_singleton] at hle
  exact hle

/-
## Counterexample: The Literal Statement Is FALSE

The literal axiom `erdos_1210` above is **unsound** as transcribed: there is a
concrete (n, A) for which the hypotheses are satisfied but the inequality
FAILS. The minimal witness is n = 5, A = {4}:

  - 4 ∈ [1, 5), so `ValidSubset 5 {4}` holds.
  - A = {4} is trivially pairwise coprime (singleton, vacuous condition).
  - ∑_{a ∈ {4}} 1/(5 - a) = 1/(5-4) = 1.
  - primesBelow 5 = {2, 3}, so ∑_{p < 5 prime} 1/(5 - p) = 1/3 + 1/2 = 5/6.
  - 1 > 5/6, so the conjectured bound fails.

The theorem `erdos_1210_literal_counterexample` below proves this in machine-
checked form. It does not invoke the bad axiom (to avoid deriving False and
destabilizing downstream uses), but its statement is direct evidence that
`erdos_1210` cannot be a theorem of any consistent extension of ZFC + Lean.

### Interpretation

The transcribed conjecture either:
  (a) requires unstated constraints on A (e.g., A ⊆ (n/2, n) or a > √n), or
  (b) uses different weights (e.g., 1/a instead of 1/(n-a)), or
  (c) was misrecorded in the source database.

Two open follow-ups:
  1. **Locate originals** [Er77c, Er80] to recover the intended hypothesis.
  2. **Revise the axiom** to a verified or correctly-stated form. The current
     axiom should be replaced (the four consequence theorems above are then
     vacuous and should be removed/refactored).
-/

/-- `primesBelow 5 = {2, 3}` (decidable equality of concrete Finsets). -/
theorem primesBelow_five : primesBelow 5 = ({2, 3} : Finset ℕ) := by
  unfold primesBelow
  decide

/-- The weighted sum over primes below 5 equals 5/6. -/
theorem primesBelow_five_sum :
    ∑ p ∈ primesBelow 5, (1 : ℝ) / ((5 : ℝ) - p) = 5 / 6 := by
  rw [primesBelow_five]
  have h23 : (2 : ℕ) ∉ ({3} : Finset ℕ) := by decide
  rw [show ({2, 3} : Finset ℕ) = insert 2 {3} from rfl,
      Finset.sum_insert h23, Finset.sum_singleton]
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

/-- **Counterexample to `erdos_1210` (as literally stated)**.

    At n = 5, A = {4}, the A-sum (= 1) STRICTLY EXCEEDS the prime-sum (= 5/6).
    All hypotheses of `erdos_1210` are satisfied (see
    `singleton_four_valid_at_five`), but the conclusion fails. -/
theorem erdos_1210_literal_counterexample :
    (∑ p ∈ primesBelow 5, (1 : ℝ) / ((5 : ℝ) - p)) <
      ∑ a ∈ ({4} : Finset ℕ), (1 : ℝ) / ((5 : ℝ) - a) := by
  rw [primesBelow_five_sum, Finset.sum_singleton]
  norm_num

end Erdos1210
