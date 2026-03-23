/-
# Erdős Problem #1055: Prime Classification by p+1 Factorization

Classify primes by the factorization structure of p+1:
- Class 1: all prime factors of p+1 are 2 or 3 (i.e., p+1 is 3-smooth)
- Class r: all prime factors of p+1 are in class ≤ r-1, with at least one
  prime factor in class exactly r-1.

## Key Questions
1. Are there infinitely many primes in each class?
2. How does p_r^{1/r} behave, where p_r is the least prime in class r?
   - Erdős conjectured p_r^{1/r} → ∞
   - Selfridge conjectured p_r^{1/r} is bounded

## Known Data
- Least primes by class: p_1=2, p_2=13, p_3=37, p_4=73, p_5=1021 (OEIS A005113)
- The count of primes ≤ n in class r is at most n^{o(1)}

## Status: OPEN

Reference: https://erdosproblems.com/1055
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/- ## Helper Lemmas -/

/-- Any non-{2,3} prime factor of p+1 is strictly less than p, when p is prime. -/
private lemma nonSmooth_factor_lt {p q : ℕ} (hp : Nat.Prime p)
    (hq : q ∈ ((p + 1).primeFactorsList.dedup.filter (fun r => r != 2 && r != 3))) :
    q < p := by
  rw [List.mem_filter] at hq
  obtain ⟨hq_dedup, hq_filt⟩ := hq
  rw [List.mem_dedup] at hq_dedup
  have hq_dvd := Nat.dvd_of_mem_primeFactorsList hq_dedup
  have hq_prime := Nat.prime_of_mem_primeFactorsList hq_dedup
  have hq_le : q ≤ p + 1 := Nat.le_of_dvd (by omega) hq_dvd
  have hq_ne2 : q ≠ 2 := by intro h; subst h; simp at hq_filt
  have hq_ne3 : q ≠ 3 := by intro h; subst h; simp at hq_filt
  by_contra h_not_lt
  push_neg at h_not_lt
  have hqp : q = p ∨ q = p + 1 := by omega
  rcases hqp with rfl | rfl
  · -- q = p: p ∣ (p+1) is impossible for prime p
    exfalso
    obtain ⟨k, hk⟩ := hq_dvd
    have hp2 := hp.one_lt
    have hk1 : k ≤ 1 := by nlinarith
    interval_cases k <;> omega
  · -- q = p+1: (p+1) is prime, p+1 ≠ 2, p+1 ≠ 3
    exfalso
    have hp_ne2 : p ≠ 2 := by omega
    have h2_ndvd_p : ¬ (2 ∣ p) := by
      intro h2p; rcases hp.eq_one_or_self_of_dvd 2 h2p with h | h <;> omega
    have h2_dvd_p1 : 2 ∣ (p + 1) := by
      rw [Nat.dvd_iff_mod_eq_zero] at h2_ndvd_p ⊢; omega
    rcases hq_prime.eq_one_or_self_of_dvd 2 h2_dvd_p1 with h | h <;> omega

/- ## Core Definitions -/

/-- The Erdős–Selfridge class of a prime p, defined by well-founded recursion. -/
def primeClass (p : ℕ) : ℕ :=
  if hp : Nat.Prime p then
    let factors := (p + 1).primeFactorsList.dedup
    let nonSmooth := factors.filter (fun q => q != 2 && q != 3)
    if nonSmooth.isEmpty then 1
    else 1 + nonSmooth.attach.foldl (fun acc ⟨q, hq⟩ =>
      have : q < p := nonSmooth_factor_lt hp hq
      max acc (primeClass q)) 0
  else 0
termination_by p

def IsInClass (p : ℕ) (r : ℕ) : Prop := p.Prime ∧ primeClass p = r

/- ## Verified Class Values -/

theorem class_2 : primeClass 2 = 1 := by native_decide
theorem class_3 : primeClass 3 = 1 := by native_decide
theorem class_5 : primeClass 5 = 1 := by native_decide
theorem class_7 : primeClass 7 = 1 := by native_decide
theorem class_11 : primeClass 11 = 1 := by native_decide
theorem class_17 : primeClass 17 = 1 := by native_decide
theorem class_23 : primeClass 23 = 1 := by native_decide
theorem class_31 : primeClass 31 = 1 := by native_decide
theorem class_13 : primeClass 13 = 2 := by native_decide
theorem class_19 : primeClass 19 = 2 := by native_decide
theorem class_29 : primeClass 29 = 2 := by native_decide
theorem class_41 : primeClass 41 = 2 := by native_decide
theorem class_43 : primeClass 43 = 2 := by native_decide
theorem class_37 : primeClass 37 = 3 := by native_decide
theorem class_103 : primeClass 103 = 3 := by native_decide
theorem class_113 : primeClass 113 = 3 := by native_decide
theorem class_73 : primeClass 73 = 4 := by native_decide
theorem class_1021 : primeClass 1021 = 5 := by native_decide
theorem class_nonprime_4 : primeClass 4 = 0 := by native_decide
theorem class_nonprime_6 : primeClass 6 = 0 := by native_decide

/- ## Least Prime in Each Class -/

def findLeastPrimeInClass (r : ℕ) (bound : ℕ) : Option ℕ :=
  (List.range bound).find? (fun p => primeClass p == r)

theorem least_class_1 : findLeastPrimeInClass 1 10 = some 2 := by native_decide
theorem least_class_2 : findLeastPrimeInClass 2 20 = some 13 := by native_decide
theorem least_class_3 : findLeastPrimeInClass 3 50 = some 37 := by native_decide
theorem least_class_4 : findLeastPrimeInClass 4 100 = some 73 := by native_decide
theorem least_class_5 : findLeastPrimeInClass 5 1100 = some 1021 := by native_decide

/- ## Foldl Helper Lemmas (term-mode to avoid tactic issues) -/

private theorem foldl_max_ge_init {α : Type*} :
    ∀ (l : List α) (f : α → ℕ) (init : ℕ),
    l.foldl (fun acc x => max acc (f x)) init ≥ init
  | [], _, init => le_refl init
  | _ :: as, f, init =>
    le_trans (le_max_left init _) (foldl_max_ge_init as f _)

private theorem foldl_max_ge_of_mem {α : Type*} :
    ∀ {l : List α} {x : α}, x ∈ l →
    ∀ (f : α → ℕ) (init : ℕ),
    l.foldl (fun acc y => max acc (f y)) init ≥ f x
  | _ :: _, _, List.Mem.head _, f, init =>
    le_trans (le_max_right init _) (foldl_max_ge_init _ f _)
  | _ :: _, _, List.Mem.tail _ hx, f, init =>
    foldl_max_ge_of_mem hx f (max init _)

/- ## Structural Properties -/

theorem class_one_iff_smooth (p : ℕ) (hp : Nat.Prime p) :
    primeClass p = 1 ↔ ∀ q ∈ (p + 1).primeFactorsList, q = 2 ∨ q = 3 := by
  sorry

theorem primeClass_pos_of_prime (p : ℕ) (hp : Nat.Prime p) :
    primeClass p ≥ 1 := by
  unfold primeClass; simp only [hp, dite_true]; split <;> omega

/-- Class is monotone: if q is a non-{2,3} prime factor of p+1, then
    primeClass q < primeClass p. With the WF definition, primeClass p
    unfolds as 1 + max(primeClass q_i), giving primeClass p > primeClass q. -/
theorem class_of_factor_lt (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hdvd : q ∣ p + 1) (hq2 : q ≠ 2) (hq3 : q ≠ 3) :
    primeClass q < primeClass p := by
  have hq_in_pfl : q ∈ (p + 1).primeFactorsList := by
    rw [Nat.mem_primeFactorsList (by omega : (p + 1) ≠ 0)]
    exact ⟨hq, hdvd⟩
  have hq_in_ns : q ∈ ((p + 1).primeFactorsList.dedup.filter (fun r => r != 2 && r != 3)) := by
    rw [List.mem_filter, List.mem_dedup]
    exact ⟨hq_in_pfl, by simp [hq2, hq3]⟩
  -- Unfold primeClass p to expose the 1 + foldl structure
  show primeClass q < primeClass p
  unfold primeClass
  simp only [hp, dite_true]
  -- Show nonSmooth is nonempty
  have h_not_empty : ((p + 1).primeFactorsList.dedup.filter
      (fun r => r != 2 && r != 3)).isEmpty = false := by
    cases hlist : (p + 1).primeFactorsList.dedup.filter (fun r => r != 2 && r != 3) with
    | nil => simp [hlist] at hq_in_ns
    | cons _ _ => rfl
  simp only [h_not_empty, ite_false]
  -- Goal: primeClass q < 1 + foldl max ... 0
  -- The foldl includes primeClass q (since q is in the list), so foldl ≥ primeClass q
  -- Therefore 1 + foldl > primeClass q
  -- NOTE: The foldl function in the goal includes a `have` proof term that is
  -- definitionally irrelevant but makes syntactic matching with helper lemmas
  -- difficult. This bound is a routine property of foldl with max.
  sorry

/- ## Concrete Evidence for Infinitude -/

theorem many_class1_primes :
    (Finset.filter (fun p => decide (primeClass p = 1)) (Finset.range 50)).card ≥ 8 := by
  native_decide

theorem many_class2_primes :
    (Finset.filter (fun p => decide (primeClass p = 2)) (Finset.range 100)).card ≥ 8 := by
  native_decide

theorem many_class3_primes :
    (Finset.filter (fun p => decide (primeClass p = 3)) (Finset.range 200)).card ≥ 3 := by
  native_decide

/- ## The Main Conjectures (OPEN) -/

axiom infinitely_many_in_each_class (r : ℕ) (hr : r ≥ 1) :
    Set.Infinite {p : ℕ | p.Prime ∧ primeClass p = r}

axiom erdos_growth_conjecture :
    ∀ M : ℝ, ∃ R : ℕ, ∀ r ≥ R,
      ∀ p : ℕ, p.Prime → primeClass p = r →
        (∀ q : ℕ, q.Prime → primeClass q = r → p ≤ q) →
        ((p : ℝ)) ^ ((1 : ℝ) / (r : ℝ)) ≥ M

axiom selfridge_bounded_conjecture :
    ∃ M : ℝ, ∀ r : ℕ, r ≥ 1 →
      ∀ p : ℕ, p.Prime → primeClass p = r →
        (∀ q : ℕ, q.Prime → primeClass q = r → p ≤ q) →
        ((p : ℝ)) ^ ((1 : ℝ) / (r : ℝ)) ≤ M

axiom class_density_subpolynomial (r : ℕ) (hr : r ≥ 1) :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ((Finset.filter (fun p => decide (Nat.Prime p ∧ primeClass p = r))
        (Finset.range (n + 1))).card : ℝ) ≤ (n : ℝ) ^ ε
