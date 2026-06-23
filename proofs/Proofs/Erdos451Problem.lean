/- Erdős Problem #451 — Primes in Interval (k, 2k) Avoiding Products

Estimate n_k, the smallest integer n > 2k such that the product
∏_{1 ≤ i ≤ k} (n - i) has no prime factor in the interval (k, 2k).

Known bounds:
- Lower: Erdős–Graham proved n_k > k^{1+c} for some c > 0.
- Upper: Adenwalla observed n_k ≤ ∏_{k < p < 2k} p = e^{O(k)}.
- Conjecture: n_k > k^d for every constant d, but n_k < e^{o(k)}.

Key insight: for prime p in (k, 2k), we have p | ∏_{i=1}^k (n-i) iff
n ≡ j (mod p) for some j ∈ {1,...,k}. Since k < p, this is a CRT problem.
The safe residues mod p are {0, k+1, ..., p-1}, giving p-k choices.

Computed values: n_1=3, n_2=6, n_3=9, n_4=20, n_5=13, n_6=21, n_7=21,
n_8=22, n_9=65, n_10=220, n_12=338, n_20=550.

Reference: https://erdosproblems.com/451
-/

import Mathlib

open Finset Real

/-- The product (n-1)(n-2)⋯(n-k) for n > k. -/
def descendingProduct (n k : ℕ) : ℕ :=
    (Finset.Icc 1 k).prod (fun i => n - i)

/-- A prime p is in the interval (k, 2k). -/
def IsInBertrandRange (p k : ℕ) : Prop :=
    k < p ∧ p < 2 * k ∧ p.Prime

instance (p k : ℕ) : Decidable (IsInBertrandRange p k) :=
  show Decidable (k < p ∧ p < 2 * k ∧ p.Prime) from inferInstance

/-- The product has no prime factor in (k, 2k). -/
def AvoidsBertrandPrimes (n k : ℕ) : Prop :=
    ∀ p : ℕ, IsInBertrandRange p k → ¬(p ∣ descendingProduct n k)

/- ## The primes in (k, 2k) -/

/-- The primes in the interval (k, 2k). -/
def bertrandPrimes (k : ℕ) : Finset ℕ :=
    (Finset.Icc (k + 1) (2 * k - 1)).filter Nat.Prime

/-- The safe residues for a single prime p > k are {0, k+1, ..., p-1}. -/
def safeResidues (k p : ℕ) : Finset ℕ :=
    {0} ∪ (Finset.Icc (k + 1) (p - 1))

/- ## The function n_k (axiomatic) -/

axiom nk : ℕ → ℕ

/-- n_k > 2k. -/
axiom nk_gt_2k (k : ℕ) (hk : 1 ≤ k) : 2 * k < nk k

/-- n_k avoids Bertrand-range primes. -/
/-- n_k is minimal: no smaller n > 2k avoids them. -/
axiom nk_minimal (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 * k < n)
    (ha : AvoidsBertrandPrimes n k) : nk k ≤ n

/- ## CRT structural lemmas -/

/-- For prime p > k, at most one of n-1, ..., n-k is divisible by p.
    If p | (n-i) and p | (n-j) then p | (i-j), but |i-j| < k < p. -/
theorem at_most_one_div (n k p : ℕ) (hp : Nat.Prime p) (hpk : k < p)
    (i j : ℕ) (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hdi : p ∣ (n - i)) (hdj : p ∣ (n - j)) (hn : k < n) :
    i = j := by
  rw [Finset.mem_Icc] at hi hj
  by_contra hij
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · -- Case i < j
    have hdiff : p ∣ (n - i) - (n - j) := Nat.dvd_sub hdi hdj
    have heq : (n - i) - (n - j) = j - i := by omega
    rw [heq] at hdiff
    exact absurd (Nat.le_of_dvd (by omega) hdiff) (by omega)
  · -- Case j < i
    have hdiff : p ∣ (n - j) - (n - i) := Nat.dvd_sub hdj hdi
    have heq : (n - j) - (n - i) = i - j := by omega
    rw [heq] at hdiff
    exact absurd (Nat.le_of_dvd (by omega) hdiff) (by omega)

/-- p divides the descending product iff p divides some factor. -/
theorem prime_dvd_descendingProduct (n k p : ℕ) (hp : Nat.Prime p)
    (_hn : k < n) :
    p ∣ descendingProduct n k ↔
    ∃ i ∈ Finset.Icc 1 k, p ∣ (n - i) := by
  simp only [descendingProduct]
  constructor
  · intro h
    have hprime : Prime p := hp.prime
    have : ∃ i ∈ Finset.Icc 1 k, p ∣ (fun i => n - i) i := by
      exact hprime.exists_mem_finset_dvd h
    simpa using this
  · intro ⟨i, hi, hd⟩
    exact dvd_trans hd (Finset.dvd_prod_of_mem _ hi)

/-- The number of safe residues is p - k when k < p < 2k. -/
theorem card_safeResidues (k p : ℕ) (_hp : Nat.Prime p) (hpk : k < p)
    (hpk2 : p < 2 * k) :
    (safeResidues k p).card = p - k := by
  simp only [safeResidues]
  have h0_notin : (0 : ℕ) ∉ Finset.Icc (k + 1) (p - 1) := by
    simp only [Finset.mem_Icc]; omega
  have hdisj : Disjoint ({0} : Finset ℕ) (Finset.Icc (k + 1) (p - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx; exact h0_notin
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton, Nat.card_Icc]
  omega

/-- Key CRT insight: if p divides n and p > k, then p does not divide
    n - i for any 1 ≤ i ≤ k, since p | n and p | (n-i) would give p | i,
    but i ≤ k < p contradicts this. -/
theorem prime_not_dvd_factor_when_dvd_n (n k p i : ℕ)
    (_hp : Nat.Prime p) (hpk : k < p) (_hn : k < n)
    (hi : 1 ≤ i) (hik : i ≤ k) (hpn : p ∣ n) :
    ¬(p ∣ (n - i)) := by
  intro h
  have hsub := Nat.dvd_sub' hpn h
  have heq : n - (n - i) = i := by omega
  rw [heq] at hsub
  exact absurd (Nat.le_of_dvd (by omega) hsub) (by omega)

/-- When n ≡ 0 (mod p) for all primes p in (k, 2k), the descending product
    avoids all Bertrand-range primes. This is the core of the CRT construction. -/
theorem avoids_when_divisible_by_all (n k : ℕ) (hn : 2 * k < n)
    (hdiv : ∀ p : ℕ, IsInBertrandRange p k → p ∣ n) :
    AvoidsBertrandPrimes n k := by
  intro p hp hprod
  obtain ⟨hpk, _, hprime⟩ := hp
  rw [prime_dvd_descendingProduct n k p hprime (by omega)] at hprod
  obtain ⟨i, hi, hdi⟩ := hprod
  rw [Finset.mem_Icc] at hi
  exact prime_not_dvd_factor_when_dvd_n n k p i hprime hpk (by omega) hi.1 hi.2
    (hdiv p hp) hdi

/-- AvoidsBertrandPrimes is equivalent to a finite check over bertrandPrimes k.
    This makes the property computationally verifiable. -/
theorem avoidsBertrand_iff_finset (n k : ℕ) (hk : 1 ≤ k) :
    AvoidsBertrandPrimes n k ↔
    ∀ p ∈ bertrandPrimes k, ¬(p ∣ descendingProduct n k) := by
  constructor
  · intro h p hp
    rw [bertrandPrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    exact h p ⟨by omega, by omega, hp.2⟩
  · intro h p ⟨hpk, hpk2, hprime⟩
    apply h p
    rw [bertrandPrimes, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hprime⟩

/- ## Known bounds -/

/-- Erdős–Graham lower bound: n_k > k^{1+c} for some constant c > 0. -/
/-- Adenwalla upper bound: n_k ≤ ∏_{k < p < 2k} p = e^{O(k)}.
    By CRT, taking n ≡ 0 (mod p) for all primes p in (k,2k). -/
/-- The trivial lower bound: n_k > 2k (by definition). -/
theorem nk_trivial_lower (k : ℕ) (hk : 1 ≤ k) : (2 * k : ℝ) < (nk k : ℝ) := by
  have := nk_gt_2k k hk
  exact_mod_cast this

/-- Adenwalla's bound via CRT: n_k ≤ product of primes in (k, 2k). -/
theorem adenwalla_crt_idea (k : ℕ) (hk : 1 ≤ k)
    (hM : 2 * k < (bertrandPrimes k).prod id)
    (hAvoids : AvoidsBertrandPrimes ((bertrandPrimes k).prod id) k) :
    nk k ≤ (bertrandPrimes k).prod id :=
  nk_minimal k hk _ hM hAvoids

/- ## Main conjectures (OPEN) -/

/-- Conjecture 1: n_k > k^d for every constant d. -/
def ErdosProblem451_superpolynomial : Prop :=
    ∀ (d : ℝ) (_ : 0 < d), ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (k : ℝ) ^ d < (nk k : ℝ)

/-- Conjecture 2: n_k < e^{o(k)}, i.e. n_k is sub-exponential. -/
def ErdosProblem451_subexponential : Prop :=
    ∀ (ε : ℝ) (_ : 0 < ε), ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (nk k : ℝ) < (2 : ℝ) ^ (ε * (k : ℝ))

/-- Erdős Problem 451: n_k is superpolynomial but sub-exponential. -/
def ErdosProblem451 : Prop :=
    ErdosProblem451_superpolynomial ∧ ErdosProblem451_subexponential
