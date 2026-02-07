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

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

open Finset in
/-- The product (n-1)(n-2)⋯(n-k) for n > k. -/
def descendingProduct (n k : ℕ) : ℕ :=
    (Icc 1 k).prod (fun i => n - i)

/-- A prime p is in the interval (k, 2k). -/
def IsInBertrandRange (p k : ℕ) : Prop :=
    k < p ∧ p < 2 * k ∧ p.Prime

instance : DecidablePred (fun p => IsInBertrandRange p k) :=
  fun p => And.decidable

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
axiom nk_avoids (k : ℕ) (hk : 1 ≤ k) : AvoidsBertrandPrimes (nk k) k

/-- n_k is minimal: no smaller n > 2k avoids them. -/
axiom nk_minimal (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 * k < n)
    (ha : AvoidsBertrandPrimes n k) : nk k ≤ n

/- ## CRT structural lemmas

For prime p in (k, 2k), the product (n-1)(n-2)⋯(n-k) is divisible by p
iff at least one of n-1, n-2, ..., n-k is divisible by p. Since k < p,
at most one of these k consecutive integers can be divisible by p.

So p | ∏(n-i) iff n ≡ j (mod p) for some j ∈ {1, ..., k}.
To avoid p, we need n mod p ∈ {0, k+1, k+2, ..., p-1}. -/

/-- For prime p > k, at most one of n-1, ..., n-k is divisible by p.
    If p | (n-i) and p | (n-j) then p | (i-j), but |i-j| < k < p. -/
theorem at_most_one_div (n k p : ℕ) (hp : Nat.Prime p) (hpk : k < p)
    (i j : ℕ) (hi : i ∈ Finset.Icc 1 k) (hj : j ∈ Finset.Icc 1 k)
    (hdi : p ∣ (n - i)) (hdj : p ∣ (n - j)) (hn : k < n) :
    i = j := by sorry

/-- p divides the descending product iff p divides some factor. -/
theorem prime_dvd_descendingProduct (n k p : ℕ) (hp : Nat.Prime p)
    (hn : k < n) :
    p ∣ descendingProduct n k ↔
    ∃ i ∈ Finset.Icc 1 k, p ∣ (n - i) := by sorry

/-- The number of safe residues is p - k when k < p < 2k. -/
theorem card_safeResidues (k p : ℕ) (hp : Nat.Prime p) (hpk : k < p)
    (hpk2 : p < 2 * k) :
    (safeResidues k p).card = p - k := by sorry

/- ## Known bounds -/

/-- Erdős–Graham lower bound: n_k > k^{1+c} for some constant c > 0. -/
axiom erdos_graham_lower :
    ∃ c : ℚ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (k : ℚ) ^ (1 + c) < (nk k : ℚ)

/-- Adenwalla upper bound: n_k ≤ ∏_{k < p < 2k} p = e^{O(k)}.
    By CRT, taking n ≡ 0 (mod p) for all primes p in (k,2k). -/
axiom adenwalla_upper :
    ∃ C : ℚ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (nk k : ℚ) ≤ (2 : ℚ) ^ (C * (k : ℚ))

/-- The trivial lower bound: n_k > 2k (by definition). -/
theorem nk_trivial_lower (k : ℕ) (hk : 1 ≤ k) : (2 * k : ℚ) < (nk k : ℚ) := by
  have := nk_gt_2k k hk
  exact_mod_cast this

/-- Adenwalla's bound via CRT: n_k ≤ product of primes in (k, 2k). -/
theorem adenwalla_crt_idea (k : ℕ) (hk : 1 ≤ k) :
    let M := (bertrandPrimes k).prod id
    2 * k < M →
    AvoidsBertrandPrimes M k →
    nk k ≤ M :=
  fun hM hAvoids => nk_minimal k hk M hM hAvoids

/- ## Main conjectures (OPEN) -/

/-- Conjecture 1: n_k > k^d for every constant d. -/
def ErdosProblem451_superpolynomial : Prop :=
    ∀ (d : ℚ) (hd : 0 < d), ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (k : ℚ) ^ d < (nk k : ℚ)

/-- Conjecture 2: n_k < e^{o(k)}, i.e. n_k is sub-exponential. -/
def ErdosProblem451_subexponential : Prop :=
    ∀ (ε : ℚ) (hε : 0 < ε), ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (nk k : ℚ) < (2 : ℚ) ^ (ε * (k : ℚ))

/-- Erdős Problem 451: n_k is superpolynomial but sub-exponential. -/
def ErdosProblem451 : Prop :=
    ErdosProblem451_superpolynomial ∧ ErdosProblem451_subexponential
