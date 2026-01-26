/-!
# Erdős Problem #451 — Primes in Interval (k, 2k) Avoiding Products

Estimate n_k, the smallest integer n > 2k such that the product
∏_{1 ≤ i ≤ k} (n - i) has no prime factor in the interval (k, 2k).

## Known bounds

- **Lower**: Erdős–Graham proved n_k > k^{1+c} for some c > 0.
- **Upper**: Adenwalla observed n_k ≤ ∏_{k < p < 2k} p = e^{O(k)}.
- **Conjecture**: n_k > k^d for every constant d, but n_k < e^{o(k)}.

Reference: https://erdosproblems.com/451
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## The product ∏(n - i) and prime factors -/

/-- The product (n-1)(n-2)⋯(n-k) for n > k. -/
def descendingProduct (n k : ℕ) : ℕ :=
    (Finset.Icc 1 k).prod (fun i => n - i)

/-- A prime p is in the interval (k, 2k). -/
def IsInBertrandRange (p k : ℕ) : Prop :=
    k < p ∧ p < 2 * k ∧ p.Prime

/-- The product has no prime factor in (k, 2k). -/
def AvoidsBertrandPrimes (n k : ℕ) : Prop :=
    ∀ p : ℕ, IsInBertrandRange p k → ¬(p ∣ descendingProduct n k)

/-! ## The function n_k -/

/-- n_k is the smallest integer > 2k such that ∏(n-i) avoids primes in (k,2k).
    Axiomatised with its defining properties. -/
axiom nk : ℕ → ℕ

/-- n_k > 2k. -/
axiom nk_gt_2k (k : ℕ) (hk : 1 ≤ k) : 2 * k < nk k

/-- n_k avoids Bertrand-range primes. -/
axiom nk_avoids (k : ℕ) (hk : 1 ≤ k) : AvoidsBertrandPrimes (nk k) k

/-- n_k is minimal: no smaller n > 2k avoids them. -/
axiom nk_minimal (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 2 * k < n)
    (ha : AvoidsBertrandPrimes n k) : nk k ≤ n

/-! ## Known bounds -/

/-- Erdős–Graham lower bound: n_k > k^{1+c} for some constant c > 0. -/
axiom erdos_graham_lower :
    ∃ c : ℚ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (k : ℚ) ^ (1 + c) < (nk k : ℚ)

/-- Adenwalla upper bound: n_k ≤ ∏_{k < p < 2k} p = e^{O(k)}.
    In particular, n_k ≤ some exponential in k. -/
axiom adenwalla_upper :
    ∃ C : ℚ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (nk k : ℚ) ≤ (2 : ℚ) ^ (C * (k : ℚ))

/-! ## Main conjectures -/

/-- Conjecture 1: n_k > k^d for every constant d.
    Formally: for every d > 0, there exists k₀ such that
    n_k > k^d for all k ≥ k₀. -/
def ErdosProblem451_superpolynomial : Prop :=
    ∀ (d : ℚ) (hd : 0 < d), ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (k : ℚ) ^ d < (nk k : ℚ)

/-- Conjecture 2: n_k < e^{o(k)}, i.e. n_k is sub-exponential.
    Formally: for every ε > 0, n_k < 2^{ε·k} for large k. -/
def ErdosProblem451_subexponential : Prop :=
    ∀ (ε : ℚ) (hε : 0 < ε), ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (nk k : ℚ) < (2 : ℚ) ^ (ε * (k : ℚ))

/-- Erdős Problem 451: n_k is superpolynomial but sub-exponential. -/
def ErdosProblem451 : Prop :=
    ErdosProblem451_superpolynomial ∧ ErdosProblem451_subexponential
