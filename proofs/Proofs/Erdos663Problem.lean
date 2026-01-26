/-!
# Erdős Problem #663: Smallest Prime Not Dividing Consecutive Products

For positive integers `n` and `k`, define `q(n,k)` to be the least prime that does
not divide the product `∏_{1 ≤ i ≤ k} (n + i) = (n+1)(n+2)···(n+k)`.

Erdős asked whether `q(n,k) < (1 + o(1)) log n` as `n → ∞` for fixed `k`.

The weak bound `q(n,k) < (1 + o(1)) k · log n` follows from the prime number theorem:
for large `n`, all primes up to about `k · log n` must divide some term `n + i`.

Tao provided heuristic support for the conjecture. This problem is related to
Erdős Problem #457 on prime factors of consecutive products.

Reference: https://erdosproblems.com/663
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Consecutive Products and Smallest Missing Prime -/

/-- The product of k consecutive integers starting from n+1: (n+1)(n+2)···(n+k). -/
noncomputable def consecutiveProduct (n k : ℕ) : ℕ :=
  (Finset.range k).prod (fun i => n + i + 1)

/-- q(n,k) is the least prime that does not divide ∏_{1 ≤ i ≤ k} (n+i). -/
axiom smallestMissingPrime : ℕ → ℕ → ℕ

/-- q(n,k) is always prime. -/
axiom smallestMissingPrime_prime (n k : ℕ) (hk : 0 < k) :
    (smallestMissingPrime n k).Prime

/-- q(n,k) does not divide the consecutive product. -/
axiom smallestMissingPrime_not_dvd (n k : ℕ) (hk : 0 < k) :
    ¬(smallestMissingPrime n k ∣ consecutiveProduct n k)

/-- q(n,k) is the least such prime: every smaller prime divides the product. -/
axiom smallestMissingPrime_least (n k : ℕ) (hk : 0 < k) (p : ℕ)
    (hp : p.Prime) (hlt : p < smallestMissingPrime n k) :
    p ∣ consecutiveProduct n k

/-! ## Main Conjecture -/

/-- Erdős Problem 663: For each fixed k, q(n,k) < (1 + o(1)) log n.
    Formally: limsup of q(n,k) / log(n) as n → ∞ is at most 1. -/
def ErdosProblem663 : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (smallestMissingPrime n k : ℝ) < (1 + ε) * Real.log n

/-! ## Weak Bound -/

/-- The weak bound: q(n,k) < (1 + o(1)) k · log n follows from the prime
    number theorem. Every prime p ≤ k·log(n) divides some n+i for 1 ≤ i ≤ k
    when n is large enough. -/
def WeakBound : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (smallestMissingPrime n k : ℝ) < (1 + ε) * k * Real.log n

/-- The weak bound implies the main conjecture when k = 1. -/
theorem weak_bound_k1_implies_main :
    (∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (smallestMissingPrime n 1 : ℝ) < (1 + ε) * 1 * Real.log n) →
    (∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (smallestMissingPrime n 1 : ℝ) < (1 + ε) * Real.log n) := by
  intro h ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  exact ⟨N₀, fun n hn => by rw [mul_one] at hN₀; exact hN₀ n hn⟩

/-! ## Related Results -/

/-- For k = 1, q(n,1) is the least prime not dividing n+1. -/
theorem consecutive_product_k1 (n : ℕ) :
    consecutiveProduct n 1 = n + 1 := by
  simp [consecutiveProduct]

/-- Consecutive product is positive when k > 0. -/
theorem consecutiveProduct_pos (n k : ℕ) (hk : 0 < k) :
    0 < consecutiveProduct n k := by
  unfold consecutiveProduct
  apply Finset.prod_pos
  intro i _
  omega

/-- Connection to Problem 457: prime factors of consecutive integer products. -/
def RelatedToProblem457 : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ p ≤ k + 1 ∧
      p ∣ consecutiveProduct n k

/-- Small primes always divide sufficiently long consecutive products.
    If p ≤ k, then p divides (n+1)(n+2)···(n+k) since among k consecutive
    integers, at least one is divisible by p. -/
axiom small_prime_divides_product (n k p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) :
    p ∣ consecutiveProduct n k

/-- Lower bound: q(n,k) > k for all n, since every prime p ≤ k divides
    some term in k consecutive integers. -/
axiom q_gt_k (n k : ℕ) (hk : 1 < k) :
    k < smallestMissingPrime n k

/-! ## Monotonicity Properties -/

/-- q(n,k) is non-increasing in k: adding more terms can only help. -/
axiom q_mono_k (n k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hle : k₁ ≤ k₂) :
    smallestMissingPrime n k₂ ≤ smallestMissingPrime n k₁

/-- The conjecture implies the weak bound. -/
theorem main_implies_weak (h : ErdosProblem663) : WeakBound := by
  intro k hk ε hε
  obtain ⟨N₀, hN₀⟩ := h k hk ε hε
  refine ⟨N₀, fun n hn => ?_⟩
  calc (smallestMissingPrime n k : ℝ) < (1 + ε) * Real.log n := hN₀ n hn
    _ ≤ (1 + ε) * k * Real.log n := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        le_of_eq_of_le (by ring_nf) (by nlinarith [Nat.cast_pos.mpr hk])
