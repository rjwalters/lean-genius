/-
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

/- ## Consecutive Products and Smallest Missing Prime -/

/-- The product of k consecutive integers starting from n+1: (n+1)(n+2)···(n+k). -/
noncomputable def consecutiveProduct (n k : ℕ) : ℕ :=
  (Finset.range k).prod (fun i => n + i + 1)

/-- There exists a prime not dividing any consecutive product.
    Proof: by infinitude of primes, take a prime p > the product; then p ∤ product. -/
theorem exists_prime_not_dvd_consecutiveProduct (n k : ℕ) :
    ∃ p, p.Prime ∧ ¬(p ∣ consecutiveProduct n k) := by
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (consecutiveProduct n k + 1)
  exact ⟨p, hp_prime, fun h_dvd => by
    have h_pos : 0 < consecutiveProduct n k := by
      unfold consecutiveProduct; apply Finset.prod_pos; intro i _; omega
    exact absurd (Nat.le_of_dvd h_pos h_dvd) (by omega)⟩

/-- q(n,k): The least prime not dividing ∏_{1 ≤ i ≤ k} (n+i).
    Defined concretely via `Nat.find` using infinitude of primes. -/
noncomputable def smallestMissingPrime (n k : ℕ) : ℕ :=
  Nat.find (exists_prime_not_dvd_consecutiveProduct n k)

/-- q(n,k) is always prime. -/
theorem smallestMissingPrime_prime (n k : ℕ) (hk : 0 < k) :
    (smallestMissingPrime n k).Prime :=
  (Nat.find_spec (exists_prime_not_dvd_consecutiveProduct n k)).1

/-- q(n,k) does not divide the consecutive product. -/
theorem smallestMissingPrime_not_dvd (n k : ℕ) (hk : 0 < k) :
    ¬(smallestMissingPrime n k ∣ consecutiveProduct n k) :=
  (Nat.find_spec (exists_prime_not_dvd_consecutiveProduct n k)).2

/-- q(n,k) is the least such prime: every smaller prime divides the product. -/
theorem smallestMissingPrime_least (n k : ℕ) (hk : 0 < k) (p : ℕ)
    (hp : p.Prime) (hlt : p < smallestMissingPrime n k) :
    p ∣ consecutiveProduct n k := by
  by_contra h
  exact absurd hlt (not_lt.mpr (Nat.find_min' _ ⟨hp, h⟩))

/- ## Main Conjecture -/

/-- Erdős Problem 663: For each fixed k, q(n,k) < (1 + o(1)) log n.
    Formally: limsup of q(n,k) / log(n) as n → ∞ is at most 1. -/
def ErdosProblem663 : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (smallestMissingPrime n k : ℝ) < (1 + ε) * Real.log n

/- ## Weak Bound -/

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

/- ## Related Results -/

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
theorem small_prime_divides_product (n k p : ℕ)
    (hp : p.Prime) (hpk : p ≤ k) :
    p ∣ consecutiveProduct n k := by
  unfold consecutiveProduct
  -- Among k ≥ p consecutive integers n+1, ..., n+k, one is divisible by p.
  -- Specifically, take i = (p - (n+1) mod p) mod p; then i < p ≤ k and p | (n+i+1).
  have hp_pos := hp.pos
  have ⟨i, hi, hdvd⟩ : ∃ i < k, p ∣ (n + i + 1) := by
    refine ⟨(p - (n + 1) % p) % p, lt_of_lt_of_le (Nat.mod_lt _ hp_pos) hpk, ?_⟩
    have h_div := Nat.div_add_mod (n + 1) p
    by_cases hr : (n + 1) % p = 0
    · simp [hr, Nat.mod_self]; exact ⟨(n + 1) / p, by omega⟩
    · rw [Nat.mod_eq_of_lt (by omega : p - (n + 1) % p < p)]
      exact ⟨(n + 1) / p + 1, by omega⟩
  exact dvd_trans hdvd (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi))

/-- Lower bound: q(n,k) > k for all n, since every prime p ≤ k divides
    some term in k consecutive integers.
    Proof: if q ≤ k, then q divides the product (by small_prime_divides_product),
    contradicting smallestMissingPrime_not_dvd. -/
theorem q_gt_k (n k : ℕ) (hk : 1 < k) :
    k < smallestMissingPrime n k := by
  by_contra h
  push_neg at h
  exact smallestMissingPrime_not_dvd n k (by omega)
    (small_prime_divides_product n k _ (smallestMissingPrime_prime n k (by omega)) h)

/- ## Monotonicity Properties -/

/-- q(n,k) is non-decreasing in k: longer products have more prime factors,
    so the smallest missing prime can only increase.
    Note: the original axiom had the wrong direction (≤ instead of ≥). -/
theorem q_mono_k (n k₁ k₂ : ℕ) (hk₁ : 0 < k₁) (hle : k₁ ≤ k₂) :
    smallestMissingPrime n k₁ ≤ smallestMissingPrime n k₂ := by
  -- Any prime p < q(n,k₁) divides the k₁-product, hence also the k₂-product
  -- (since the k₁-product divides the k₂-product). So p < q(n,k₂).
  -- Contrapositive: q(n,k₂) ≤ p < q(n,k₁) is impossible.
  by_contra h
  push_neg at h  -- h : smallestMissingPrime n k₂ < smallestMissingPrime n k₁
  -- q(n,k₂) is prime and < q(n,k₁), so q(n,k₂) divides the k₁-product
  have hq2_prime := smallestMissingPrime_prime n k₂ (by omega : 0 < k₂)
  have hq2_dvd := smallestMissingPrime_least n k₁ hk₁ _ hq2_prime h
  -- But q(n,k₂) doesn't divide the k₂-product
  have hq2_not_dvd := smallestMissingPrime_not_dvd n k₂ (by omega : 0 < k₂)
  -- The k₁-product divides the k₂-product (more factors)
  have hprod_dvd : consecutiveProduct n k₁ ∣ consecutiveProduct n k₂ := by
    unfold consecutiveProduct
    have hsub := Finset.range_mono hle
    exact Dvd.intro _ (Finset.prod_sdiff hsub).symm
  exact hq2_not_dvd (dvd_trans hq2_dvd hprod_dvd)

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
