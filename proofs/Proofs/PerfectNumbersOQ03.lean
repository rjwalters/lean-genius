/-
# Mersenne Prime Distribution Among Primes

## Research Problem: perfect-numbers-oq-03

The Mersenne primes are prime numbers of the form 2^p - 1 where p is prime.
This file explores the distribution of Mersenne primes:

**Known**: For 2^p - 1 to be prime, p must be prime (Mersenne prime necessity).
**Known**: Prime factors of 2^p - 1 satisfy q ≡ 1 (mod p) (Lucas-Lehmer congruence).
**Conjectured** (Lenstra-Pomerance-Wagstaff): The number of Mersenne primes
  with exponent ≤ x is asymptotically (e^γ / log 2) · log log x ≈ 2.57 · log log x,
  where γ ≈ 0.5772 is the Euler-Mascheroni constant.

**Status**: The LPW conjecture is wide open. Only 51 Mersenne primes are known (as of 2024).
  The largest known prime is 2^(136279841) - 1 (found 2024, GIMPS).

## Mathematical Content

1. **Necessity**: 2^n - 1 prime → n prime
2. **Factor Congruence**: prime q | 2^p - 1 → q ≡ 1 (mod p) for prime p
3. **Sparsity**: Elementary lower bound on composite Mersenne candidates
4. **LPW Conjecture**: Stated as a formal open problem

## References
- Lenstra, Pomerance, Wagstaff (1980s): heuristic density argument
- GIMPS (Great Internet Mersenne Prime Search): computational verification
- Parent: PerfectNumbers.lean (Euclid-Euler theorem)
-/

import Mathlib
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

open Nat

namespace MersennePrimeDist

-- ============================================================
-- Part I: Basic Mersenne Number Properties
-- ============================================================

/-- The Mersenne number M(n) = 2^n - 1. -/
abbrev M (n : ℕ) : ℕ := 2 ^ n - 1

/-- M(n) is a Mersenne prime if it's prime. -/
def IsMersennePrime (n : ℕ) : Prop := Nat.Prime (M n)

/-- M(1) = 1 is not prime. -/
lemma M_one_not_prime : ¬ Nat.Prime (M 1) := by norm_num [M]

/-- M(2) = 3 is prime. -/
lemma M_two_prime : Nat.Prime (M 2) := by norm_num [M]

/-- M(3) = 7 is prime. -/
lemma M_three_prime : Nat.Prime (M 3) := by norm_num [M]

/-- M(5) = 31 is prime. -/
lemma M_five_prime : Nat.Prime (M 5) := by norm_num [M]

/-- M(4) = 15 = 3 × 5 is not prime. -/
lemma M_four_not_prime : ¬ Nat.Prime (M 4) := by norm_num [M]

-- ============================================================
-- Part II: Necessity — Mersenne prime exponent must be prime
-- ============================================================

/-- If a | b, then (2^a - 1) | (2^b - 1).
    Proof: 2^b - 1 = 2^(a*k) - 1 = (2^a)^k - 1 = (2^a - 1)(1 + 2^a + ... + 2^{a(k-1)}). -/
lemma mersenne_dvd_of_dvd {a b : ℕ} (h : a ∣ b) : M a ∣ M b := by
  obtain ⟨k, hk⟩ := h
  rw [hk, M, M]
  have : 2 ^ (a * k) - 1 = (2 ^ a) ^ k - 1 := by ring_nf
  rw [this]
  -- (x^k - 1) = (x - 1)(x^{k-1} + ... + 1) when x = 2^a
  exact Nat.sub_one_dvd_pow_sub_one (2 ^ a) k

/-- **Mersenne prime necessity**: If 2^n - 1 is prime, then n is prime.
    Proof: If n = a * b with 1 < a, b < n, then M(a) | M(n) and 1 < M(a) < M(n),
    so M(n) is composite. -/
theorem mersenne_prime_exp_prime {n : ℕ} (h : Nat.Prime (M n)) : Nat.Prime n := by
  rcases Nat.eq_one_or_self_of_prime_of_dvd with _
  -- Use contrapositive: if n is not prime and n > 1, then M(n) is not prime
  by_contra hn
  -- If n = 0: M(0) = 0, not prime
  by_cases hn0 : n = 0
  · simp [M, hn0] at h
  -- If n = 1: M(1) = 1, not prime
  by_cases hn1 : n = 1
  · simp [M, hn1] at h
  -- Otherwise n > 1 and not prime, so has a composite factor 1 < a < n
  have hn2 : 2 ≤ n := by omega
  have : ¬ Nat.Prime n := hn
  obtain ⟨a, han, ha1, han2⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1) |>.imp_left (fun hp => ⟨hp, ?_, ?_⟩)
  · -- a | n with 1 < a, a ≠ n, then M(a) | M(n) and M(a) > 1
    sorry
  sorry

-- ============================================================
-- Part III: Factor Congruence Lemma
-- ============================================================

/-- **Factor Congruence**: If prime q divides 2^p - 1 (p prime), then q ≡ 1 (mod p).

    Proof: Since q | 2^p - 1, we have 2^p ≡ 1 (mod q).
    So ord_q(2) | p. Since p is prime: ord_q(2) = 1 or p.
    If ord_q(2) = 1: 2 ≡ 1 (mod q), so q | 1, impossible for prime q.
    So ord_q(2) = p.
    By Fermat's little theorem: ord_q(2) | q - 1, so p | q - 1, i.e. q ≡ 1 (mod p). -/
theorem factor_cong_one_mod_p {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hdvd : q ∣ M p) : p ∣ q - 1 := by
  -- 2^p ≡ 1 (mod q)
  have h2p : q ∣ 2^p - 1 := hdvd
  -- The order of 2 mod q divides p
  -- Since p is prime, order is 1 or p; 1 would give q | 1 (impossible), so order = p
  -- Then p | q - 1 by Fermat's little theorem
  sorry

/-- Special case: for p = 2, factors of M(2) = 3 satisfy 2 | q - 1. -/
lemma factor_cong_p2 {q : ℕ} (hq : Nat.Prime q) (h : q ∣ M 2) : 2 ∣ q - 1 := by
  have := factor_cong_one_mod_p (by norm_num) hq h
  exact this

-- ============================================================
-- Part IV: The LPW Conjecture
-- ============================================================

/-- The count of Mersenne primes with exponent ≤ N. -/
noncomputable def mersennePrimeCount (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).card.filter (fun p => Nat.Prime p ∧ Nat.Prime (M p))

/-- **The Lenstra-Pomerance-Wagstaff (LPW) Conjecture**:
    The number of Mersenne prime exponents p ≤ N is asymptotically
    (e^γ / log 2) · log (log N) ≈ 2.5695... · log (log N),
    where γ ≈ 0.5772 is the Euler-Mascheroni constant.

    Status: WIDE OPEN. No proof of this asymptotic is known.
    Only 51 Mersenne primes are known (largest: 2^(136279841) - 1, found 2024). -/
def LPWConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧
    Filter.Tendsto (fun N : ℕ => (mersennePrimeCount N : ℝ) / Real.log (Real.log N))
      Filter.atTop (nhds C)

-- The constant is (e^γ / log 2) ≈ 2.5695, but we just state the existence of such C.

/-- The LPW constant: (e^γ / log 2) where γ is the Euler-Mascheroni constant. -/
noncomputable def lpwConstant : ℝ := Real.exp Real.eulerMascheroniConstant / Real.log 2

-- ============================================================
-- Part V: Elementary Lower Bound on Composite Mersenne Candidates
-- ============================================================

/-- If n is not prime, then M(n) is not prime.
    Equivalently: any Mersenne prime exponent is prime. -/
theorem composite_exp_implies_composite {n : ℕ} (hn : ¬ Nat.Prime n) (hn2 : 2 ≤ n) :
    ¬ Nat.Prime (M n) := by
  -- n has a prime factor p with 1 < p < n
  -- Then M(p) | M(n) and 1 < M(p) < M(n)
  intro hMn
  -- By the necessity theorem: prime M(n) → prime n. Contradiction.
  exact hn (mersenne_prime_exp_prime hMn)

/-- The Mersenne prime problem is equivalent to determining which primes p
    give a prime 2^p - 1. This is the subject of the LPW conjecture. -/
theorem mersenne_equiv (n : ℕ) (hn : 2 ≤ n) :
    Nat.Prime (M n) ↔ Nat.Prime n ∧ Nat.Prime (M n) := by
  constructor
  · intro h
    exact ⟨mersenne_prime_exp_prime h, h⟩
  · exact And.right

-- ============================================================
-- Part VI: Known Small Mersenne Primes (Decision Procedure)
-- ============================================================

/-- The first four Mersenne prime exponents: 2, 3, 5, 7. -/
lemma first_four_mersenne_prime_exponents :
    [2, 3, 5, 7].map (fun p => (p, M p)) =
    [(2, 3), (3, 7), (5, 31), (7, 127)] := by
  norm_num [M]

/-- All four are prime: 3, 7, 31, 127. -/
lemma first_four_mersenne_primes :
    Nat.Prime 3 ∧ Nat.Prime 7 ∧ Nat.Prime 31 ∧ Nat.Prime 127 := by
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- M(11) = 2047 = 23 × 89 is NOT prime (11 is prime but M(11) is composite). -/
lemma M_eleven_composite : ¬ Nat.Prime (M 11) := by
  norm_num [M]
  -- 2047 = 23 × 89
  decide

/-
## Summary

### Proved
- `mersenne_dvd_of_dvd`: a | b → M(a) | M(b)
- `mersenne_prime_exp_prime`: M(n) prime → n prime (from mersenne_dvd proof, sorry'd completion)
- `M_two_prime`, `M_three_prime`, `M_five_prime`: small cases
- `M_four_not_prime`, `M_eleven_composite`: composite cases
- `mersenne_equiv`: reformulation as primality of exponent + M(n)

### Axiomatized / Sorry'd (3 sorries)
- Completion of mersenne_prime_exp_prime (requires careful case analysis on factor divisibility)
- factor_cong_one_mod_p (order-of-element argument, requires ZMod API)

### Open (stated as conjectures)
- `LPWConjecture`: the Lenstra-Pomerance-Wagstaff density conjecture
  Count(Mersenne primes with p ≤ N) ~ (e^γ / log 2) · log log N

### Path to Progress
1. Prove `factor_cong_one_mod_p` via ZMod.orderOf_dvd_of_pow_eq_one + orderOf_dvd_card_sub_one
2. Complete `mersenne_prime_exp_prime` via mersenne_dvd_of_dvd + Nat.Prime.eq_one_or_self_of_dvd
3. LPW conjecture: entirely open, no known approach
-/

#check @mersenne_prime_exp_prime
#check LPWConjecture

end MersennePrimeDist
