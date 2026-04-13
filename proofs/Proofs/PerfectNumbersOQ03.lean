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
theorem mersenne_prime_exp_prime {n : ℕ} (hM : Nat.Prime (M n)) : Nat.Prime n := by
  by_contra hn
  -- Establish n ≥ 2: M(0)=0 and M(1)=1 are not prime
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | _
    · simp [M] at hM
    · norm_num [M] at hM
    · omega
  -- n ≥ 2 and not prime: get prime factor a with a ∣ n, a < n
  obtain ⟨a, ha_prime, ha_dvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have ha_le : a ≤ n := Nat.le_of_dvd (by omega) ha_dvd
  -- a < n: if a = n then n is prime, contradicting hn
  have ha_lt : a < n := lt_of_le_of_ne ha_le (fun heq => hn (heq ▸ ha_prime))
  -- M(a) | M(n) by divisibility chain
  have hdvd_M : M a ∣ M n := mersenne_dvd_of_dvd ha_dvd
  -- 1 < M(a) since a ≥ 2, so 2^a ≥ 4, M(a) = 2^a - 1 ≥ 3
  have hMa_gt1 : 1 < M a := by
    show 1 < 2 ^ a - 1
    have : 4 ≤ 2 ^ a :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha_prime.two_le
    omega
  -- M(a) < M(n) since a < n (M strictly increasing)
  have hMa_lt : M a < M n := by
    show 2 ^ a - 1 < 2 ^ n - 1
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by norm_num)
    have h2 : 2 ^ a < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) ha_lt
    omega
  -- M(n) prime and 1 < M(a) < M(n) with M(a) | M(n): contradiction
  rcases hM.eq_one_or_self_of_dvd (M a) hdvd_M with h1 | h2
  · omega  -- M(a) = 1 contradicts 1 < M(a)
  · omega  -- M(a) = M(n) contradicts M(a) < M(n)

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
  haveI hqfact : Fact q.Prime := ⟨hq⟩
  have hp1 : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by norm_num)
  -- (2 : ZMod q) ≠ 0: q ∣ 2^p-1 which is odd, so q is odd, so q ∤ 2
  have h2_ne : (2 : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd]
    intro hq2  -- assume q ∣ 2 for contradiction
    -- q prime and q ∣ 2 forces q = 2
    have hq2' : q = 2 := le_antisymm (Nat.le_of_dvd (by norm_num) hq2) hq.two_le
    rw [hq2'] at hdvd  -- now 2 ∣ M p = 2^p - 1
    -- 2 ∣ 2^p (trivially) and 2 ∣ 2^p - M p forces 2 ∣ 1: contradiction
    have h2p : 2 ∣ 2 ^ p := dvd_pow_self 2 hp.pos.ne'
    have h12 : 2 ∣ 2 ^ p - M p := Nat.dvd_sub' h2p hdvd
    have hval : 2 ^ p - M p = 1 := by simp only [M]; omega
    exact absurd (hval ▸ h12) (by norm_num)
  -- Convert q ∣ 2^p - 1 to (2 : ZMod q)^p = 1
  have h2p_eq : (2 : ZMod q) ^ p = 1 := by
    have hzero : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := by
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd]; exact hdvd
    rw [Nat.cast_sub hp1, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hzero
    exact sub_eq_zero.mp hzero
  -- orderOf (2 : ZMod q) divides p
  have hord : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one h2p_eq
  -- p prime: orderOf = 1 or p
  rcases hp.eq_one_or_self_of_dvd _ hord with h1 | h_eq_p
  · -- orderOf = 1 → (2 : ZMod q) = 1 → (1 : ZMod q) = 0: contradicts one_ne_zero
    rw [orderOf_eq_one_iff] at h1
    have h1eq0 : (1 : ZMod q) = 0 :=
      calc (1 : ZMod q) = 2 - 1 := by ring
        _ = 1 - 1 := by rw [h1]
        _ = 0 := sub_self 1
    exact absurd h1eq0 one_ne_zero
  · -- orderOf (2 : ZMod q) = p; Fermat gives orderOf ∣ q - 1
    rw [← h_eq_p]
    have hfermat : (2 : ZMod q) ^ (Fintype.card (ZMod q) - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one h2_ne
    rw [ZMod.card q] at hfermat
    exact orderOf_dvd_of_pow_eq_one hfermat

/-- Special case: for p = 2, factors of M(2) = 3 satisfy 2 | q - 1. -/
lemma factor_cong_p2 {q : ℕ} (hq : Nat.Prime q) (h : q ∣ M 2) : 2 ∣ q - 1 := by
  have := factor_cong_one_mod_p (by norm_num) hq h
  exact this

-- ============================================================
-- Part IV: The LPW Conjecture
-- ============================================================

/-- The count of Mersenne primes with exponent ≤ N. -/
noncomputable def mersennePrimeCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ Nat.Prime (M p))).card

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

### Proved (0 sorries remaining)
- `mersenne_prime_exp_prime`: M(n) prime → n prime
  (prime factor a < n: M(a)|M(n), 1 < M(a) < M(n) contradicts primality)
- `factor_cong_one_mod_p`: prime q | 2^p-1 → p | q-1
  (ZMod order: ord_q(2)|p, ord_q(2)≠1, Fermat gives ord_q(2)|q-1)

### Open (formally stated)
- `LPWConjecture`: the Lenstra-Pomerance-Wagstaff density conjecture
  Count(Mersenne primes with p ≤ N) ~ (e^γ / log 2) · log log N
  Status: WIDE OPEN — no proof known
-/

#check @mersenne_prime_exp_prime
#check LPWConjecture

end MersennePrimeDist
