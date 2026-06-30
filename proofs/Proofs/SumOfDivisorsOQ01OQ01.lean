import Mathlib

/-
# Odd perfect numbers have at least three distinct prime factors

## What this proves

`odd_perfect_three_primeFactors` : every **odd** perfect number `N` satisfies
`3 ≤ N.primeFactors.card`, i.e. it has at least three *distinct* prime factors.

This is the classical sharp structural constraint that sits one step beyond
Euler's form for odd perfect numbers (`odd_perfect_euler_form`, the
`sum-of-divisors-oq-01` headline).  Euler's form fixes the *shape*
`N = pᵃ m²`; this result bounds the *number of distinct primes* from below.

## The mathematics (abundancy-index argument)

For a prime power the sum-of-divisors function obeys the sharp geometric bound

  `σ(pᵃ) · (p − 1) = p^{a+1} − 1 < p^{a+1}`,

equivalently the abundancy contribution `σ(pᵃ)/pᵃ < p/(p−1)`.  If `N` had only
one prime factor it would be a prime power, hence *deficient*
(`σ(pᵃ) < 2pᵃ`), contradicting `σ(N) = 2N`.  If `N = pᵃ qᵇ` had exactly two
(necessarily odd, so `≥ 3`) prime factors, multiplying the two sharp bounds
gives `2(p−1)(q−1) < pq`, which is impossible for distinct integers `≥ 3`
because `2(p−1)(q−1) − pq = (p−2)(q−2) − 2 ≥ 0`.  Hence `N` has `≥ 3` distinct
primes.  (The bound is best possible for the *abundancy* threshold: the two
smallest odd primes give `(3/2)(5/4) = 15/8 < 2`.)

The proof is elementary, `native_decide`-free, and fully kernel-checked
(0 axioms beyond Lean's logical foundations).

## Why this is new

The Perfect-Numbers / Sum-of-Divisors gallery contains Euler's form, prime-power
deficiency (`PerfectNumbersOQ05.prime_pow_is_deficient`), and σ parity/square
results, but **not** a lower bound on the count of distinct prime factors of an
odd perfect number.  This file fills that gap.
-/

open ArithmeticFunction Finset Nat
open scoped ArithmeticFunction.sigma

namespace SumOfDivisorsOQ01OQ01

/-! ## The sharp per-prime-power identity -/

/-- **Sharp prime-power geometric identity (subtraction-free form).**
For a prime `p` and any exponent `a`,
`σ(pᵃ) · p + 1 = pᵃ · p + σ(pᵃ)`.

This is the integer form of `σ(pᵃ)(p − 1) = p^{a+1} − 1`, the engine of the
abundancy bound `σ(pᵃ)/pᵃ < p/(p−1)`.  Proved by casting the finite geometric
sum `σ(pᵃ) = Σ_{k≤a} pᵏ` to `ℤ` and applying `geom_sum_mul`. -/
theorem sigma_one_primePow_succ_eq {p a : ℕ} (hp : p.Prime) :
    σ 1 (p ^ a) * p + 1 = p ^ a * p + σ 1 (p ^ a) := by
  have key : ((σ 1 (p ^ a) * p + 1 : ℕ) : ℤ) = ((p ^ a * p + σ 1 (p ^ a) : ℕ) : ℤ) := by
    rw [sigma_one_apply_prime_pow hp]
    push_cast
    linear_combination geom_sum_mul (p : ℤ) (a + 1)
  exact_mod_cast key

/-! ## The elementary number inequality at the heart of the two-prime case -/

/-- For distinct integers `P, Q ≥ 3` one has `P·Q ≤ 2·(P−1)·(Q−1)`.

Equivalently `(P−2)(Q−2) ≥ 2`: the two factors are `≥ 1` and, being distinct
positives, are not both `1`, so their product is `≥ 2`.  The numerical content
is `2(P−1)(Q−1) − PQ = (P−2)(Q−2) − 2 ≥ 0`. -/
theorem two_le_prod {P Q : ℤ} (hP : 3 ≤ P) (hQ : 3 ≤ Q) (hne : P ≠ Q) :
    P * Q ≤ 2 * (P - 1) * (Q - 1) := by
  -- distinct integers `≥ 3` have sum `≥ 7`
  have hs : 7 ≤ P + Q := by omega
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ P - 3 by omega) (show (0 : ℤ) ≤ Q - 3 by omega), hs]

/-! ## Main theorem -/

/-- **Odd perfect numbers have at least three distinct prime factors.**

If `N` is odd and perfect then `3 ≤ N.primeFactors.card`. -/
theorem odd_perfect_three_primeFactors {N : ℕ} (hodd : Odd N) (hperf : N.Perfect) :
    3 ≤ N.primeFactors.card := by
  have hN0 : 0 < N := hperf.2
  have hN : N ≠ 0 := hN0.ne'
  -- perfect ⇒ σ(N) = 2N
  have hσ : σ 1 N = 2 * N := by
    have h := (Nat.perfect_iff_sum_divisors_eq_two_mul hN0).mp hperf
    rwa [← sigma_one_apply N] at h
  by_contra hlt
  push_neg at hlt
  have hcases : N.primeFactors.card = 0 ∨ N.primeFactors.card = 1 ∨ N.primeFactors.card = 2 := by
    omega
  rcases hcases with hc | hc | hc
  · -- ω = 0 ⇒ N = 1, but σ(1) = 1 ≠ 2
    rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at hc
    rcases hc with h | h
    · exact hN h
    · subst h; simp at hσ
  · -- ω = 1 ⇒ N is a prime power pᵏ, which is deficient
    have hpp : IsPrimePow N := isPrimePow_iff_card_primeFactors_eq_one.mpr hc
    obtain ⟨p, k, hp, _hk, rfl⟩ := (isPrimePow_nat_iff N).mp hpp
    -- σ(pᵏ) < 2 pᵏ contradicts σ(pᵏ) = 2 pᵏ
    have hdef : σ 1 (p ^ k) < 2 * p ^ k := by
      rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
      have hgeom : ∑ j ∈ range k, p ^ j < p ^ k :=
        Nat.geomSum_lt hp.two_le (fun _ hj => mem_range.mp hj)
      omega
    rw [hσ] at hdef
    exact lt_irrefl _ hdef
  · -- ω = 2 ⇒ N = pᵃ qᵇ with distinct odd primes p, q
    obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
    have hpmem : p ∈ N.primeFactors := by rw [hset]; exact Finset.mem_insert_self _ _
    have hqmem : q ∈ N.primeFactors := by rw [hset]; simp
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hpdvd : p ∣ N := (Nat.mem_primeFactors.mp hpmem).2.1
    have hqdvd : q ∣ N := (Nat.mem_primeFactors.mp hqmem).2.1
    -- the prime factors are odd, hence ≥ 3
    have hp_ge3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with rfl | hpo
      · have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
        have : (2 : ℕ) ∣ N := hpdvd
        omega
      · have := Nat.odd_iff.mp hpo; have := hp.two_le; omega
    have hq_ge3 : 3 ≤ q := by
      rcases hq.eq_two_or_odd' with rfl | hqo
      · have hmod : N % 2 = 1 := Nat.odd_iff.mp hodd
        have : (2 : ℕ) ∣ N := hqdvd
        omega
      · have := Nat.odd_iff.mp hqo; have := hq.two_le; omega
    set a := N.factorization p with ha
    set b := N.factorization q with hb
    -- decompose N as the coprime product pᵃ qᵇ
    have hNeq : N = p ^ a * q ^ b := by
      have h1 := Nat.factorization_prod_pow_eq_self hN
      rw [Nat.prod_factorization_eq_prod_primeFactors] at h1
      rw [hset, Finset.prod_pair hpq, ← ha, ← hb] at h1
      exact h1.symm
    have hcop : Nat.Coprime (p ^ a) (q ^ b) := ((Nat.coprime_primes hp hq).mpr hpq).pow a b
    have hσprod : σ 1 N = σ 1 (p ^ a) * σ 1 (q ^ b) := by
      rw [hNeq]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
    -- ℕ facts
    have E1n : σ 1 (p ^ a) * σ 1 (q ^ b) = 2 * (p ^ a * q ^ b) := by
      rw [← hσprod, hσ, hNeq]
    have hep := sigma_one_primePow_succ_eq (p := p) (a := a) hp
    have heq := sigma_one_primePow_succ_eq (p := q) (a := b) hq
    -- move to ℤ
    have E1 : (σ 1 (p ^ a) : ℤ) * σ 1 (q ^ b) = 2 * ((p ^ a : ℤ) * (q ^ b : ℤ)) := by
      exact_mod_cast E1n
    have E2 : (σ 1 (p ^ a) : ℤ) * p + 1 = (p ^ a : ℤ) * p + σ 1 (p ^ a) := by
      exact_mod_cast hep
    have E3 : (σ 1 (q ^ b) : ℤ) * q + 1 = (q ^ b : ℤ) * q + σ 1 (q ^ b) := by
      exact_mod_cast heq
    have hP3 : (3 : ℤ) ≤ p := by exact_mod_cast hp_ge3
    have hQ3 : (3 : ℤ) ≤ q := by exact_mod_cast hq_ge3
    have hPQne : (p : ℤ) ≠ q := by exact_mod_cast hpq
    have hA1 : (1 : ℤ) ≤ (p ^ a : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (pow_ne_zero a hp.pos.ne')
    have hB1 : (1 : ℤ) ≤ (q ^ b : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (pow_ne_zero b hq.pos.ne')
    -- sharp per-prime bounds in product form
    have ep : (σ 1 (p ^ a) : ℤ) * ((p : ℤ) - 1) = (p ^ a : ℤ) * p - 1 := by
      linear_combination E2
    have eqb : (σ 1 (q ^ b) : ℤ) * ((q : ℤ) - 1) = (q ^ b : ℤ) * q - 1 := by
      linear_combination E3
    -- multiply the two sharp bounds, substituting σ(pᵃ)σ(qᵇ) = 2 pᵃ qᵇ
    have hLHS :
        (σ 1 (p ^ a) : ℤ) * ((p : ℤ) - 1) * ((σ 1 (q ^ b) : ℤ) * ((q : ℤ) - 1))
          = 2 * (p ^ a : ℤ) * (q ^ b : ℤ) * (((p : ℤ) - 1) * ((q : ℤ) - 1)) := by
      linear_combination (((p : ℤ) - 1) * ((q : ℤ) - 1)) * E1
    have hRHS :
        (σ 1 (p ^ a) : ℤ) * ((p : ℤ) - 1) * ((σ 1 (q ^ b) : ℤ) * ((q : ℤ) - 1))
          = ((p ^ a : ℤ) * p - 1) * ((q ^ b : ℤ) * q - 1) := by
      rw [ep, eqb]
    have hR :
        2 * (p ^ a : ℤ) * (q ^ b : ℤ) * (((p : ℤ) - 1) * ((q : ℤ) - 1))
          = ((p ^ a : ℤ) * p - 1) * ((q ^ b : ℤ) * q - 1) := by
      rw [← hLHS, hRHS]
    -- the impossible inequality
    have hpqle : (p : ℤ) * q ≤ 2 * ((p : ℤ) - 1) * ((q : ℤ) - 1) := two_le_prod hP3 hQ3 hPQne
    have hABnn : (0 : ℤ) ≤ (p ^ a : ℤ) * (q ^ b : ℤ) := by positivity
    have hkey :
        (p ^ a : ℤ) * (q ^ b : ℤ) * ((p : ℤ) * q)
          ≤ (p ^ a : ℤ) * (q ^ b : ℤ) * (2 * ((p : ℤ) - 1) * ((q : ℤ) - 1)) :=
      mul_le_mul_of_nonneg_left hpqle hABnn
    nlinarith [hkey, hR, hA1, hB1, hP3, hQ3,
      mul_nonneg (show (0 : ℤ) ≤ (p ^ a : ℤ) - 1 by linarith)
        (show (0 : ℤ) ≤ (p : ℤ) - 3 by linarith),
      mul_nonneg (show (0 : ℤ) ≤ (q ^ b : ℤ) - 1 by linarith)
        (show (0 : ℤ) ≤ (q : ℤ) - 3 by linarith)]

/-- **Corollary.** An odd number with at most two distinct prime factors is not
perfect. -/
theorem not_perfect_of_odd_of_card_le_two {N : ℕ} (hodd : Odd N)
    (hcard : N.primeFactors.card ≤ 2) : ¬ N.Perfect := by
  intro hperf
  have := odd_perfect_three_primeFactors hodd hperf
  omega

end SumOfDivisorsOQ01OQ01
