/-
  Abundant numbers OQ03-OQ03 satellite: every odd abundant number has at
  least three distinct prime factors.

  The tracker's session-sized follow-up to the completed infinitude result
  (`OddPrimitiveAbundant.Infinite`, PR #43297): with at most two odd prime
  divisors the abundancy index is below `(3/2)·(5/4) = 15/8 < 2`, so an odd
  abundant number needs `ω(n) ≥ 3`.  (The bound is sharp: `945 = 3³·5·7` has
  exactly three.)

  Everything is carried out in subtraction-safe ℕ arithmetic:

  * `pred_mul_geom_sum_add_one` — `(p−1)·(1 + p + ⋯ + p^a) + 1 = p^(a+1)`.
  * `pred_mul_sum_divisors_prime_pow_lt` — `(p−1)·σ(p^a) < p·p^a`.
  * `pred_prod_mul_sum_divisors_lt` — for `n ≥ 2`,
    `(∏_{p ∣ n} (p−1))·σ(n) < (∏_{p ∣ n} p)·n`, the ℕ-arithmetic form of the
    strict abundancy bound `σ(n)/n < ∏_{p ∣ n} p/(p−1)`; proved by
    `Nat.recOnPosPrimePosCoprime` with `σ` multiplicativity on the coprime
    step.
  * `three_le_primeFactors_card_of_odd_abundant` — the headline: `Odd n` and
    `n.Abundant` force `3 ≤ n.primeFactors.card`.  With `|primeFactors| ≤ 2`
    and every prime factor `≥ 3` (oddness), `∏ p ≤ 2·∏(p−1)` — the
    `card = 2` case is exactly `(p−2)(q−2) ≥ 2` for distinct odd primes —
    whence `σ(n) < 2n`, contradicting abundance.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: classical; see Dickson, "Finiteness of the odd perfect and
  primitive abundant numbers with n distinct prime factors" (1913).
-/
import Mathlib

namespace AbundantNumberOQ03OQ03

open Nat Finset

/-- **Geometric-sum identity, subtraction-safe**:
`(p − 1) · (1 + p + ⋯ + p^a) + 1 = p^(a+1)` for `1 ≤ p`. -/
theorem pred_mul_geom_sum_add_one {p : ℕ} (hp : 1 ≤ p) (a : ℕ) :
    (p - 1) * (∑ i ∈ Finset.range (a + 1), p ^ i) + 1 = p ^ (a + 1) := by
  induction a with
  | zero =>
      simp only [Finset.range_one, Finset.sum_singleton, pow_zero, pow_one, mul_one]
      omega
  | succ a ih =>
      rw [Finset.sum_range_succ, mul_add]
      have h1 : (p - 1) * p ^ (a + 1) + p ^ (a + 1) = p ^ (a + 1 + 1) := by
        have hpp : (p - 1) + 1 = p := by omega
        calc (p - 1) * p ^ (a + 1) + p ^ (a + 1)
            = ((p - 1) + 1) * p ^ (a + 1) := by ring
          _ = p * p ^ (a + 1) := by rw [hpp]
          _ = p ^ (a + 1 + 1) := by ring
      linarith [ih, h1]

/-- **Strict prime-power abundancy bound**: `(p − 1) · σ(p^a) < p · p^a` —
the ℕ-arithmetic form of `σ(p^a)/p^a < p/(p−1)`. -/
theorem pred_mul_sum_divisors_prime_pow_lt {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (p - 1) * (∑ d ∈ (p ^ a).divisors, d) < p * p ^ a := by
  rw [Nat.sum_divisors_prime_pow hp]
  have h := pred_mul_geom_sum_add_one hp.one_lt.le a
  have h2 : p * p ^ a = p ^ (a + 1) := by ring
  linarith [h, h2]

/-- **Strict abundancy-index product bound**: for `n ≥ 2`,

    `(∏_{p ∈ primeFactors n} (p − 1)) · σ(n) < (∏_{p ∈ primeFactors n} p) · n`,

the ℕ-arithmetic form of `σ(n)/n < ∏_{p ∣ n} p/(p−1)`.  Induction over the
factorization (`Nat.recOnPosPrimePosCoprime`): prime powers are the previous
lemma; on coprime products both sides factor (σ is multiplicative, prime
factors split as a disjoint union) and the strict inequalities multiply. -/
theorem pred_prod_mul_sum_divisors_lt {n : ℕ} (hn : 2 ≤ n) :
    (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      < (∏ p ∈ n.primeFactors, p) * n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
      have hpp : p.Prime := hp.nat_prime
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [Nat.primeFactors_pow_succ, hpp.primeFactors,
        Finset.prod_singleton, Finset.prod_singleton]
      exact pred_mul_sum_divisors_prime_pow_lt hpp (m + 1)
  | zero => exact absurd hn (by omega)
  | one => exact absurd hn (by omega)
  | coprime a b ha hb hab iha ihb =>
      have hkeya := iha (by omega)
      have hkeyb := ihb (by omega)
      rw [hab.primeFactors_mul,
        Finset.prod_union hab.disjoint_primeFactors,
        Finset.prod_union hab.disjoint_primeFactors]
      have hσ : (∑ d ∈ (a * b).divisors, d)
          = (∑ d ∈ a.divisors, d) * (∑ d ∈ b.divisors, d) := by
        rw [← ArithmeticFunction.sigma_one_apply, ← ArithmeticFunction.sigma_one_apply,
          ← ArithmeticFunction.sigma_one_apply]
        exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hab
      rw [hσ]
      have h1 := mul_lt_mul'' hkeya hkeyb (Nat.zero_le _) (Nat.zero_le _)
      calc (∏ p ∈ a.primeFactors, (p - 1)) * (∏ p ∈ b.primeFactors, (p - 1))
            * ((∑ d ∈ a.divisors, d) * (∑ d ∈ b.divisors, d))
          = (∏ p ∈ a.primeFactors, (p - 1)) * (∑ d ∈ a.divisors, d)
            * ((∏ p ∈ b.primeFactors, (p - 1)) * (∑ d ∈ b.divisors, d)) := by ring
        _ < (∏ p ∈ a.primeFactors, p) * a * ((∏ p ∈ b.primeFactors, p) * b) := h1
        _ = (∏ p ∈ a.primeFactors, p) * (∏ p ∈ b.primeFactors, p) * (a * b) := by ring

/-- **Every odd abundant number has at least three distinct prime factors.**

With at most two prime factors, all `≥ 3` by oddness, the product bound gives
`∏ p ≤ 2·∏(p − 1)` (the two-prime case is `(p−2)(q−2) ≥ 2` for distinct odd
primes), and the strict abundancy bound then forces `σ(n) < 2n` — contradicting
abundance.  Sharp: `945 = 3³·5·7` is odd abundant with exactly three. -/
theorem three_le_primeFactors_card_of_odd_abundant {n : ℕ}
    (hodd : Odd n) (hab : n.Abundant) :
    3 ≤ n.primeFactors.card := by
  by_contra hcard
  have hc2 : n.primeFactors.card ≤ 2 := by omega
  have habs : 2 * n < ∑ d ∈ n.divisors, d := Nat.abundant_iff_sum_divisors.mp hab
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n < 2 := by omega
    interval_cases n
    · norm_num [Nat.divisors_zero] at habs
    · norm_num [Nat.divisors_one] at habs
  have hodd_p : ∀ p ∈ n.primeFactors, 3 ≤ p := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      have h1 : n % 2 = 1 := Nat.odd_iff.mp hodd
      omega
    have := hprime.two_le
    omega
  have hprod : (∏ p ∈ n.primeFactors, p) ≤ 2 * ∏ p ∈ n.primeFactors, (p - 1) := by
    have hc : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1
        ∨ n.primeFactors.card = 2 := by omega
    rcases hc with hc | hc | hc
    · rw [Finset.card_eq_zero.mp hc]
      simp
    · obtain ⟨p, hP⟩ := Finset.card_eq_one.mp hc
      have hp3 : 3 ≤ p := hodd_p p (by rw [hP]; exact Finset.mem_singleton_self p)
      rw [hP, Finset.prod_singleton, Finset.prod_singleton]
      omega
    · obtain ⟨p, q, hpq, hP⟩ := Finset.card_eq_two.mp hc
      have hp3 : 3 ≤ p := hodd_p p (by rw [hP]; simp)
      have hq3 : 3 ≤ q := hodd_p q (by rw [hP]; simp)
      rw [hP, Finset.prod_insert (by simp [hpq]), Finset.prod_singleton,
        Finset.prod_insert (by simp [hpq]), Finset.prod_singleton]
      -- `p·q ≤ 2·(p−1)·(q−1)` for distinct primes `≥ 3`: `(p−2)(q−2) ≥ 2`.
      obtain ⟨s, rfl⟩ : ∃ s, p = s + 3 := ⟨p - 3, by omega⟩
      obtain ⟨t, rfl⟩ : ∃ t, q = t + 3 := ⟨q - 3, by omega⟩
      have hst : 1 ≤ s + t := by omega
      have hsub1 : s + 3 - 1 = s + 2 := by omega
      have hsub2 : t + 3 - 1 = t + 2 := by omega
      rw [hsub1, hsub2]
      nlinarith
  have hkey := pred_prod_mul_sum_divisors_lt hn2
  have h2 : (∏ p ∈ n.primeFactors, p) * n ≤ 2 * (∏ p ∈ n.primeFactors, (p - 1)) * n :=
    Nat.mul_le_mul_right n hprod
  have h3 : (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
      < (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by
    calc (∏ p ∈ n.primeFactors, (p - 1)) * (∑ d ∈ n.divisors, d)
        < (∏ p ∈ n.primeFactors, p) * n := hkey
      _ ≤ 2 * (∏ p ∈ n.primeFactors, (p - 1)) * n := h2
      _ = (∏ p ∈ n.primeFactors, (p - 1)) * (2 * n) := by ring
  have h4 : (∑ d ∈ n.divisors, d) < 2 * n := Nat.lt_of_mul_lt_mul_left h3
  omega

/-- Sanity anchor: the bound is attained — `945` is odd, abundant, and has
exactly three distinct prime factors (`3, 5, 7`). -/
example : (945 : ℕ).primeFactors.card = 3 := by decide

end AbundantNumberOQ03OQ03
