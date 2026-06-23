import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-
# Symbolic prime-power values of Jacobi's σ* (OQ-06 of FourSquareDistribution)

## Open Question (Gallery OQ-06 of `four-square-distribution`)
"Can the type-decomposition compute r₄(p²) symbolically as a function of an
odd prime p, matching Jacobi's prediction r₄(p²) = 8·(1 + p + p²)?
For p = 3 this gives 8·13 = 104, matching the verified `r₄_9_distribution`."

## What this provides

The parent family `FourSquareDistribution*` verifies Jacobi's prediction
`jacobiR4 n = 8·σ*(n)` only at individual numerical values `n = 1,…,10`,
each discharged by `native_decide`. Those proofs evaluate the modified
divisor sum

  σ*(n) = Σ_{d | n, 4 ∤ d} d              (`FourSquareDistributionOQ01.sigmaStar`)

at a *fixed* `n`; they say nothing about a general `n`.

This file replaces the table with **closed-form, `native_decide`-free,
0-axiom theorems** for two infinite families:

* `sigmaStar_odd_prime_pow` — for an odd prime `p`, σ*(pᵏ) is the full
  geometric divisor sum `1 + p + ⋯ + pᵏ` (no divisor of an odd number is
  divisible by 4, so σ* drops nothing).
* `sigmaStar_prime_sq`, `jacobiR4_prime_sq` — the headline OQ-06 identity
  `jacobiR4 (p²) = 8·(1 + p + p²)` for every odd prime `p`.
* `sigmaStar_two_pow`, `jacobiR4_two_pow` — the *even* prime powers: σ*(2ᵏ)
  is constantly `3` for `k ≥ 1` (only the divisors `1` and `2` survive),
  so `jacobiR4 (2ᵏ) = 24`. This explains the repeated `24` at
  `n = 2, 4, 8` in the parent table.
* `sigmaStar_eq_sumDivisors_of_odd` — the structural reason: on odd inputs
  σ* coincides with the ordinary sum-of-divisors function σ.

`jacobiR4_nine` then recovers the gallery's `jacobiR4 9 = 104` symbolically,
as the `p = 3` instance of `jacobiR4_prime_sq`, with no `native_decide`.

## Honest scope

`jacobiR4` is *defined* as `8·σ*`; these theorems compute that prediction
symbolically. They do **not** prove the geometric count
r₄(n) = #{(a,b,c,d) : a²+b²+c²+d² = n} equals `jacobiR4 n` — that is the
genuinely open `jacobi_r4_formula` of OQ-01, which needs the q-expansion of
`jacobiTheta⁴`. The contribution here is purely the arithmetic side, and it
is fully machine-checked with no axioms beyond Lean's foundations.
-/

namespace FourSquareDistributionOQ06

open Finset Nat

/-- Jacobi's modified divisor sum `σ*(n) = Σ_{d | n, 4 ∤ d} d`.

    This is the identical definition to `FourSquareDistributionOQ01.sigmaStar`;
    it is restated here so this file verifies standalone (against Mathlib only)
    while the theorems below give the symbolic closed forms that the parent
    family establishes only at individual `native_decide`-checked values. -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d

/-- Jacobi's prediction `r₄(n) = 8·σ*(n)` (same definition as
    `FourSquareDistributionOQ01.jacobiR4`). -/
def jacobiR4 (n : ℕ) : ℕ := 8 * sigmaStar n

-- =====================================================================
-- PART 1: σ* on odd prime powers is the full geometric divisor sum
-- =====================================================================

/-- For an odd prime `p`, no divisor of `pᵏ` is divisible by `4`, so
    Jacobi's modified divisor sum σ*(pᵏ) keeps every divisor and equals the
    geometric sum `Σ_{i=0}^{k} pⁱ`. -/
theorem sigmaStar_odd_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    sigmaStar (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  unfold sigmaStar
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Function.Embedding.coeFn_mk]
  rw [if_neg]
  -- `4 ∣ pⁱ` is impossible: `pⁱ` is odd.
  intro h4
  have hoi : p ^ i % 2 = 1 := Nat.odd_iff.mp hodd.pow
  obtain ⟨c, hc⟩ := h4
  omega

/-- The headline OQ-06 σ* value: `σ*(p²) = 1 + p + p²` for every odd prime. -/
theorem sigmaStar_prime_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    sigmaStar (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigmaStar_odd_prime_pow hp hp2]
  simp [Finset.sum_range_succ]

/-- The `k = 1` instance: `σ*(p) = 1 + p` for an odd prime. -/
theorem sigmaStar_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    sigmaStar p = 1 + p := by
  have h := sigmaStar_odd_prime_pow hp hp2 1
  rw [pow_one] at h
  rw [h]
  simp [Finset.sum_range_succ]

-- =====================================================================
-- PART 2: Jacobi's prediction on odd prime powers
-- =====================================================================

/-- **OQ-06 headline.** Jacobi's prediction at an odd prime square:
    `jacobiR4 (p²) = 8·(1 + p + p²)`, a symbolic function of `p`. -/
theorem jacobiR4_prime_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiR4 (p ^ 2) = 8 * (1 + p + p ^ 2) := by
  unfold jacobiR4
  rw [sigmaStar_prime_sq hp hp2]

/-- Symbolic recovery of the gallery's `jacobiR4 9 = 104`, as the `p = 3`
    instance of the closed form — proved with no `native_decide`. -/
theorem jacobiR4_nine : jacobiR4 (3 ^ 2) = 104 := by
  rw [jacobiR4_prime_sq (by norm_num) (by norm_num)]
  norm_num

-- =====================================================================
-- PART 3: σ* on even prime powers is eventually constant
-- =====================================================================

/-- The summand of σ*(2ᵏ) after expanding the divisors of `2ᵏ`. -/
private theorem sumg_two_pow {k : ℕ} (hk : 1 ≤ k) :
    ∑ i ∈ Finset.range (k + 1), (if 4 ∣ 2 ^ i then 0 else 2 ^ i) = 3 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Finset.sum_range_succ, ih]
    have h4 : (4 : ℕ) ∣ 2 ^ (k + 1) := by
      have : (2 : ℕ) ^ 2 ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
      simpa using this
    rw [if_pos h4]

/-- For `k ≥ 1` only the divisors `1` and `2` of `2ᵏ` escape divisibility by
    `4`, so `σ*(2ᵏ) = 3` is constant. This is the reason the parent table
    shows the same value at `n = 2, 4, 8`. -/
theorem sigmaStar_two_pow {k : ℕ} (hk : 1 ≤ k) : sigmaStar (2 ^ k) = 3 := by
  unfold sigmaStar
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  exact sumg_two_pow hk

/-- Jacobi's prediction is constant on the even prime powers:
    `jacobiR4 (2ᵏ) = 24` for every `k ≥ 1`. -/
theorem jacobiR4_two_pow {k : ℕ} (hk : 1 ≤ k) : jacobiR4 (2 ^ k) = 24 := by
  unfold jacobiR4
  rw [sigmaStar_two_pow hk]

-- =====================================================================
-- PART 4: structural reason — σ* = σ on odd inputs
-- =====================================================================

/-- On any odd number `n`, every divisor is odd, hence not divisible by `4`,
    so Jacobi's modified divisor sum coincides with the ordinary
    sum-of-divisors function: `σ*(n) = Σ_{d | n} d`. -/
theorem sigmaStar_eq_sumDivisors_of_odd {n : ℕ} (hn : Odd n) :
    sigmaStar n = ∑ d ∈ n.divisors, d := by
  unfold sigmaStar
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [if_neg]
  intro h4
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have h2n : (2 : ℕ) ∣ n := dvd_trans (dvd_trans (by norm_num) h4) hdn
  obtain ⟨c, hc⟩ := h2n
  have : n % 2 = 1 := Nat.odd_iff.mp hn
  omega

end FourSquareDistributionOQ06
