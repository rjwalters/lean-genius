import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-
# Symbolic prime-power values of the r₂ arithmetic side (OQ-06-OQ-03 of FourSquareDistribution)

## Open Question (Gallery OQ-06-OQ-03 of `four-square-distribution`)
"Do the sibling sum-of-squares counts admit analogous `native_decide`-free closed forms on
prime powers?  Jacobi's r₂, r₆, r₈ … are also expressed through (modified) divisor sums; the
same `divisors_prime_pow` + parity strategy may yield symbolic prime-power values for those
families."

## What this provides

The parent `FourSquareDistributionOQ06` computes symbolic prime-power values of Jacobi's
`σ*` divisor sum, the arithmetic side of the **four**-square count r₄.  This file carries out
the same programme one exponent down, for the **two**-square count r₂, whose arithmetic side
is Jacobi's classical two-square formula

  r₂(n) = 4 · Σ_{d ∣ n} χ₄(d),

where `χ₄` is Mathlib's primitive quadratic character mod 4
(`χ₄(d) = 0, 1, −1` according as `d` is even, `≡ 1`, `≡ 3 (mod 4)`).  Writing

  `chiSum n = Σ_{d ∣ n} χ₄(d)`      and      `jacobiR2 n = 4 · chiSum n`,

we give closed forms on every prime power, split by the residue of the prime mod 4 — exactly
the trichotomy that governs which primes are sums of two squares:

* `chiSum_two_pow` — `chiSum (2ᵏ) = 1`: every proper power of 2 is even, so `χ₄` kills all
  divisors except `1`.  Hence `jacobiR2 (2ᵏ) = 4`.
* `chiSum_prime_pow_one_mod_four` — for `p ≡ 1 (mod 4)`, `χ₄(pⁱ) = 1` for all `i`, so
  `chiSum (pᵏ) = k + 1` and `jacobiR2 (pᵏ) = 4(k+1)`.  (Split primes contribute a full ramp.)
* `chiSum_prime_pow_three_mod_four` — for `p ≡ 3 (mod 4)`, `χ₄(pⁱ) = (−1)ⁱ`, an alternating
  sum, so `chiSum (pᵏ) = 1` if `k` even and `0` if `k` odd; hence `jacobiR2 (pᵏ)` is `4` or `0`.
  (Inert primes: `pᵏ` is a sum of two squares iff `k` is even.)

The numeric corollaries `jacobiR2_five/nine/three/eight` recover the small two-square counts
r₂(5)=8, r₂(9)=4, r₂(3)=0, r₂(8)=4 symbolically, as instances of the three families rather
than by `native_decide`.

## Honest scope

`jacobiR2` is *defined* as `4 · Σ χ₄(d)`; these theorems compute that arithmetic side
symbolically on prime powers.  They do **not** prove the geometric identity
r₂(n) = #{(a,b) ∈ ℤ² : a²+b² = n} equals `jacobiR2 n` (Jacobi's two-square theorem) — that,
like the parent's r₄ identity, is the genuinely open direction.  The contribution here is the
arithmetic closed forms, fully machine-checked with no axioms and no `native_decide`.
-/

namespace FourSquareDistributionOQ06OQ03

open Finset ZMod

/-- The arithmetic side of Jacobi's two-square formula:
    `chiSum n = Σ_{d ∣ n} χ₄(d)`, so Jacobi's prediction reads `r₂(n) = 4 · chiSum n`.
    Here `χ₄` is Mathlib's primitive quadratic character mod 4. -/
def chiSum (n : ℕ) : ℤ := ∑ d ∈ n.divisors, χ₄ (d : ZMod 4)

/-- Jacobi's prediction for the two-square count, `r₂(n) = 4 · Σ_{d ∣ n} χ₄(d)`. -/
def jacobiR2 (n : ℕ) : ℤ := 4 * chiSum n

-- =====================================================================
-- PART 0: base value
-- =====================================================================

/-- `chiSum 1 = 1`: the sole divisor of `1` is `1`, and `χ₄(1) = 1`.  Hence `jacobiR2 1 = 4`,
    matching r₂(1) = #{(±1,0),(0,±1)} = 4. -/
theorem chiSum_one : chiSum 1 = 1 := by
  simp [chiSum]

-- =====================================================================
-- PART 1: even prime powers — χ₄ kills everything but the unit divisor
-- =====================================================================

/-- **Powers of two.** Every divisor of `2ᵏ` other than `1` is even, so `χ₄` sends it to `0`;
    the modified divisor sum collapses to `χ₄(1) = 1`.  Thus `chiSum (2ᵏ) = 1` for all `k`. -/
theorem chiSum_two_pow (k : ℕ) : chiSum (2 ^ k) = 1 := by
  unfold chiSum
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.sum_eq_single 0]
  · -- value at i = 0 : χ₄(2⁰) = χ₄(1) = 1
    simp
  · -- every other term vanishes : χ₄(2ⁱ) = 0 for i ≠ 0 since 2ⁱ is even
    intro i _ hi
    have h2 : 2 ^ i % 2 = 0 := by
      have : (2 : ℕ) ∣ 2 ^ i := dvd_pow_self 2 hi
      omega
    rw [χ₄_nat_eq_if_mod_four, if_pos h2]
  · -- 0 always lies in range (k+1)
    intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h

-- =====================================================================
-- PART 2: odd prime powers, split prime  p ≡ 1 (mod 4)
-- =====================================================================

/-- **Split primes `p ≡ 1 (mod 4)`.** Here `χ₄(p) = 1`, so `χ₄(pⁱ) = 1ⁱ = 1` for every `i`,
    and the divisor sum is the full ramp `chiSum (pᵏ) = k + 1`. -/
theorem chiSum_prime_pow_one_mod_four {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (k : ℕ) :
    chiSum (p ^ k) = (k : ℤ) + 1 := by
  unfold chiSum
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hval : ∀ i ∈ Finset.range (k + 1), χ₄ ((p ^ i : ℕ) : ZMod 4) = 1 := by
    intro i _
    push_cast
    rw [map_pow, χ₄_nat_one_mod_four hp1, one_pow]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, Finset.card_range]
  simp

-- =====================================================================
-- PART 3: odd prime powers, inert prime  p ≡ 3 (mod 4)
-- =====================================================================

/-- **Inert primes `p ≡ 3 (mod 4)`.** Here `χ₄(p) = −1`, so `χ₄(pⁱ) = (−1)ⁱ` alternates and
    the divisor sum telescopes to `1` when `k` is even and `0` when `k` is odd.  This is the
    arithmetic shadow of "`pᵏ` is a sum of two squares iff `k` is even". -/
theorem chiSum_prime_pow_three_mod_four {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (k : ℕ) :
    chiSum (p ^ k) = if Even k then 1 else 0 := by
  unfold chiSum
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hval : ∀ i ∈ Finset.range (k + 1), χ₄ ((p ^ i : ℕ) : ZMod 4) = (-1 : ℤ) ^ i := by
    intro i _
    push_cast
    rw [map_pow, χ₄_nat_three_mod_four hp3]
  rw [Finset.sum_congr rfl hval, neg_one_geom_sum]
  -- reconcile `if Even (k+1) then 0 else 1` with `if Even k then 1 else 0`
  by_cases hk : Even k
  · rw [if_pos hk, if_neg (by rw [Nat.even_add_one]; exact not_not.mpr hk)]
  · rw [if_neg hk, if_pos (Nat.even_add_one.mpr hk)]

-- =====================================================================
-- PART 4: Jacobi's r₂ prediction (= 4 · chiSum) on prime powers
-- =====================================================================

/-- `jacobiR2 (2ᵏ) = 4` for every `k`. -/
theorem jacobiR2_two_pow (k : ℕ) : jacobiR2 (2 ^ k) = 4 := by
  unfold jacobiR2; rw [chiSum_two_pow]; norm_num

/-- `jacobiR2 (pᵏ) = 4(k+1)` for a split prime `p ≡ 1 (mod 4)`. -/
theorem jacobiR2_prime_pow_one_mod_four {p : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (k : ℕ) :
    jacobiR2 (p ^ k) = 4 * ((k : ℤ) + 1) := by
  unfold jacobiR2; rw [chiSum_prime_pow_one_mod_four hp hp1]

/-- `jacobiR2 (pᵏ) = 4` (k even) or `0` (k odd) for an inert prime `p ≡ 3 (mod 4)`. -/
theorem jacobiR2_prime_pow_three_mod_four {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (k : ℕ) :
    jacobiR2 (p ^ k) = if Even k then 4 else 0 := by
  unfold jacobiR2
  rw [chiSum_prime_pow_three_mod_four hp hp3, mul_ite, mul_one, mul_zero]

-- =====================================================================
-- PART 5: numeric recoveries (no native_decide) of small two-square counts
-- =====================================================================

/-- r₂(5) = 8, as the `p = 5 ≡ 1, k = 1` instance. -/
theorem jacobiR2_five : jacobiR2 5 = 8 := by
  have h := jacobiR2_prime_pow_one_mod_four (p := 5) (by norm_num) (by norm_num) 1
  simpa using h

/-- r₂(9) = 4, as the `p = 3 ≡ 3, k = 2` (even) instance. -/
theorem jacobiR2_nine : jacobiR2 9 = 4 := by
  have h := jacobiR2_prime_pow_three_mod_four (p := 3) (by norm_num) (by norm_num) 2
  norm_num at h
  simpa using h

/-- r₂(3) = 0, as the `p = 3 ≡ 3, k = 1` (odd) instance. -/
theorem jacobiR2_three : jacobiR2 3 = 0 := by
  have h := jacobiR2_prime_pow_three_mod_four (p := 3) (by norm_num) (by norm_num) 1
  norm_num at h
  simpa using h

/-- r₂(8) = 4, as the `2³` instance. -/
theorem jacobiR2_eight : jacobiR2 8 = 4 := by
  have h := jacobiR2_two_pow 3
  norm_num at h
  simpa using h

end FourSquareDistributionOQ06OQ03
