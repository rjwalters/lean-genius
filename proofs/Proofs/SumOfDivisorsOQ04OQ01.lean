/-
# Sum of Divisors OQ-04-OQ-01: prime powers are deficient — never perfect, almost-perfect powers of two, sharp abundancy bound

## Open Question
OQ-04 establishes the *structural* divisor-sum identities on prime powers
(`σ(pⁱ)·(p−1) = pⁱ⁺¹−1`). The base entry classifies particular numbers as
deficient / perfect / abundant by `native_decide`. This entry proves the
*qualitative classification of every prime power*, axiom-free and once-and-for-all
in `p` and `k`:

* **Deficiency.** `σ(pᵏ) < 2·pᵏ` for every prime `p` and exponent `k`. Hence no
  prime power is perfect or abundant — it is always strictly deficient.
* **Almost-perfect powers of two.** `σ(2ᵏ) + 1 = 2·2ᵏ`: powers of two are
  deficient by *exactly one*, the smallest possible positive deficiency (this is
  the classical "almost perfect" property of `2ᵏ`).
* **No prime power is perfect.** `¬ Nat.Perfect (pᵏ)`, connecting the deficiency
  bound back to the base entry's perfection predicate.
* **Sharp abundancy bound.** Over ℚ, `σ(pᵏ)/pᵏ < p/(p−1) ≤ 2`. The bound
  `p/(p−1)` is the supremum of the abundancy index over the powers of a fixed
  prime `p` (approached as `k → ∞`), and is `≤ 2` exactly because `p ≥ 2`.

## Approach
Everything reduces to the integer identity `σ(pᵏ)·(p−1) = pᵏ⁺¹−1`
(`sigma_one_apply_prime_pow` + `geom_sum_mul`). Multiplying the target deficiency
gap by the positive quantity `p−1` turns it into `pᵏ·(p−2)+1 ≥ 1 > 0`, an
elementary nonnegativity. The abundancy bound is the same identity read over ℚ via
`div_lt_div_iff`.

Sorry-free and axiom-free (no `native_decide`).
-/
import Mathlib

namespace SumOfDivisorsOQ04OQ01

open ArithmeticFunction Finset

/-- **The defining integer identity** (OQ-04): `σ(pⁱ)·(p−1) = pⁱ⁺¹−1` over ℤ.
Restated locally as the engine for every result below. -/
theorem sigma_one_prime_pow_mul {p : ℕ} (hp : p.Prime) (i : ℕ) :
    (sigma 1 (p ^ i) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (i + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_mul]

/-- **Every prime power is deficient:** `σ(pᵏ) < 2·pᵏ` for every prime `p` and `k`.
The deficiency gap, scaled by the positive factor `p−1`, equals `pᵏ·(p−2)+1 ≥ 1`. -/
theorem sigma_one_prime_pow_deficient {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigma 1 (p ^ k) < 2 * p ^ k := by
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have key := sigma_one_prime_pow_mul hp k
  -- The deficiency gap times `(p − 1)` is `pᵏ·(p − 2) + 1`.
  have expand :
      ((2 : ℤ) * (p : ℤ) ^ k - (sigma 1 (p ^ k) : ℤ)) * ((p : ℤ) - 1)
        = (p : ℤ) ^ k * ((p : ℤ) - 2) + 1 := by
    linear_combination -key
  have hpk : (0 : ℤ) ≤ (p : ℤ) ^ k := by positivity
  have hrhs : (0 : ℤ) < (p : ℤ) ^ k * ((p : ℤ) - 2) + 1 := by
    have : (0 : ℤ) ≤ (p : ℤ) ^ k * ((p : ℤ) - 2) :=
      mul_nonneg hpk (by linarith)
    linarith
  have hp1 : (0 : ℤ) < (p : ℤ) - 1 := by linarith
  zify
  nlinarith [expand, hrhs, hp1]

/-- **Powers of two are almost perfect:** `σ(2ᵏ) + 1 = 2·2ᵏ`. The divisor sum falls
exactly one short of `2·2ᵏ` — the minimal possible positive deficiency, so `2ᵏ` is
the "least deficient" prime power. -/
theorem pow_two_almost_perfect (k : ℕ) :
    sigma 1 (2 ^ k) + 1 = 2 * 2 ^ k := by
  have key := sigma_one_prime_pow_mul Nat.prime_two k
  have hpow : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
  zify
  push_cast at key
  linarith [key, hpow]

/-- **No prime power is perfect.** Combines the deficiency bound with the base
entry's `Nat.Perfect` predicate: perfection requires `σ(n) = 2n`, which prime
powers never satisfy. -/
theorem prime_pow_not_perfect {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ¬ Nat.Perfect (p ^ k) := by
  intro hperf
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply] at hperf
  have hdef := sigma_one_prime_pow_deficient hp k
  omega

/-- **Sharp abundancy bound:** the abundancy index `σ(pᵏ)/pᵏ` of a prime power is
strictly below `p/(p−1)`. As `k → ∞` the index increases to this bound, so
`p/(p−1)` is its supremum over the powers of `p`. -/
theorem abundancy_prime_pow_lt {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (sigma 1 (p ^ k) : ℚ) / (p ^ k : ℚ) < (p : ℚ) / ((p : ℚ) - 1) := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hb : (0 : ℚ) < (p ^ k : ℚ) := by
    have : 0 < p ^ k := pow_pos hp.pos k
    exact_mod_cast this
  have hd : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  rw [div_lt_div_iff₀ hb hd]
  have key : (sigma 1 (p ^ k) : ℚ) * ((p : ℚ) - 1) = (p : ℚ) ^ (k + 1) - 1 := by
    rw [sigma_one_apply_prime_pow hp]
    push_cast
    rw [geom_sum_mul]
  rw [key]
  have hpow : (p : ℚ) ^ (k + 1) = (p : ℚ) * (p : ℚ) ^ k := by ring
  linarith [hpow]

/-- **Abundancy of a prime power is below 2** (the deficiency bound, over ℚ): since
`p ≥ 2`, the supremum `p/(p−1)` is itself `≤ 2`, so `σ(pᵏ)/pᵏ < 2`. -/
theorem abundancy_prime_pow_lt_two {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (sigma 1 (p ^ k) : ℚ) / (p ^ k : ℚ) < 2 := by
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hd : (0 : ℚ) < (p : ℚ) - 1 := by linarith
  have hsup : (p : ℚ) / ((p : ℚ) - 1) ≤ 2 := by
    rw [div_le_iff₀ hd]
    linarith
  exact lt_of_lt_of_le (abundancy_prime_pow_lt hp k) hsup

/-- **Divisor count of a prime power:** `τ(pᵏ) = k + 1` (bonus structural identity,
generalising OQ-04's `τ(p) = 2`). -/
theorem sigma_zero_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sigma 0 (p ^ k) = k + 1 := by
  rw [sigma_zero_apply_prime_pow hp]

end SumOfDivisorsOQ04OQ01
