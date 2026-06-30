import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-
# Explicit growth bounds for the totient of a prime power

**Open question (`euler-totient-oq-09-oq-02`).** The parent entry
`euler-totient-oq-09` establishes the power law `φ(nᵏ) = nᵏ⁻¹·φ(n)`, and Mathlib
records the exact prime-power *value*
`Nat.totient_prime_pow_succ : φ(p^(n+1)) = pⁿ·(p−1)`.  What neither states is how
fast a prime-power totient actually *grows* — its density relative to `pᵏ`, its
multiplicative growth rate, and the two-sided envelope trapping it.  This entry
collects those quantitative facts.

For a prime `p` and exponent `k = n + 1 ≥ 1` we prove:

* **Exact density** `p · φ(pᵏ) = (p−1) · pᵏ`, i.e. `φ(pᵏ)/pᵏ = 1 − 1/p`
  (`totient_prime_pow_density`).
* **Density is independent of the exponent**: the cross-ratio
  `p^j · φ(pᵏ) = pᵏ · φ(pʲ)` holds for all `j, k ≥ 1`
  (`totient_density_independent_of_exponent`) — the relative size `1 − 1/p`
  does not depend on how high the power is.
* **Geometric growth** with ratio exactly `p`: `φ(p^(k+1)) = p · φ(pᵏ)`
  (`totient_prime_pow_ratio`).
* **Two-sided envelope** `pᵏ ≤ 2·φ(pᵏ)` and `φ(pᵏ) < pᵏ`
  (`two_mul_totient_prime_pow_ge`, `totient_prime_pow_lt`): the totient sits in
  the band `[pᵏ/2, pᵏ)`.
* **Base-power floor** `pᵏ⁻¹ ≤ φ(pᵏ)` (`base_pow_le_totient_prime_pow`).
* **Square-root floor** `pᵏ ≤ φ(pᵏ)²` for `k ≥ 2`
  (`sq_prime_pow_le_totient_sq`): for genuine prime powers `φ(pᵏ) ≥ √(pᵏ)`,
  the classical `φ(m) ≥ √m` bound specialised to prime powers.

Everything reduces to `Nat.totient_prime_pow_succ` plus elementary arithmetic, so
the whole file is machine-checked with 0 sorries and 0 axioms.

`φ` is `Nat.totient` throughout.
-/

namespace EulerTotientOQ09OQ02

open Nat

variable {p : ℕ}

/-- **Exact density.** For a prime `p` and any exponent `k = n+1 ≥ 1`,
`p · φ(pᵏ) = (p−1) · pᵏ`; equivalently the density `φ(pᵏ)/pᵏ = (p−1)/p = 1 − 1/p`.
The right-hand side has no dependence on `n` beyond the leading `pᵏ`, so the
density is the constant `1 − 1/p` for every exponent. -/
theorem totient_prime_pow_density (hp : p.Prime) (n : ℕ) :
    p * φ (p ^ (n + 1)) = (p - 1) * p ^ (n + 1) := by
  rw [totient_prime_pow_succ hp]
  ring

/-- **The density is independent of the exponent.** For a prime `p` and exponents
`j+1, k+1 ≥ 1`, the cross-ratio `p^(j+1) · φ(p^(k+1)) = p^(k+1) · φ(p^(j+1))`
holds, i.e. `φ(p^(k+1))/p^(k+1) = φ(p^(j+1))/p^(j+1)`. Both sides equal
`p^(j+k+1)·(p−1)`. The relative size of the totient does not grow with the power. -/
theorem totient_density_independent_of_exponent (hp : p.Prime) (j k : ℕ) :
    p ^ (j + 1) * φ (p ^ (k + 1)) = p ^ (k + 1) * φ (p ^ (j + 1)) := by
  rw [totient_prime_pow_succ hp, totient_prime_pow_succ hp]
  ring

/-- **Geometric growth with ratio exactly `p`.** `φ(p^(k+1)) = p · φ(pᵏ)`:
raising the exponent by one multiplies the totient by `p`. -/
theorem totient_prime_pow_ratio (hp : p.Prime) (n : ℕ) :
    φ (p ^ (n + 2)) = p * φ (p ^ (n + 1)) := by
  rw [totient_prime_pow_succ hp, totient_prime_pow_succ hp]
  ring

/-- **Lower envelope `pᵏ/2`.** `pᵏ ≤ 2·φ(pᵏ)` for any exponent `k = n+1 ≥ 1`.
Since `φ(pᵏ) = pᵏ⁻¹(p−1)` and `p ≥ 2` forces `p ≤ 2(p−1)`, the totient never drops
below half of `pᵏ`. -/
theorem two_mul_totient_prime_pow_ge (hp : p.Prime) (n : ℕ) :
    p ^ (n + 1) ≤ 2 * φ (p ^ (n + 1)) := by
  rw [totient_prime_pow_succ hp]
  have h2 : 2 ≤ p := hp.two_le
  calc p ^ (n + 1) = p ^ n * p := by ring
    _ ≤ p ^ n * (2 * (p - 1)) := by gcongr; omega
    _ = 2 * (p ^ n * (p - 1)) := by ring

/-- **Strict upper envelope.** `φ(pᵏ) < pᵏ` for any exponent `k = n+1 ≥ 1`,
directly from `Nat.totient_lt` since `pᵏ > 1`. -/
theorem totient_prime_pow_lt (hp : p.Prime) (n : ℕ) :
    φ (p ^ (n + 1)) < p ^ (n + 1) :=
  Nat.totient_lt _ (Nat.one_lt_pow (Nat.succ_ne_zero n) hp.one_lt)

/-- **Base-power floor.** `pᵏ⁻¹ ≤ φ(pᵏ)` for `k = n+1 ≥ 1`: the totient is at least
the next-lower power, since `φ(pᵏ) = pᵏ⁻¹(p−1)` and `p − 1 ≥ 1`. -/
theorem base_pow_le_totient_prime_pow (hp : p.Prime) (n : ℕ) :
    p ^ n ≤ φ (p ^ (n + 1)) := by
  rw [totient_prime_pow_succ hp]
  have h2 : 2 ≤ p := hp.two_le
  calc p ^ n = p ^ n * 1 := (mul_one _).symm
    _ ≤ p ^ n * (p - 1) := by gcongr; omega

/-- **Square-root floor.** For exponent `k = n+2 ≥ 2`, `pᵏ ≤ φ(pᵏ)²`, i.e.
`φ(pᵏ) ≥ √(pᵏ)`. This is the classical lower bound `φ(m) ≥ √m` (valid for
`m ≠ 2, 6`) specialised to genuine prime powers. The proof chains the base-power
floor `pᵏ⁻¹ ≤ φ(pᵏ)` with `pᵏ ≤ (pᵏ⁻¹)²` (which holds because `k ≤ 2(k−1)` once
`k ≥ 2`). -/
theorem sq_prime_pow_le_totient_sq (hp : p.Prime) (n : ℕ) :
    p ^ (n + 2) ≤ φ (p ^ (n + 2)) ^ 2 := by
  have h2 : 2 ≤ p := hp.two_le
  have hbase : p ^ (n + 1) ≤ φ (p ^ (n + 2)) := base_pow_le_totient_prime_pow hp (n + 1)
  calc p ^ (n + 2)
      ≤ (p ^ (n + 1)) ^ 2 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ φ (p ^ (n + 2)) ^ 2 := Nat.pow_le_pow_left hbase 2

/-- **Numeric sanity check.** `φ(2¹⁰) = 512 = 2⁹·(2−1)`. -/
theorem totient_two_pow_ten : φ (2 ^ 10) = 512 := by
  rw [show (10 : ℕ) = 9 + 1 from rfl, totient_prime_pow_succ Nat.prime_two]
  norm_num

/-- **Numeric sanity check.** `φ(3⁴) = 54 = 3³·(3−1)`, and `54² = 2916 ≥ 81 = 3⁴`
illustrates the square-root floor. -/
theorem totient_three_pow_four : φ (3 ^ 4) = 54 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, totient_prime_pow_succ (by norm_num)]
  norm_num

end EulerTotientOQ09OQ02
