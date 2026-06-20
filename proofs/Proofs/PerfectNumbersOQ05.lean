import Mathlib

/-!
# Every Prime Power is Deficient: σ(pᵏ) < 2·pᵏ

## What This Proves

A positive integer `n` is **deficient** when the sum of all its divisors falls
short of `2n`, equivalently when its *proper* divisors sum to strictly less than
`n` itself.  This file proves the full infinite family

  **for every prime `p` and every exponent `k`, the prime power `pᵏ` is deficient.**

The sum-of-divisors function on a prime power is the finite geometric series
`σ(pᵏ) = 1 + p + p² + ⋯ + pᵏ`.  The deficiency is then the elementary geometric
fact that the *lower* tail `1 + p + ⋯ + pᵏ⁻¹` is strictly smaller than the single
top term `pᵏ` (for `p ≥ 2`):

  `σ(pᵏ) = (1 + p + ⋯ + pᵏ⁻¹) + pᵏ  <  pᵏ + pᵏ = 2·pᵏ.`

## Why This Is New

The Perfect-Numbers / Sum-of-Divisors gallery family already contains:

* `prime_is_deficient` — the single case `k = 1` (`σ(p) = p + 1 < 2p`);
* `sigma_prime_pow` — the closed geometric-sum formula `σ(pᵏ) = Σ pⁱ`;
* a handful of *specific* deficient numbers (`4`, `8`, `16`, …) proved by
  `native_decide` (which is decidable computation, not a uniform argument).

What was missing is the **general, all-`k` deficiency theorem with a genuine
geometric-series proof** — a single statement covering the whole infinite family
`{pᵏ}` at once, and crucially proved *without* `native_decide`, so the result is
fully kernel-checked (0 axioms beyond Lean's logical foundations).

The load-bearing Mathlib lemma is `Nat.geomSum_lt`:
`2 ≤ m → (∀ k ∈ s, k < n) → Σ_{k ∈ s} mᵏ < mⁿ`.

## Main Results

* `geomSum_prime_pow_lt`        : `Σ_{j<k} pʲ < pᵏ`           (the geometric heart)
* `sigma_one_prime_pow_lt`      : `σ(pᵏ) < 2·pᵏ`              (sum-of-divisors form)
* `sum_properDivisors_pow_lt`   : proper divisors of `pᵏ` sum to `< pᵏ`
* `prime_pow_is_deficient`      : `IsDeficient (pᵏ)`          (the headline)
* `prime_is_deficient`          : `k = 1` corollary
* concrete instances (`8`, `16`, `9`, `81`, `2187`) derived *from the general
  theorem*, not by `native_decide`.
-/

namespace PerfectNumbersOQ05

open ArithmeticFunction Finset Nat

/-! ## The geometric heart: the lower tail is smaller than the top term -/

/-- For a prime `p` and any exponent `k`, the geometric sum of the lower powers
`1 + p + ⋯ + pᵏ⁻¹` is strictly less than the single top power `pᵏ`.

This is the engine of every deficiency statement below.  It is a direct instance
of `Nat.geomSum_lt` (which itself runs through `Nat.geomSum_eq` and the bound
`(pᵏ - 1)/(p - 1) < pᵏ`): every index `j` in `range k` satisfies `j < k`. -/
theorem geomSum_prime_pow_lt (p k : ℕ) (hp : p.Prime) :
    ∑ j ∈ range k, p ^ j < p ^ k :=
  Nat.geomSum_lt hp.two_le (fun _ hj => mem_range.mp hj)

/-! ## Sum-of-divisors form: σ(pᵏ) < 2·pᵏ -/

/-- **Every prime power is deficient (σ form).** For a prime `p` and any `k`,
`σ(pᵏ) < 2·pᵏ`.

Proof: `σ(pᵏ) = Σ_{j ∈ range (k+1)} pʲ` (Mathlib's `sigma_one_apply_prime_pow`).
Splitting off the top term `pᵏ` via `Finset.sum_range_succ` leaves the lower tail
`Σ_{j ∈ range k} pʲ`, which `geomSum_prime_pow_lt` bounds by `pᵏ`.  Hence
`σ(pᵏ) = (lower tail) + pᵏ < pᵏ + pᵏ = 2·pᵏ`. -/
theorem sigma_one_prime_pow_lt (p k : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ k) < 2 * p ^ k := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]
  have h := geomSum_prime_pow_lt p k hp
  omega

/-! ## Proper-divisor form: the proper divisors of pᵏ sum to less than pᵏ -/

/-- The proper divisors of `pᵏ` are exactly `1, p, …, pᵏ⁻¹`, and they sum to
strictly less than `pᵏ`.  This is the most concrete statement of deficiency:
*the parts are smaller than the whole.* -/
theorem sum_properDivisors_pow_lt (p k : ℕ) (hp : p.Prime) :
    ∑ d ∈ (p ^ k).properDivisors, d < p ^ k := by
  have hσ := sigma_one_prime_pow_lt p k hp
  have hsum : sigma 1 (p ^ k) = (∑ d ∈ (p ^ k).properDivisors, d) + p ^ k := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-! ## The headline: deficiency of the whole infinite family -/

/-- A number is *deficient* if the sum of its divisors is less than twice itself.
(Identical to `SumOfDivisors.IsDeficient`; restated here so this file is
self-contained.) -/
def IsDeficient (n : ℕ) : Prop := sigma 1 n < 2 * n

/-- **Main theorem.** Every prime power `pᵏ` is deficient. -/
theorem prime_pow_is_deficient (p k : ℕ) (hp : p.Prime) :
    IsDeficient (p ^ k) :=
  sigma_one_prime_pow_lt p k hp

/-- `IsDeficient pᵏ` is equivalent to "proper divisors sum to `< pᵏ`", and both
hold for every prime power.  This packages the two viewpoints. -/
theorem isDeficient_iff_sum_properDivisors_lt (n : ℕ) :
    IsDeficient n ↔ ∑ d ∈ n.properDivisors, d < n := by
  unfold IsDeficient
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-! ## Corollaries: k = 1 recovers prime deficiency -/

/-- The classical `k = 1` case: every prime is deficient (`σ(p) = p + 1 < 2p`),
recovered as a special case of the general prime-power theorem. -/
theorem prime_is_deficient (p : ℕ) (hp : p.Prime) : IsDeficient p := by
  have h := prime_pow_is_deficient p 1 hp
  simpa using h

/-! ## Concrete instances — from the general theorem, *not* `native_decide`

These witness that the infinite family produces deficient numbers without any
decidable computation: each is a substitution into `prime_pow_is_deficient`. -/

/-- `8 = 2³` is deficient (σ(8) = 15 < 16). -/
theorem eight_is_deficient : IsDeficient 8 :=
  prime_pow_is_deficient 2 3 (by norm_num)

/-- `16 = 2⁴` is deficient (σ(16) = 31 < 32). -/
theorem sixteen_is_deficient : IsDeficient 16 :=
  prime_pow_is_deficient 2 4 (by norm_num)

/-- `9 = 3²` is deficient (σ(9) = 13 < 18). -/
theorem nine_is_deficient : IsDeficient 9 :=
  prime_pow_is_deficient 3 2 (by norm_num)

/-- `81 = 3⁴` is deficient (σ(81) = 121 < 162). -/
theorem eightyone_is_deficient : IsDeficient 81 :=
  prime_pow_is_deficient 3 4 (by norm_num)

/-- `2187 = 3⁷` is deficient — an instance no `native_decide` was used to certify. -/
theorem prime_pow_3_7_is_deficient : IsDeficient (3 ^ 7) :=
  prime_pow_is_deficient 3 7 (by norm_num)

end PerfectNumbersOQ05
