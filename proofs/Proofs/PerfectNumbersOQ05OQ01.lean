import Mathlib

/-!
# Quantifying the deficiency of a prime power: `2·pᵏ − σ(pᵏ) = pᵏ − (pᵏ − 1)/(p − 1)`

## What This Proves

The parent entry (*Every Prime Power is Deficient*, `perfect-numbers-oq-05`) proves the
**inequality** `σ(pᵏ) < 2·pᵏ`: every prime power is deficient. Its first open question
asks to go from the inequality to the **exact size of the gap** — the *deficiency*

  `deficiency(n) := 2·n − σ(n)`.

This file computes that gap in closed form for every prime power and records its sharp
consequences:

  **`deficiency(pᵏ) = pᵏ − (1 + p + ⋯ + pᵏ⁻¹) = pᵏ − (pᵏ − 1)/(p − 1).`**

The gap is exactly the single top power `pᵏ` minus the geometric lower tail. Two facts
fall out immediately:

* **It is always at least `1`** — a quantitative refinement of "deficient" (`< 2pᵏ`) into
  "deficient by a definite amount".
* **For `p = 2` it is *exactly* `1`, for every `k`** — the powers of two are the
  *almost perfect* numbers `σ(2ᵏ) = 2·2ᵏ − 1`, the tightest possible deficiency.

## Why This Is New

`perfect-numbers-oq-05` established `σ(pᵏ) < 2·pᵏ` (the lower tail is *smaller* than the
top term) but never quantified *by how much*. The exact deficiency, its division-form
matching the closed geometric sum `(pᵏ − 1)/(p − 1)`, and the sharp `p = 2` value
(almost-perfect numbers) are all new content answering that open question.

## Main Results

* `deficiency_prime_pow_eq`      : `deficiency(pᵏ) = pᵏ − Σ_{j<k} pʲ`   (the exact gap)
* `deficiency_prime_pow_eq_div`  : `= pᵏ − (pᵏ − 1)/(p − 1)`             (OQ's literal form)
* `pred_mul_geomSum_add_one`     : `(p − 1)·Σ_{j<k} pʲ + 1 = pᵏ`          (division-free meaning)
* `one_le_deficiency`            : `1 ≤ deficiency(pᵏ)`                   (deficient by ≥ 1)
* `deficiency_two_pow_eq_one`    : `deficiency(2ᵏ) = 1`                   (almost perfect)
* concrete gaps: `deficiency 8 = 1`, `deficiency 9 = 5`.

The load-bearing Mathlib lemmas are `ArithmeticFunction.sigma_one_apply_prime_pow`,
`Nat.geomSum_lt`, and `Nat.geomSum_eq` (the closed form `Σ_{j<n} mʲ = (mⁿ − 1)/(m − 1)`).
No `native_decide`: everything is kernel-checked (0 axioms).
-/

namespace PerfectNumbersOQ05OQ01

open ArithmeticFunction Finset Nat

/-! ## The deficiency gap -/

/-- The **deficiency** of `n`: how far the sum of divisors falls short of `2n`.
`deficiency n = 0` iff `n` is perfect; `> 0` iff deficient. -/
def deficiency (n : ℕ) : ℕ := 2 * n - sigma 1 n

/-! ## Geometric ingredients (reused from the parent's argument) -/

/-- The geometric lower tail `1 + p + ⋯ + pᵏ⁻¹` is strictly below the top power `pᵏ`
(for a prime, hence `p ≥ 2`). A direct instance of `Nat.geomSum_lt`. -/
theorem geomSum_lt_pow (p k : ℕ) (hp : p.Prime) :
    ∑ j ∈ range k, p ^ j < p ^ k :=
  Nat.geomSum_lt hp.two_le (fun _ hj => mem_range.mp hj)

/-- Closed form of the lower tail as the classical geometric sum
`(pᵏ − 1)/(p − 1)` (Mathlib's `Nat.geomSum_eq`). -/
theorem geomSum_eq_div (p k : ℕ) (hp : p.Prime) :
    ∑ j ∈ range k, p ^ j = (p ^ k - 1) / (p - 1) :=
  Nat.geomSum_eq hp.two_le k

/-- The division-free content of `(pᵏ − 1)/(p − 1)`: for any `p ≥ 1`,
`(p − 1)·(1 + p + ⋯ + pᵏ⁻¹) + 1 = pᵏ`. Proved by induction, so no exact-division
side condition is needed. -/
theorem pred_mul_geomSum_add_one (p k : ℕ) (hp : 1 ≤ p) :
    (p - 1) * (∑ j ∈ range k, p ^ j) + 1 = p ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, pow_succ]
      have key : p ^ n + (p - 1) * p ^ n = p ^ n * p := by
        have hpp : 1 + (p - 1) = p := by omega
        calc p ^ n + (p - 1) * p ^ n
              = (1 + (p - 1)) * p ^ n := by ring
          _ = p * p ^ n := by rw [hpp]
          _ = p ^ n * p := by ring
      omega

/-! ## The sum-of-divisors split -/

/-- `σ(pᵏ)` splits as the lower tail plus the top term:
`σ(pᵏ) = (1 + p + ⋯ + pᵏ⁻¹) + pᵏ`. -/
theorem sigma_prime_pow_split (p k : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ k) = (∑ j ∈ range k, p ^ j) + p ^ k := by
  rw [sigma_one_apply_prime_pow hp, Finset.sum_range_succ]

/-! ## The exact deficiency -/

/-- **Headline (exact gap).** The deficiency of a prime power is the top term minus the
geometric lower tail:

  `2·pᵏ − σ(pᵏ) = pᵏ − (1 + p + ⋯ + pᵏ⁻¹).`

This upgrades the parent's inequality `σ(pᵏ) < 2pᵏ` to an *equation* for the gap. -/
theorem deficiency_prime_pow_eq (p k : ℕ) (hp : p.Prime) :
    deficiency (p ^ k) = p ^ k - ∑ j ∈ range k, p ^ j := by
  unfold deficiency
  rw [sigma_prime_pow_split p k hp]
  have hlt := geomSum_lt_pow p k hp
  omega

/-- **Headline (OQ's literal form).** With the geometric sum written in its classical
closed form,

  `2·pᵏ − σ(pᵏ) = pᵏ − (pᵏ − 1)/(p − 1).` -/
theorem deficiency_prime_pow_eq_div (p k : ℕ) (hp : p.Prime) :
    deficiency (p ^ k) = p ^ k - (p ^ k - 1) / (p - 1) := by
  rw [deficiency_prime_pow_eq p k hp, geomSum_eq_div p k hp]

/-- Subtraction-free form of the exact deficiency:
`σ(pᵏ) + deficiency(pᵏ) = 2·pᵏ` with `deficiency(pᵏ) = pᵏ − Σ_{j<k} pʲ`. -/
theorem sigma_add_deficiency (p k : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ k) + deficiency (p ^ k) = 2 * p ^ k := by
  rw [deficiency_prime_pow_eq p k hp, sigma_prime_pow_split p k hp]
  have hlt := geomSum_lt_pow p k hp
  omega

/-- Every prime power is deficient **by at least `1`** — the quantitative refinement of
`σ(pᵏ) < 2·pᵏ`. -/
theorem one_le_deficiency (p k : ℕ) (hp : p.Prime) :
    1 ≤ deficiency (p ^ k) := by
  rw [deficiency_prime_pow_eq p k hp]
  have hlt := geomSum_lt_pow p k hp
  omega

/-! ## Sharp corollary: powers of two are almost perfect -/

/-- **The powers of two are *almost perfect*.** For every `k`, the deficiency of `2ᵏ`
is *exactly* `1`:

  `2·2ᵏ − σ(2ᵏ) = 1,`  equivalently  `σ(2ᵏ) = 2^{k+1} − 1.`

This is the tightest possible deficiency (`≥ 1` by `one_le_deficiency`, attained here),
because the lower tail `1 + 2 + ⋯ + 2ᵏ⁻¹ = 2ᵏ − 1` is just one short of `2ᵏ`. -/
theorem deficiency_two_pow_eq_one (k : ℕ) :
    deficiency (2 ^ k) = 1 := by
  rw [deficiency_prime_pow_eq 2 k Nat.prime_two]
  have hgeo : ∑ j ∈ range k, 2 ^ j = 2 ^ k - 1 := by
    have h := Nat.geomSum_eq (le_refl 2) k
    simpa using h
  rw [hgeo]
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
  omega

/-! ## Concrete gaps — from the general theorem, not `native_decide` -/

/-- `8 = 2³` is deficient by exactly `1` (σ(8) = 15). -/
theorem deficiency_eight : deficiency 8 = 1 := by
  rw [show (8 : ℕ) = 2 ^ 3 from by norm_num]
  exact deficiency_two_pow_eq_one 3

/-- `9 = 3²` is deficient by exactly `5` (σ(9) = 13 = 18 − 5). -/
theorem deficiency_nine : deficiency 9 = 5 := by
  rw [show (9 : ℕ) = 3 ^ 2 from by norm_num, deficiency_prime_pow_eq 3 2 (by norm_num)]
  decide

end PerfectNumbersOQ05OQ01
