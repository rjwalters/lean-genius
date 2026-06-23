import Archive.Wiedijk100Theorems.PerfectNumbers
import Mathlib.Tactic

/-
# Every Even Perfect Number is Triangular

## What This Proves

A *triangular number* is one of the form `Tₘ = m(m+1)/2` (the count of dots
in a triangular arrangement): `1, 3, 6, 10, 15, 21, 28, …`.

A number is *perfect* if it equals the sum of its proper divisors
(`6 = 1+2+3`, `28 = 1+2+4+7+14`).

**Main result.** Every even perfect number is a triangular number.  More
precisely, if `n` is even and perfect then `n = T_{2^{p}-1}` where
`2^{p}-1` is the Mersenne prime occurring in the Euclid–Euler factorization
`n = 2^{p-1}(2^{p}-1)`.  So the triangulating index is the Mersenne prime
itself.

For example:
- `6  = T₃   = 3·4/2`      (Mersenne prime `3`)
- `28 = T₇   = 7·8/2`      (Mersenne prime `7`)
- `496 = T₃₁ = 31·32/2`    (Mersenne prime `31`)
- `8128 = T₁₂₇ = 127·128/2` (Mersenne prime `127`)

## Approach

The Euclid–Euler theorem (`Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`,
from Mathlib's Archive) gives `n = 2^k · m` with `m = mersenne (k+1) = 2^{k+1}-1`
a Mersenne prime.  The key arithmetic identity is then purely algebraic:
`2·n = 2 · 2^k · (2^{k+1}-1) = 2^{k+1} · (2^{k+1}-1) = m · (m+1)`,
using `m + 1 = 2^{k+1}`.  Hence `n = m(m+1)/2 = T_m`.  Working with the
*doubled* form `2·n = m·(m+1)` keeps the whole argument free of natural-number
division.

## Distinctness

The parent `PerfectNumbers.lean` proves the Euclid–Euler characterization
(the Mersenne *form*) but never the triangular consequence.  `PerfectNumbersOQ03`
covers a different angle.  This file closes the form → triangular gap.

## Status
- [x] Complete proof, 0 sorries, 0 axioms (beyond Mathlib's foundational set)
-/

namespace PerfectNumbersOQ06

open scoped ArithmeticFunction

/-- `IsTriangular n` means `n` is the `m`-th triangular number `m(m+1)/2`
for some `m`. -/
def IsTriangular (n : ℕ) : Prop := ∃ m : ℕ, n = m * (m + 1) / 2

/-- The doubled form: `n` is triangular as soon as `2 * n = m * (m + 1)`.
This is the division-free certificate of triangularity. -/
theorem isTriangular_of_two_mul {n m : ℕ} (h : 2 * n = m * (m + 1)) :
    IsTriangular n := by
  refine ⟨m, ?_⟩
  rw [← h, Nat.mul_div_cancel_left n (by norm_num)]

/-- Every triangular number `m(m+1)/2` satisfies `2 * Tₘ = m(m+1)`
(consecutive integers have an even product, so the division is exact). -/
theorem two_mul_triangular (m : ℕ) : 2 * (m * (m + 1) / 2) = m * (m + 1) := by
  have h2 : 2 ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  rw [Nat.mul_div_cancel' h2]

/-- **Core identity.** For the Euclid–Euler factor `n = 2^k · (2^{k+1}-1)`,
the doubled value equals `m·(m+1)` with `m = 2^{k+1}-1`, since
`m + 1 = 2^{k+1}`. -/
theorem two_mul_euclid_factor (k : ℕ) :
    2 * (2 ^ k * mersenne (k + 1)) = mersenne (k + 1) * (mersenne (k + 1) + 1) := by
  have hm1 : mersenne (k + 1) + 1 = 2 ^ (k + 1) := by
    rw [mersenne, Nat.sub_add_cancel Nat.one_le_two_pow]
  -- Keep `mersenne (k+1)` opaque; only `m + 1 = 2^{k+1} = 2·2^k` is needed.
  rw [hm1, pow_succ]
  ring

/-- **Main theorem.** Every even perfect number is triangular; the triangulating
index is the Mersenne prime from its Euclid–Euler factorization. -/
theorem even_perfect_isTriangular {n : ℕ} (hev : Even n) (hperf : n.Perfect) :
    IsTriangular n := by
  obtain ⟨k, _hprime, rfl⟩ :=
    Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect hev hperf
  exact isTriangular_of_two_mul (two_mul_euclid_factor k)

/-- Strengthened form: an even perfect number `n` equals `T_m` where `m` is a
Mersenne prime (so the triangulating index is itself prime). -/
theorem even_perfect_triangular_mersenne_prime {n : ℕ} (hev : Even n) (hperf : n.Perfect) :
    ∃ m : ℕ, m.Prime ∧ n = m * (m + 1) / 2 := by
  obtain ⟨k, hprime, rfl⟩ :=
    Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect hev hperf
  refine ⟨mersenne (k + 1), hprime, ?_⟩
  have h := two_mul_euclid_factor k
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num)]

/-! ## Concrete examples (the first four perfect numbers) -/

example : IsTriangular 6 := ⟨3, by norm_num⟩      -- 6 = T₃
example : IsTriangular 28 := ⟨7, by norm_num⟩      -- 28 = T₇
example : IsTriangular 496 := ⟨31, by norm_num⟩    -- 496 = T₃₁
example : IsTriangular 8128 := ⟨127, by norm_num⟩  -- 8128 = T₁₂₇

end PerfectNumbersOQ06
