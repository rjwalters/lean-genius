/-
# Four-Square Distribution — OQ01 · 01:
# Reducing Jacobi's modified divisor sum σ*(n) to the ordinary divisor sum

Source: parent entry `four-square-distribution-oq-01`
(`Proofs/FourSquareDistributionOQ01.lean`), which states Jacobi's four-square
formula `r₄(n) = 8·σ*(n)` as `axiom jacobi_r4_formula`, where

    σ*(n) := Σ_{d ∣ n, 4 ∤ d} d

is Jacobi's *modified* divisor sum (every divisor divisible by 4 is dropped).

## The open question

OQ01-OQ01 asks to replace `axiom jacobi_r4_formula` with a Lean proof,
identifying `θ⁴` as a weight-2 Eisenstein combination on `Γ₀(4)`. The full
modular-forms proof is out of reach of current Mathlib. This file makes
unconditional, axiom-free progress on the *arithmetic side* of that formula:
it pins down exactly how Jacobi's `σ*` relates to the ordinary divisor sum

    σ(n) := Σ_{d ∣ n} d,

which is precisely the relation underlying the Eisenstein-series decomposition
(the `Γ₀(4)` weight-2 Eisenstein space is spanned by `E₂(τ) - 2E₂(2τ)` and
`E₂(τ) - 4E₂(4τ)`, whose `q`-coefficients are `σ` with the `4 ∣ d` divisors
removed — i.e. exactly `σ*`).

## What is proved (0 axioms, fully verified)

* `sigmaStar_eq_filter` — `σ*(n) = Σ_{d ∣ n, 4 ∤ d} d` as a genuine filtered sum.
* `sigmaStar_of_not_four_dvd` — **whenever `4 ∤ n`, `σ*(n) = σ(n)`**: no divisor
  of such `n` is divisible by `4`, so the modification is inert. This covers
  three of the four residue classes mod 4 (`n ≡ 1, 2, 3`).
* `sigmaStar_odd`, `sigmaStar_two_mul_odd` — the `n` odd and `n ≡ 2 (mod 4)`
  corollaries.
* `sigmaStar_add_four_part` — the `4 ∣ n` correction: `σ*(n)` plus the sum of the
  divisors of `n` divisible by `4` equals `σ(n)`. Equivalently
  `σ*(n) = σ(n) − Σ_{d ∣ n, 4 ∣ d} d`, isolating the entire deviation of `σ*`
  from `σ` into the dropped `4 ∣ d` part.
* `sigmaStar_le_sigma` — `σ*(n) ≤ σ(n)` always.

`σ*` is reproduced verbatim from the parent file (the entry keeps itself
import-light — Mathlib only — so it verifies without the parent's
`native_decide`-heavy build).

Tags: number-theory, sums-of-squares, jacobi, divisor-sum, axiom-reduction
-/

import Mathlib

namespace FourSquareDistributionOQ01OQ01

open Finset

/-- Jacobi's modified divisor sum `σ*(n) = Σ_{d ∣ n, 4 ∤ d} d` (verbatim from
`Proofs/FourSquareDistributionOQ01.lean`). -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d

/-- The ordinary divisor sum `σ(n) = Σ_{d ∣ n} d`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `σ*(n)` is the sum of the divisors of `n` that are **not** divisible by 4. -/
theorem sigmaStar_eq_filter (n : ℕ) :
    sigmaStar n = ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d := by
  unfold sigmaStar
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases h : 4 ∣ d <;> simp [h]

/-- **Main reduction.** When `4 ∤ n`, no divisor of `n` is divisible by `4`, so
Jacobi's modification is inert and `σ*(n) = σ(n)`. This covers `n ≡ 1, 2, 3
(mod 4)`. -/
theorem sigmaStar_of_not_four_dvd {n : ℕ} (h : ¬ 4 ∣ n) :
    sigmaStar n = sigma1 n := by
  unfold sigmaStar sigma1
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hnd : ¬ 4 ∣ d := fun hh => h (hh.trans hdvd)
  simp [hnd]

/-- For odd `n`, `σ*(n) = σ(n)`. -/
theorem sigmaStar_odd {n : ℕ} (hn : Odd n) : sigmaStar n = sigma1 n := by
  apply sigmaStar_of_not_four_dvd
  rintro ⟨k, rfl⟩
  rw [Nat.odd_iff] at hn
  omega

/-- For `n = 2·m` with `m` odd (i.e. `n ≡ 2 (mod 4)`), `σ*(n) = σ(n)`. -/
theorem sigmaStar_two_mul_odd {m : ℕ} (hm : Odd m) : sigmaStar (2 * m) = sigma1 (2 * m) := by
  apply sigmaStar_of_not_four_dvd
  rintro ⟨k, hk⟩
  rw [Nat.odd_iff] at hm
  omega

/-- **The `4 ∣ n` correction.** `σ*(n)` together with the sum of the divisors of
`n` that *are* divisible by `4` recovers the full divisor sum `σ(n)`. Thus the
entire deviation of `σ*` from `σ` is the dropped `4 ∣ d` part. -/
theorem sigmaStar_add_four_part (n : ℕ) :
    sigmaStar n + ∑ d ∈ n.divisors.filter (fun d => 4 ∣ d), d = sigma1 n := by
  rw [sigmaStar_eq_filter, add_comm]
  exact Finset.sum_filter_add_sum_filter_not n.divisors (fun d => 4 ∣ d) (fun d => d)

/-- Consequently `σ*(n) ≤ σ(n)` for every `n`. -/
theorem sigmaStar_le_sigma (n : ℕ) : sigmaStar n ≤ sigma1 n := by
  rw [← sigmaStar_add_four_part n]; exact Nat.le_add_right _ _

/-- Sanity checks against the divisor characterisation (kernel `decide`, so no
`Lean.ofReduceBool`). `σ*(12) = 1+2+3+6 = 12 = σ(12) − 4·σ(3) = 28 − 16`. -/
example : sigmaStar 12 = 12 := by decide
example : sigma1 12 = 28 := by decide
example : sigmaStar 8 = 3 := by decide   -- divisors 1,2,4,8 → keep 1,2

end FourSquareDistributionOQ01OQ01
