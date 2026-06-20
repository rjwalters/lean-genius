/-
# Euler's totient periodicity beyond the coprime case (prime-power moduli)

Euler's theorem says that for `gcd(a, n) = 1` the exponent of a power `aᵏ (mod n)`
may be reduced modulo `φ n`. Mathlib formalizes exactly this coprime statement
(`Nat.pow_add_totient_mod_eq`, `Nat.pow_add_mul_totient_mod_eq`, `Nat.pow_totient_mod`),
and `Mathlib/NumberTheory/PowModTotient.lean` lists as an explicit TODO:

> "Extend to results in cases where the base is not coprime to the modulus."

This file carries out exactly that extension for **prime-power moduli** `pᵉ`.
The key observation is that the coprime hypothesis can be dropped entirely as long
as the exponent is at least `e`: if `p ∤ a` the usual Euler argument applies, while
if `p ∣ a` then `pᵉ ∣ aᵏ` already (because `k ≥ e`), so both `aᵏ` and `aᵏ⁺ᵠ⁽ᵖᵉ⁾`
are `≡ 0`. The resulting periodicity holds for *every* base `a`.

## Main results

* `EulerTotientOQ08.pow_add_totient_modEq_primePow` — for any base `a`, prime `p`,
  `1 ≤ e` and `e ≤ k`:  `a ^ (k + φ (pᵉ)) ≡ a ^ k [MOD pᵉ]`.
* `EulerTotientOQ08.pow_add_mul_totient_modEq_primePow` — the multi-period version,
  adding any multiple `l * φ (pᵉ)` to the exponent.
* `EulerTotientOQ08.pow_modEq_primePow` — the full exponent reduction
  `a ^ k ≡ a ^ (e + (k - e) % φ (pᵉ)) [MOD pᵉ]`, valid for *all* bases (the
  non-coprime analogue of `Nat.pow_totient_mod`); the constant `e`-prefix is the
  pre-period during which a power that shares the factor `p` collapses to `0`.

These are genuinely outside Mathlib's coprime-only coverage: e.g. they apply to
`2 ^ k (mod 8)` or `6 ^ k (mod 16)`, where the base is *not* invertible mod `pᵉ`.
-/
import Mathlib

open Nat (totient)

namespace EulerTotientOQ08

open scoped Nat

/-- **Non-coprime prime-power Euler periodicity.**
For any natural base `a`, prime `p`, exponent `e ≥ 1` and any `k ≥ e`, adding
`φ (pᵉ)` to the exponent leaves `aᵏ` unchanged modulo `pᵉ` — *even when `p ∣ a`*,
the case Euler's theorem does not cover. -/
theorem pow_add_totient_modEq_primePow {p a k e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hk : e ≤ k) : a ^ (k + totient (p ^ e)) ≡ a ^ k [MOD p ^ e] := by
  by_cases hpa : p ∣ a
  · -- `p ∣ a`: both powers vanish mod `pᵉ`, so they are congruent (to `0`).
    have hak : p ^ e ∣ a ^ k :=
      (pow_dvd_pow_of_dvd hpa e).trans (pow_dvd_pow a hk)
    have hak' : p ^ e ∣ a ^ (k + totient (p ^ e)) :=
      hak.trans (pow_dvd_pow a (Nat.le_add_right k _))
    calc a ^ (k + totient (p ^ e))
        ≡ 0 [MOD p ^ e] := (Nat.modEq_zero_iff_dvd).mpr hak'
      _ ≡ a ^ k [MOD p ^ e] := ((Nat.modEq_zero_iff_dvd).mpr hak).symm
  · -- `p ∤ a`: `a` is coprime to `pᵉ`, and Euler's theorem applies.
    have hcop : a.Coprime (p ^ e) := (hp.coprime_iff_not_dvd.2 hpa).symm.pow_right e
    have heul : a ^ totient (p ^ e) ≡ 1 [MOD p ^ e] := Nat.ModEq.pow_totient hcop
    calc a ^ (k + totient (p ^ e))
        = a ^ k * a ^ totient (p ^ e) := by rw [pow_add]
      _ ≡ a ^ k * 1 [MOD p ^ e] := (Nat.ModEq.refl _).mul heul
      _ = a ^ k := by rw [mul_one]

/-- The multi-period form: adding any multiple `l * φ (pᵉ)` of the period to the
exponent leaves `aᵏ` unchanged modulo `pᵉ`, for every base `a` (non-coprime case
included). -/
theorem pow_add_mul_totient_modEq_primePow {p a k e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hk : e ≤ k) (l : ℕ) : a ^ (k + l * totient (p ^ e)) ≡ a ^ k [MOD p ^ e] := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hstep : a ^ ((k + l * totient (p ^ e)) + totient (p ^ e))
        ≡ a ^ (k + l * totient (p ^ e)) [MOD p ^ e] :=
      pow_add_totient_modEq_primePow hp he (hk.trans (Nat.le_add_right _ _))
    calc a ^ (k + (l + 1) * totient (p ^ e))
        = a ^ ((k + l * totient (p ^ e)) + totient (p ^ e)) := by congr 1; ring
      _ ≡ a ^ (k + l * totient (p ^ e)) [MOD p ^ e] := hstep
      _ ≡ a ^ k [MOD p ^ e] := ih

/-- **Full exponent reduction for prime-power moduli** (the non-coprime analogue of
`Nat.pow_totient_mod`). For every base `a`, prime `p`, `e ≥ 1` and `k ≥ e`, the
exponent of `aᵏ (mod pᵉ)` can be reduced to `e + (k - e) % φ (pᵉ)`. The leading `e`
is the pre-period: for bases sharing the factor `p`, the powers `a⁰, …, aᵉ⁻¹` are
not yet stable, but from `aᵉ` onward the sequence is periodic with period `φ (pᵉ)`. -/
theorem pow_modEq_primePow {p a k e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hk : e ≤ k) :
    a ^ k ≡ a ^ (e + (k - e) % totient (p ^ e)) [MOD p ^ e] := by
  -- Split `k - e` as `(k - e) % φ(pᵉ) + ((k - e) / φ(pᵉ)) * φ(pᵉ)` via the division
  -- algorithm, so the exponent `k` becomes `(e + (k - e) % φ(pᵉ)) + (quotient) * φ(pᵉ)`.
  have hsplit : k = (e + (k - e) % totient (p ^ e))
      + ((k - e) / totient (p ^ e)) * totient (p ^ e) := by
    have hdm : (k - e) % totient (p ^ e) + (k - e) / totient (p ^ e) * totient (p ^ e)
        = k - e := Nat.mod_add_div' (k - e) (totient (p ^ e))
    omega
  have hge : e ≤ e + (k - e) % totient (p ^ e) := Nat.le_add_right _ _
  calc a ^ k
      = a ^ ((e + (k - e) % totient (p ^ e))
          + ((k - e) / totient (p ^ e)) * totient (p ^ e)) := by rw [← hsplit]
    _ ≡ a ^ (e + (k - e) % totient (p ^ e)) [MOD p ^ e] :=
        pow_add_mul_totient_modEq_primePow hp he hge ((k - e) / totient (p ^ e))

/-! ### Worked examples (non-coprime bases) -/

-- `2 ^ k (mod 8)`: the base shares the factor `2`, so Euler's coprime theorem does
-- not apply. From `k = 3 = e` onward the powers are constant (`≡ 0`).
example : (2 : ℕ) ^ (3 + totient (2 ^ 3)) ≡ 2 ^ 3 [MOD 2 ^ 3] :=
  pow_add_totient_modEq_primePow (p := 2) Nat.prime_two (by norm_num) (by norm_num)

-- Concrete sanity check of the same instance: `2⁷ = 128 ≡ 0` and `2³ = 8 ≡ 0 (mod 8)`.
example : (2 : ℕ) ^ 7 ≡ 2 ^ 3 [MOD 8] := by decide

-- `6 ^ k (mod 16)`: `6 = 2 · 3` shares the factor `2`; here `e = 4`, `φ(16) = 8`.
example : (6 : ℕ) ^ (4 + totient (2 ^ 4)) ≡ 6 ^ 4 [MOD 2 ^ 4] :=
  pow_add_totient_modEq_primePow (p := 2) Nat.prime_two (by norm_num) (by norm_num)

-- Full reduction collapsing a large exponent of a non-invertible base:
-- `6 ^ 100 ≡ 6 ^ (4 + (100 - 4) % 8) = 6 ^ 4 (mod 16)`, and indeed `6⁴ ≡ 0`.
example : (6 : ℕ) ^ 100 ≡ 6 ^ 4 [MOD 16] := by decide

end EulerTotientOQ08
