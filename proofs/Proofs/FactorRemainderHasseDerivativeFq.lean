import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.CharP.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-
# Full failure profile of the ordinary-derivative multiplicity test over `𝔽_q`

Problem id: `factor-remainder-hasse-derivative-fq`.

## Background

The multiplicity form of the factor theorem says, over a field of characteristic `0`,

  `(X − a)ᵏ ∣ p  ↔  p(a) = p′(a) = ⋯ = p^{(k−1)}(a) = 0`,

with the *ordinary* iterated derivatives `p^{(j)} = derivative^[j] p`.  In positive
characteristic this criterion breaks down: the gallery entry
`factor-remainder-theorem-oq-01-oq-02` (`FactorRemainderTheoremOQ01OQ02`) repairs it with the
**Hasse (divided-power) derivative** `hasseDeriv`, and records a *single* witness of the
breakdown — `hasseDeriv_detects_char_p`, where `derivative (X²) = 0` over `ZMod 2`.

This entry gives the **full failure profile**: it pins down *exactly* at which derivative order
the ordinary test goes blind over an arbitrary characteristic-`p` field (hence over every finite
field `𝔽_q`, `q = p^f`), and generalizes the `Xᵖ / 𝔽_p` counterexample to the whole family
`X^{p^e}`.

## The engine

Mathlib's `Polynomial.factorial_smul_hasseDeriv` is the identity tying the two derivatives
together:

  `derivative^[k] f = k ! • hasseDeriv k f`.

So the ordinary derivative is the Hasse derivative *scaled by `k!`*.  Whether the ordinary
derivative loses information is therefore governed entirely by whether `(k! : F)` vanishes.

## Main results

* `factorial_cast_eq_zero_iff` : the **exact threshold** — over a characteristic-`p` ring,
  `(k! : F) = 0 ↔ p ≤ k`.  (`p ∣ k!` happens iff `k ≥ p`, by `Nat.Prime.dvd_factorial`.)
* `iterate_derivative_eq_smul_hasseDeriv` : the scaling identity in base-field-scalar form,
  `derivative^[k] f = (k! : F) • hasseDeriv k f`.
* `iterate_derivative_eq_zero_of_char_le` : **above the threshold the ordinary test is blind** —
  for `p ≤ k`, `derivative^[k] f = 0` for *every* `f`, so the ordinary derivatives carry no
  multiplicity information at orders `≥ p`.
* `iterate_derivative_eq_zero_iff_hasseDeriv_of_lt` : **below the threshold the two agree** —
  for `k < p` over a field, `derivative^[k] f = 0 ↔ hasseDeriv k f = 0`, since `k!` is then a
  unit.  Together these two say the ordinary-derivative test is *reliable exactly up to order
  `p − 1`* and *useless from order `p` on*.
* `rootMultiplicity_X_pow`, `derivative_X_pow_char`,
  `iterate_derivative_X_pow_char_eq_zero`, `failure_profile_X_pow` : the concrete `X^{p^e}`
  family.  The Hasse test returns the true multiplicity `p^e`, while *every* positive-order
  ordinary derivative of `X^{p^e}` vanishes — so the ordinary test certifies multiplicity `≥ k`
  at `0` for every `k`, wildly overcounting the true value `p^e`.

All results are `0`-axiom, `0`-sorry, and hold over any characteristic-`p` field (every `𝔽_q`).
-/

namespace FactorRemainderHasseDerivativeFq

open Polynomial Nat

variable {F : Type*} {p : ℕ}

/- ============================================================
   Part I — The exact factorial threshold in characteristic `p`
   ============================================================ -/

/-- **The exact threshold.** In a commutative ring of characteristic `p` (prime), the cast
factorial `(k! : F)` is zero **iff** `p ≤ k`.  This is the algebraic heart of the failure
profile: `p ∣ k!` exactly when `k ≥ p`. -/
theorem factorial_cast_eq_zero_iff [CommRing F] [CharP F p] (hp : p.Prime) (k : ℕ) :
    (k ! : F) = 0 ↔ p ≤ k := by
  rw [CharP.cast_eq_zero_iff F p, hp.dvd_factorial]

/- ============================================================
   Part II — Ordinary derivative = Hasse derivative scaled by `k!`
   ============================================================ -/

/-- **Scaling identity (base-field form).** The `k`-th iterated *ordinary* derivative is the
`k`-th *Hasse* derivative scaled by the base-field element `(k! : F)`.  This is Mathlib's
`factorial_smul_hasseDeriv` with the scalar pushed into `F`. -/
theorem iterate_derivative_eq_smul_hasseDeriv [CommRing F] (k : ℕ) (f : F[X]) :
    (derivative^[k]) f = (k ! : F) • hasseDeriv k f := by
  rw [Nat.cast_smul_eq_nsmul, ← LinearMap.smul_apply]
  exact (congrFun (factorial_smul_hasseDeriv (R := F) (k := k)) f).symm

/-- **Above the threshold: the ordinary test is blind.** Over a characteristic-`p` field,
for `p ≤ k` the `k`-th iterated ordinary derivative of *every* polynomial vanishes.  Thus the
ordinary-derivative multiplicity criterion contributes no information at orders `≥ p`. -/
theorem iterate_derivative_eq_zero_of_char_le [CommRing F] [CharP F p]
    (hp : p.Prime) {k : ℕ} (hk : p ≤ k) (f : F[X]) :
    (derivative^[k]) f = 0 := by
  rw [iterate_derivative_eq_smul_hasseDeriv, (factorial_cast_eq_zero_iff hp k).mpr hk, zero_smul]

/-- **Below the threshold: ordinary and Hasse agree.** Over a field of characteristic `p`,
for `k < p` the factor `(k! : F)` is a unit, so the ordinary derivative vanishes exactly when
the Hasse derivative does.  The ordinary-derivative test is therefore *reliable up to order
`p − 1`*. -/
theorem iterate_derivative_eq_zero_iff_hasseDeriv_of_lt [Field F] [CharP F p]
    (hp : p.Prime) {k : ℕ} (hk : k < p) (f : F[X]) :
    (derivative^[k]) f = 0 ↔ hasseDeriv k f = 0 := by
  rw [iterate_derivative_eq_smul_hasseDeriv]
  have hu : IsUnit (k ! : F) := by
    refine isUnit_iff_ne_zero.mpr (fun h => ?_)
    rw [factorial_cast_eq_zero_iff hp k] at h
    omega
  exact hu.smul_eq_zero

/- ============================================================
   Part III — The `X^{p^e}` family: Hasse correct, ordinary blind
   ============================================================ -/

/-- **The Hasse test is correct on `X^n`.** The root multiplicity of `X^n` at `0` is `n`
(in every characteristic), as the Hasse-derivative criterion returns. -/
theorem rootMultiplicity_X_pow [Field F] (n : ℕ) :
    rootMultiplicity (0 : F) (X ^ n) = n := by
  simpa using rootMultiplicity_X_sub_C_pow (0 : F) n

/-- **The ordinary derivative of `X^{p^e}` vanishes outright.** Over a characteristic-`p` field
and `e ≥ 1`, already the first ordinary derivative of `X^{p^e}` is `0`, since `p ∣ p^e`. -/
theorem derivative_X_pow_char [CommRing F] [CharP F p] (_hp : p.Prime) {e : ℕ} (he : 1 ≤ e) :
    derivative (X ^ (p ^ e) : F[X]) = 0 := by
  rw [derivative_X_pow]
  have hpe : ((p ^ e : ℕ) : F) = 0 := by
    rw [CharP.cast_eq_zero_iff F p]
    exact dvd_pow_self p (by omega)
  rw [hpe, C_0, zero_mul]

/-- Every *positive-order* iterated ordinary derivative of `X^{p^e}` vanishes over a
characteristic-`p` field. -/
theorem iterate_derivative_X_pow_char_eq_zero [CommRing F] [CharP F p] (hp : p.Prime)
    {e : ℕ} (he : 1 ≤ e) {j : ℕ} (hj : 1 ≤ j) :
    (derivative^[j]) (X ^ (p ^ e) : F[X]) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply, derivative_X_pow_char hp he, iterate_derivative_zero]

/-- **Full failure profile for `X^{p^e}`.** Over any field of characteristic `p` with `e ≥ 1`:
the true root multiplicity at `0` is `p^e` (returned by the Hasse test), while *every*
positive-order ordinary derivative vanishes — so the ordinary-derivative test certifies
multiplicity `≥ k` at `0` for every `k`, overcounting the true value `p^e` without bound. -/
theorem failure_profile_X_pow [Field F] [CharP F p] (hp : p.Prime) {e : ℕ} (he : 1 ≤ e) :
    rootMultiplicity (0 : F) (X ^ (p ^ e)) = p ^ e ∧
      ∀ j, 1 ≤ j → (derivative^[j]) (X ^ (p ^ e) : F[X]) = 0 :=
  ⟨rootMultiplicity_X_pow _, fun _ hj => iterate_derivative_X_pow_char_eq_zero hp he hj⟩

end FactorRemainderHasseDerivativeFq
