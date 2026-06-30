import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Div
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

## The reliability profile (Part IV)

Parts II–III locate where the ordinary test goes *blind*; Part IV proves the positive
complement — the exact range in which it is a *correct* multiplicity criterion.

* `sub_pow_dvd_iff_hasseDeriv_eval_eq_zero` : the **Hasse-derivative multiplicity criterion**
  `(X − a)ᵏ ∣ f ↔ ∀ j < k, (hasseDeriv j f)(a) = 0`, valid over *any* commutative ring.
  Mathlib has the pieces (`taylor`, `taylor_coeff`, `X_pow_dvd_iff`) but not this assembled
  criterion; it is obtained by transporting `Xᵏ ∣ taylor a f` back along the Taylor shift
  `X ↦ X + a` (an `AlgEquiv`).  This is the characteristic-free engine.
* `ordinary_derivative_test_valid_range` : **the ordinary test is correct for multiplicities
  up to `p`** — over a characteristic-`p` field, for `m ≤ p`,
  `(X − a)ᵐ ∣ f ↔ ∀ j < m, (derivative^{(j)} f)(a) = 0`.  Below the threshold each `(j! : F)`
  is a unit, so the ordinary and Hasse tests agree termwise.
* `ordinary_derivative_test_sharp` : **the bound `m ≤ p` is sharp** — at `m = p + 1` the test
  already lies, certifying multiplicity `≥ p + 1` for `X^p` at `0` (all its derivatives vanish)
  even though `X^{p+1} ∤ X^p`.  So `m ≤ p` is *exactly* the reliable range.

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

/- ============================================================
   Part IV — The reliability profile: the ordinary test is a *correct*
   multiplicity criterion exactly in the range `m ≤ p`
   ============================================================

   Parts II–III pinned down where the ordinary-derivative test goes *blind*
   (orders `≥ p`).  Here we establish the positive companion: in the range
   `m ≤ p` the ordinary test is a genuine, correct multiplicity criterion, and
   this range is sharp.  The engine is a characteristic-free bridge — the
   *Hasse-derivative multiplicity criterion*, which Mathlib does not record in
   this form — obtained from `Polynomial.taylor` (the shift `X ↦ X + a`, an
   `AlgEquiv`) and `Polynomial.taylor_coeff` (`(taylor a f).coeff k =
   (hasseDeriv k f).eval a`). -/

/-- `taylor a` sends the linear factor `X - C a` to `X` (it is the shift
`X ↦ X + a`). -/
private theorem taylor_X_sub_C_eq [CommRing F] (a : F) :
    taylor a (X - C a : F[X]) = X := by
  rw [map_sub, taylor_X, taylor_C, add_sub_cancel_right]

/-- `taylor (-a)` sends `X` back to the linear factor `X - C a` (the inverse
shift). -/
private theorem taylor_neg_X_eq [CommRing F] (a : F) :
    taylor (-a) (X : F[X]) = X - C a := by
  rw [taylor_X, map_neg, ← sub_eq_add_neg]

/-- **Linear-factor divisibility transports to `X`-divisibility under the Taylor
shift.** Since `taylor a` is the algebra automorphism `X ↦ X + a` carrying
`X - C a` to `X`, a polynomial `f` is divisible by `(X - C a)^n` iff its Taylor
expansion at `a` is divisible by `X^n`. -/
theorem sub_pow_dvd_iff_X_pow_dvd_taylor [CommRing F] (a : F) (n : ℕ) (f : F[X]) :
    (X - C a) ^ n ∣ f ↔ X ^ n ∣ taylor a f := by
  constructor
  · intro h
    have h2 := map_dvd (taylorAlgHom a) h
    simpa only [taylorAlgHom_apply, taylor_pow, taylor_X_sub_C_eq] using h2
  · intro h
    have h2 := map_dvd (taylorAlgHom (-a)) h
    simpa only [taylorAlgHom_apply, taylor_pow, taylor_neg_X_eq, taylor_taylor,
      neg_add_cancel, taylor_zero] using h2

/-- **Hasse-derivative multiplicity criterion (characteristic-free).** A
polynomial `f` over any commutative ring is divisible by `(X - C a)^n` **iff**
all Hasse derivatives of order `< n` vanish at `a`:

  `(X - C a)^n ∣ f  ↔  ∀ j < n, (hasseDeriv j f).eval a = 0`.

This is the divided-power (Hasse) form of the factor-multiplicity theorem and
the correct replacement for the ordinary-derivative test in every
characteristic.  It is the engine of the reliability range below. -/
theorem sub_pow_dvd_iff_hasseDeriv_eval_eq_zero [CommRing F] (a : F) (n : ℕ) (f : F[X]) :
    (X - C a) ^ n ∣ f ↔ ∀ j < n, (hasseDeriv j f).eval a = 0 := by
  rw [sub_pow_dvd_iff_X_pow_dvd_taylor, X_pow_dvd_iff]
  simp_rw [taylor_coeff]

/-- **Evaluation form of the scaling identity.** Evaluating the ordinary
derivative at a point scales the Hasse-derivative value by `(k! : F)`:
`(derivative^[k] f).eval a = (k! : F) * (hasseDeriv k f).eval a`. -/
theorem iterate_derivative_eval_eq [CommRing F] (k : ℕ) (f : F[X]) (a : F) :
    (derivative^[k] f).eval a = (k ! : F) * (hasseDeriv k f).eval a := by
  rw [iterate_derivative_eq_smul_hasseDeriv, smul_eq_C_mul, eval_mul, eval_C]

/-- **The reliability range: `m ≤ p`.** Over a field of characteristic `p`, for
every order bound `m ≤ p` the *ordinary*-derivative test is a correct
multiplicity criterion:

  `(X - C a)^m ∣ f  ↔  ∀ j < m, (derivative^[j] f).eval a = 0`.

This is the positive complement to Part II's blindness result: below the
factorial threshold each `(j! : F)` (`j < m ≤ p`) is a unit, so the ordinary
derivative vanishes at `a` exactly when the Hasse derivative does, and the
Hasse criterion (`sub_pow_dvd_iff_hasseDeriv_eval_eq_zero`) closes the loop.
The ordinary-derivative multiplicity test is therefore *reliable for all
multiplicities up to `p`*. -/
theorem ordinary_derivative_test_valid_range [Field F] [CharP F p] (hp : p.Prime)
    {m : ℕ} (hm : m ≤ p) (a : F) (f : F[X]) :
    (X - C a) ^ m ∣ f ↔ ∀ j < m, (derivative^[j] f).eval a = 0 := by
  rw [sub_pow_dvd_iff_hasseDeriv_eval_eq_zero]
  refine forall_congr' fun j => imp_congr_right fun hjm => ?_
  have hjp : j < p := hjm.trans_le hm
  have hu : (j ! : F) ≠ 0 := by
    rw [Ne, factorial_cast_eq_zero_iff hp]; omega
  rw [iterate_derivative_eval_eq]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hu
    · exact h'

/-- **Sharpness of the reliability range.** The bound `m ≤ p` in
`ordinary_derivative_test_valid_range` is best possible: at order `m = p + 1`
the ordinary test already fails.  Witness: `f = X^p` over a characteristic-`p`
field.  Every ordinary derivative of order `≤ p` vanishes at `0` (the first
already does, as `p · X^{p-1} = 0`), so the ordinary test *certifies*
multiplicity `≥ p + 1` at `0`; yet `(X - C 0)^{p+1} = X^{p+1}` does **not**
divide `X^p`.  Thus the criterion breaks at exactly one step past the
threshold. -/
theorem ordinary_derivative_test_sharp [Field F] [CharP F p] (hp : p.Prime) :
    (∀ j < p + 1, (derivative^[j] (X ^ p : F[X])).eval 0 = 0) ∧
      ¬ (X - C (0 : F)) ^ (p + 1) ∣ (X ^ p : F[X]) := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [zero_pow hp.pos.ne']
    · have hpe : (X ^ p : F[X]) = X ^ (p ^ 1) := by rw [pow_one]
      rw [hpe, iterate_derivative_X_pow_char_eq_zero hp le_rfl hj0, eval_zero]
  · rw [C_0, sub_zero, X_pow_dvd_iff]
    push_neg
    exact ⟨p, by omega, by simp [coeff_X_pow]⟩

end FactorRemainderHasseDerivativeFq
