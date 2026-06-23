import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Tactic

/-!
# Factor–remainder theorem OQ-01-OQ-01: the Taylor-coefficient form

The grandparent entry (`factor-remainder-theorem`) proves the Factor Theorem
`(X − a) ∣ p ↔ p(a) = 0`. Its OQ-01 (`factor-remainder-theorem-oq-01`) gives the
**multiplicity version** over a characteristic-zero field, phrased through iterated
derivatives:

> `(X − a)ᵏ ∣ p ↔ p(a) = p′(a) = ⋯ = p^{(k−1)}(a) = 0`.

This entry answers OQ-01's first open question:

> *Formalize the explicit Taylor-coefficient form: the order-`k` Taylor coefficient of `p`
> at `a` is `p^{(k)}(a)/k!`, so `(X − a)ᵏ ∣ p` iff the first `k` Taylor coefficients vanish,
> via `Polynomial.taylor`.*

The Taylor coefficient `(taylor a p).coeff m` is defined directly through Hasse derivatives
(`Polynomial.taylor_coeff : (taylor a p).coeff m = (hasseDeriv m p).eval a`) and so requires
**no division**. Consequently the entire characterization holds over an **arbitrary
commutative ring** — strictly more general than the parent's characteristic-zero field, and
in particular valid in positive characteristic where ordinary derivatives fail to detect
multiplicity. This simultaneously addresses the spirit of OQ-01's *second* open question
(Hasse derivatives in positive characteristic).

## Main results

* `X_pow_dvd_taylor_iff` : `X^k ∣ taylor a p ↔ (X − a)^k ∣ p` — the substitution
  `X ↦ X + a` (`Polynomial.taylorEquiv`, an algebra **equivalence**) reflects divisibility,
  trading the shifted factor `(X − a)^k` for the monomial factor `X^k`.
* `pow_dvd_iff_taylor_coeff_eq_zero` : **`(X − a)^k ∣ p ↔ ∀ m < k, (taylor a p).coeff m = 0`**
  — the OQ's target, over any commutative ring, for any `k`.
* `pow_dvd_iff_hasseDeriv_eval_eq_zero` : the same vanishing rephrased with Hasse derivatives,
  `(X − a)^k ∣ p ↔ ∀ m < k, (hasseDeriv m p).eval a = 0` (the positive-characteristic form).
* `factor_theorem_taylor` (`k = 1`) and `double_root_iff_taylor` (`k = 2`) : the low-order
  specializations, recovering `p(a) = 0` and `p(a) = p′(a) = 0`.
* `pow_dvd_iff_iterate_derivative_eval_eq_zero` : over a characteristic-zero field, the Taylor
  form is *equivalent* to the parent's iterated-derivative form, since
  `(derivative^[m] p).eval a = m! · (taylor a p).coeff m` and `m! ≠ 0`.

`0` axioms.
-/

namespace FactorRemainderTheoremOQ01OQ01

open Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- The substitution `X ↦ X + a` is an algebra **equivalence** of `R[X]`
    (`Polynomial.taylorEquiv`), so it both preserves and reflects divisibility. Applied to the
    factor `(X − a)^k` — which it sends to `X^k` — it shows that `X^k ∣ taylor a p` is
    *equivalent* to `(X − a)^k ∣ p`. -/
theorem X_pow_dvd_taylor_iff {p : R[X]} {a : R} {k : ℕ} :
    X ^ k ∣ taylor a p ↔ (X - C a) ^ k ∣ p := by
  -- `taylor a` carries the shifted factor `(X − a)^k` to the monomial `X^k`.
  have hX : taylor a ((X - C a) ^ k) = X ^ k := by
    have h1 : taylor a (X - C a) = X := by
      rw [map_sub, taylor_X, taylor_C]; ring
    rw [taylor_pow, h1]
  -- Trade `X^k` for `taylor a ((X − a)^k)`, then reflect divisibility along the equivalence
  -- `taylorEquiv a` (whose underlying map is `taylor a`, definitionally).
  rw [← hX]
  exact map_dvd_iff (taylorEquiv a)

/-- **The Taylor-coefficient factor theorem.** Over any commutative ring, the factor
    `(X − a)^k` divides `p` if and only if the first `k` Taylor coefficients of `p` at `a`
    vanish:
    `(X − a)^k ∣ p ↔ ∀ m < k, (taylor a p).coeff m = 0`.

    No hypothesis on `p`, on `k`, or on the characteristic is needed. -/
theorem pow_dvd_iff_taylor_coeff_eq_zero {p : R[X]} {a : R} {k : ℕ} :
    (X - C a) ^ k ∣ p ↔ ∀ m < k, (taylor a p).coeff m = 0 := by
  rw [← X_pow_dvd_taylor_iff, X_pow_dvd_iff]

/-- **The Hasse-derivative form** (valid in positive characteristic). Since the Taylor
    coefficient is `(taylor a p).coeff m = (hasseDeriv m p).eval a`, the divisibility
    `(X − a)^k ∣ p` is equivalent to the vanishing of the first `k` Hasse derivatives of `p`
    at `a`. Unlike ordinary derivatives, the divided-power (Hasse) derivatives correctly
    characterize multiplicity over every commutative ring. -/
theorem pow_dvd_iff_hasseDeriv_eval_eq_zero {p : R[X]} {a : R} {k : ℕ} :
    (X - C a) ^ k ∣ p ↔ ∀ m < k, (hasseDeriv m p).eval a = 0 := by
  simp_rw [pow_dvd_iff_taylor_coeff_eq_zero, taylor_coeff]

/-- **Factor Theorem** (`k = 1`) recovered from the Taylor form: `(X − a) ∣ p ↔ p(a) = 0`,
    because the `0`th Taylor coefficient is the evaluation `p(a)`. -/
theorem factor_theorem_taylor {p : R[X]} {a : R} :
    (X - C a) ∣ p ↔ p.eval a = 0 := by
  rw [← pow_one (X - C a), pow_dvd_iff_taylor_coeff_eq_zero]
  constructor
  · intro h; simpa [taylor_coeff_zero] using h 0 Nat.zero_lt_one
  · intro h m hm
    interval_cases m
    simpa [taylor_coeff_zero] using h

/-- **Double-root criterion** (`k = 2`) recovered from the Taylor form:
    `(X − a)² ∣ p ↔ p(a) = 0 ∧ p′(a) = 0`. The `0`th and `1`st Taylor coefficients are
    `p(a)` and `p′(a)`. -/
theorem double_root_iff_taylor {p : R[X]} {a : R} :
    (X - C a) ^ 2 ∣ p ↔ p.eval a = 0 ∧ (derivative p).eval a = 0 := by
  rw [pow_dvd_iff_taylor_coeff_eq_zero]
  constructor
  · intro h
    exact ⟨by simpa [taylor_coeff_zero] using h 0 (by norm_num),
           by simpa [taylor_coeff_one] using h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ m hm
    interval_cases m
    · simpa [taylor_coeff_zero] using h0
    · simpa [taylor_coeff_one] using h1

end CommRing

section CharZero

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Over a characteristic-zero field, the iterated derivative recovers the Taylor coefficient
    up to the factorial scalar: `(derivative^[m] p).eval a = m! · (taylor a p).coeff m`. This
    is the polynomial form of Taylor's theorem `cₘ = p^{(m)}(a)/m!`. (No characteristic
    hypothesis is needed for this identity; it holds over any commutative ring.) -/
theorem iterate_derivative_eval_eq_factorial_smul_taylor_coeff
    (p : K[X]) (a : K) (m : ℕ) :
    (derivative^[m] p).eval a = (m.factorial : K) * (taylor a p).coeff m := by
  have h := congrFun (factorial_smul_hasseDeriv (R := K) (k := m)) p
  rw [taylor_coeff, ← h]
  simp [nsmul_eq_mul]

/-- **Consistency with the parent entry.** Over a characteristic-zero field the Taylor-form
    factor theorem is *equivalent* to the parent's iterated-derivative form
    (`factor-remainder-theorem-oq-01`): the first `k` Taylor coefficients of `p` at `a` vanish
    iff the first `k` iterated derivatives of `p` vanish at `a`. The two characterizations of
    multiplicity coincide because `m! ≠ 0`. -/
theorem pow_dvd_iff_iterate_derivative_eval_eq_zero {p : K[X]} {a : K} {k : ℕ} :
    (X - C a) ^ k ∣ p ↔ ∀ m < k, (derivative^[m] p).eval a = 0 := by
  rw [pow_dvd_iff_taylor_coeff_eq_zero]
  refine forall₂_congr fun m _ => ?_
  rw [iterate_derivative_eval_eq_factorial_smul_taylor_coeff]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h
    have hfac : (m.factorial : K) ≠ 0 := by
      exact_mod_cast m.factorial_ne_zero
    exact (mul_eq_zero.mp h).resolve_left hfac

end CharZero

end FactorRemainderTheoremOQ01OQ01
