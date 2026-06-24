import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# Factor–remainder theorem OQ-01-OQ-02: the multiplicity version in *all* characteristics

The parent entry (`factor-remainder-theorem-oq-01`, `FactorRemainderTheoremOQ01`) proves the
multiplicity factor theorem

> `(X − a)ᵏ ∣ p ↔ p(a) = p′(a) = ⋯ = p^{(k−1)}(a) = 0`

but **only over a field of characteristic zero**, because its proof divides by the factorials
`m!` produced by ordinary iterated derivatives (`factorial_mem_nonZeroDivisors`).  In positive
characteristic this fails outright: over `ZMod p` the polynomial `Xᵖ` has *every* ordinary
derivative identically zero, so the characteristic-zero criterion would certify arbitrarily
high multiplicity at `0`.

The fix, due to Hasse, is the **divided-power (Hasse) derivative** `hasseDeriv m`, whose
`m`-th value is the Taylor coefficient `(taylor a p).coeff m` *without dividing by `m!`*.
This entry proves the multiplicity factor theorem in the Hasse form, which is valid over an
**arbitrary commutative ring** (every characteristic, and with **no** `p ≠ 0` hypothesis):

  `(X − a)ᵏ ∣ p ↔ ∀ m < k, (hasseDeriv m p)(a) = 0`.

## Main results

* `pow_X_sub_C_dvd_iff_taylor` : `(X − a)ᵏ ∣ p ↔ Xᵏ ∣ taylor a p`, transferring divisibility
  through the Taylor shift `X ↦ X + a`.
* `pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero` : the **Hasse multiplicity factor theorem**
  `(X − a)ᵏ ∣ p ↔ ∀ m < k, (hasseDeriv m p)(a) = 0`, over any `CommRing`.
* `factor_theorem` (`k = 1`) and `double_root_iff` (`k = 2`), now hypothesis-free in any
  characteristic.
* `le_rootMultiplicity_iff_hasseDeriv` : the multiplicity reading
  `k ≤ rootMultiplicity a p ↔ ∀ m < k, (hasseDeriv m p)(a) = 0`.
* `hasseDeriv_detects_char_p` : an explicit `ZMod 2` witness where the ordinary derivative is
  blind (`derivative (X²) = 0`) but the second Hasse derivative correctly refutes a higher
  multiplicity, so `(X)³ ∤ X²`.

The new content over Mathlib and the gallery is the characteristic-free divisibility
characterization of multiplicity via Hasse derivatives; Mathlib has `hasseDeriv`, `taylor`,
and `rootMultiplicity` but not this `iff`.
-/

namespace FactorRemainderTheoremOQ01OQ02

open Polynomial

variable {R : Type*} [CommRing R]

/-- **Divisibility transfers through the Taylor shift.** The substitution `X ↦ X + a` (which
realizes `taylor a` as `· .comp (X + C a)`) is a ring automorphism of `R[X]` carrying `X − a`
to `X`, so the factor `(X − a)ᵏ` divides `p` iff `Xᵏ` divides the Taylor expansion
`taylor a p`. -/
theorem pow_X_sub_C_dvd_iff_taylor (a : R) (k : ℕ) (p : R[X]) :
    (X - C a) ^ k ∣ p ↔ X ^ k ∣ taylor a p := by
  rw [taylor_apply]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.comp (X + C a), by
      rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, add_sub_cancel_right]⟩
  · rintro ⟨r, hr⟩
    refine ⟨r.comp (X - C a), ?_⟩
    have key : p = (p.comp (X + C a)).comp (X - C a) := by
      rw [comp_assoc]; simp [add_comp]
    rw [key, hr, mul_comp, pow_comp, X_comp]

/-- **The Hasse multiplicity factor theorem (all characteristics).** For a polynomial `p` over
any commutative ring `R`, the factor `(X − a)ᵏ` divides `p` if and only if `p` and its first
`k − 1` *Hasse* derivatives all vanish at `a`:

  `(X − a)ᵏ ∣ p ↔ ∀ m < k, (hasseDeriv m p)(a) = 0`.

Unlike the parent's `FactorRemainderTheoremOQ01.pow_dvd_iff_iterate_derivative_eval_eq_zero`,
this requires **no** characteristic hypothesis and **no** `p ≠ 0` hypothesis: the Hasse
derivative `hasseDeriv m` records the Taylor coefficient `(taylor a p).coeff m` without dividing
by `m!`, so it remains informative when `m!` vanishes in `R`. -/
theorem pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero (a : R) (k : ℕ) (p : R[X]) :
    (X - C a) ^ k ∣ p ↔ ∀ m < k, (hasseDeriv m p).eval a = 0 := by
  rw [pow_X_sub_C_dvd_iff_taylor, X_pow_dvd_iff]
  simp_rw [taylor_coeff]

/-- **Factor theorem** (`k = 1`): `(X − a) ∣ p ↔ p(a) = 0`, in any characteristic. -/
theorem factor_theorem {a : R} (p : R[X]) : (X - C a) ∣ p ↔ p.eval a = 0 := by
  rw [← pow_one (X - C a), pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero]
  simp [Nat.lt_one_iff]

/-- **Double-root criterion** (`k = 2`): `(X − a)² ∣ p ↔ p(a) = 0 ∧ p′(a) = 0`, valid in any
characteristic and with no `p ≠ 0` hypothesis (here `p′` is the ordinary derivative
`hasseDeriv 1 p = derivative p`). -/
theorem double_root_iff {a : R} (p : R[X]) :
    (X - C a) ^ 2 ∣ p ↔ p.eval a = 0 ∧ (derivative p).eval a = 0 := by
  rw [pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero]
  constructor
  · intro h
    exact ⟨by simpa [hasseDeriv_zero'] using h 0 (by norm_num),
           by simpa [hasseDeriv_one'] using h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ m hm
    interval_cases m
    · simpa [hasseDeriv_zero'] using h0
    · simpa [hasseDeriv_one'] using h1

/-- **Multiplicity reading.** For a nonzero polynomial `p`, the root multiplicity of `a` is at
least `k` iff the first `k` Hasse derivatives vanish at `a`. -/
theorem le_rootMultiplicity_iff_hasseDeriv {p : R[X]} (hp : p ≠ 0) {a : R} {k : ℕ} :
    k ≤ rootMultiplicity a p ↔ ∀ m < k, (hasseDeriv m p).eval a = 0 := by
  rw [le_rootMultiplicity_iff hp, pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero]

/-- **Why Hasse derivatives are needed in positive characteristic.** Over `ZMod 2` the ordinary
derivative of `X²` is identically `0`, so the characteristic-zero criterion (all ordinary
derivatives vanishing at `0`) would wrongly certify `(X)³ ∣ X²`.  The *second Hasse derivative*
evaluates to `1 ≠ 0` at `0`, and via the Hasse multiplicity factor theorem this correctly
refutes the divisibility: `(X)³ ∤ X²`. -/
theorem hasseDeriv_detects_char_p :
    derivative ((X : (ZMod 2)[X]) ^ 2) = 0 ∧
      (hasseDeriv 2 ((X : (ZMod 2)[X]) ^ 2)).eval 0 = 1 ∧
        ¬ (X - C (0 : ZMod 2)) ^ 3 ∣ (X : (ZMod 2)[X]) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [derivative_X_pow, h2, map_zero, zero_mul]
  · rw [← taylor_coeff, taylor_zero, coeff_X_pow]
    norm_num
  · rw [pow_X_sub_C_dvd_iff_hasseDeriv_eval_eq_zero]
    intro h
    have h2 := h 2 (by norm_num)
    rw [← taylor_coeff, taylor_zero, coeff_X_pow] at h2
    norm_num at h2

end FactorRemainderTheoremOQ01OQ02
