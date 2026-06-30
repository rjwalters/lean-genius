import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

/-
# Euler identity OQ-01 → OQ-02 → OQ-01: Euler's formula from the Taylor series as *definitions*

The parent chain proves Euler's formula `e^{ix} = cos x + i·sin x` by **starting** from
Mathlib's definition `cos z = (e^{iz} + e^{−iz})/2` and **deriving** the power series
`cos z = Σ (−1)ⁿ z²ⁿ/(2n)!`. This entry **reverses the foundational dependency** requested by
the open question:

> *Take the Taylor series `sin x = Σ (−1)ᵏ x^{2k+1}/(2k+1)!` and `cos x = Σ (−1)ᵏ x^{2k}/(2k)!`
> as the definitions of the trigonometric functions, then prove Euler's exponential formula.*

So here `cosSeries` and `sinSeries` are **defined** by their Maclaurin series, and Euler's
formula is obtained **directly from the exponential series** `e^w = Σ wⁿ/n!`: regrouping the
sum over `ℕ` into its even-indexed and odd-indexed parts (`n = 2k` and `n = 2k+1`) splits
`e^{iz}` into exactly `cosSeries z + i·sinSeries z`. No appeal to the value of `Complex.cos`
is made in the core derivation `hasSum_euler`/`euler_formula`; we only invoke Mathlib's cosine
*at the very end* to identify our series-definitions with the standard functions and to recover
Euler's identity `e^{iπ} = −1`.

The even/odd regrouping uses `Nat.divModEquiv 2 : ℕ ≃ ℕ × Fin 2` together with
`HasSum.prod_fiberwise`, mirroring (in the opposite logical direction) Mathlib's own
`Complex.hasSum_cos`. `0` axioms, `0` sorries.

## Main results

* `cosSeries`, `sinSeries` : cosine and sine **defined** as their Maclaurin series.
* `summable_cosTerm`, `summable_sinTerm` : the defining series converge (comparison with `e^{‖z‖}`).
* `hasSum_euler` : `e^{iz}` is the sum of the interleaved series `cosTerm k + i·sinTerm k`,
  obtained purely from the exponential series by even/odd regrouping.
* `euler_formula` : `e^{iz} = cosSeries z + i·sinSeries z` — Euler's formula from the series.
* `cosSeries_eq_cos`, `sinSeries_eq_sin` : the series-definitions agree with `Complex.cos/sin`.
* `pythagoras` : `cosSeries z ^ 2 + sinSeries z ^ 2 = 1`.
* `euler_identity` : `e^{iπ} = −1`.
-/

namespace EulerIdentityOQ01OQ02OQ01

open Complex NormedSpace
open scoped Nat

/-- **Cosine, defined by its Maclaurin series** `cos z := Σₖ (−1)ᵏ z²ᵏ/(2k)!`. -/
noncomputable def cosSeries (z : ℂ) : ℂ := ∑' k : ℕ, (-1) ^ k * z ^ (2 * k) / (2 * k)!

/-- **Sine, defined by its Maclaurin series** `sin z := Σₖ (−1)ᵏ z^{2k+1}/(2k+1)!`. -/
noncomputable def sinSeries (z : ℂ) : ℂ := ∑' k : ℕ, (-1) ^ k * z ^ (2 * k + 1) / (2 * k + 1)!

/-- The cosine series converges, by comparison with the exponential series for `‖z‖`. -/
theorem summable_cosTerm (z : ℂ) :
    Summable (fun k : ℕ => (-1) ^ k * z ^ (2 * k) / ((2 * k)! : ℂ)) := by
  apply Summable.of_norm_bounded (g := fun k : ℕ => ‖z‖ ^ (2 * k) / ((2 * k)! : ℝ))
  · exact (Real.summable_pow_div_factorial ‖z‖).comp_injective
      (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  · intro k
    refine le_of_eq ?_
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]

/-- The sine series converges, by comparison with the exponential series for `‖z‖`. -/
theorem summable_sinTerm (z : ℂ) :
    Summable (fun k : ℕ => (-1) ^ k * z ^ (2 * k + 1) / ((2 * k + 1)! : ℂ)) := by
  apply Summable.of_norm_bounded (g := fun k : ℕ => ‖z‖ ^ (2 * k + 1) / ((2 * k + 1)! : ℝ))
  · exact (Real.summable_pow_div_factorial ‖z‖).comp_injective
      ((add_left_injective 1).comp (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)))
  · intro k
    refine le_of_eq ?_
    rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]

/-- **Euler's formula at the level of series.** The exponential series `e^{iz} = Σ (iz)ⁿ/n!`,
    regrouped into its even-indexed (`n = 2k`) and odd-indexed (`n = 2k+1`) parts, has sum equal
    to the interleaved cosine/sine terms. This is the heart of the reversed dependency: it is
    proved *only* from the exponential series, never from `Complex.cos`. -/
theorem hasSum_euler (z : ℂ) :
    HasSum (fun k : ℕ =>
        (-1) ^ k * z ^ (2 * k) / ((2 * k)! : ℂ)
        + Complex.I * ((-1) ^ k * z ^ (2 * k + 1) / ((2 * k + 1)! : ℂ)))
      (Complex.exp (z * I)) := by
  rw [Complex.exp_eq_exp_ℂ]
  have h := expSeries_div_hasSum_exp ℂ (z * I)
  replace h := (Nat.divModEquiv 2).symm.hasSum_iff.mpr h
  dsimp [Function.comp_def] at h
  simp_rw [← mul_comm 2 _] at h
  refine h.prod_fiberwise fun k => ?_
  dsimp only
  convert hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, add_zero]
  rw [mul_pow z I (2 * k), mul_pow z I (2 * k + 1), pow_succ I (2 * k), pow_mul I 2 k,
    Complex.I_sq]
  ring

/-- **Euler's formula.** `e^{iz} = cosSeries z + i·sinSeries z`, where `cosSeries`/`sinSeries`
    are *defined* as their Maclaurin series. Obtained by combining the convergent series with
    `hasSum_euler` and uniqueness of sums. -/
theorem euler_formula (z : ℂ) :
    Complex.exp (z * I) = cosSeries z + Complex.I * sinSeries z := by
  have hc : HasSum (fun k : ℕ => (-1) ^ k * z ^ (2 * k) / ((2 * k)! : ℂ)) (cosSeries z) :=
    (summable_cosTerm z).hasSum
  have hs : HasSum (fun k : ℕ => (-1) ^ k * z ^ (2 * k + 1) / ((2 * k + 1)! : ℂ)) (sinSeries z) :=
    (summable_sinTerm z).hasSum
  exact (hasSum_euler z).unique (hc.add (hs.mul_left Complex.I))

/-- The cosine series-definition coincides with `Complex.cos` (Mathlib `cos_eq_tsum`). -/
theorem cosSeries_eq_cos (z : ℂ) : cosSeries z = Complex.cos z :=
  (Complex.cos_eq_tsum z).symm

/-- The sine series-definition coincides with `Complex.sin` (Mathlib `sin_eq_tsum`). -/
theorem sinSeries_eq_sin (z : ℂ) : sinSeries z = Complex.sin z :=
  (Complex.sin_eq_tsum z).symm

/-- The Pythagorean identity holds for the series-definitions: `cos²+sin² = 1`. -/
theorem pythagoras (z : ℂ) : cosSeries z ^ 2 + sinSeries z ^ 2 = 1 := by
  rw [cosSeries_eq_cos, sinSeries_eq_sin, Complex.cos_sq_add_sin_sq]

/-- The classical real form: `e^{ix} = cos x + i·sin x` with the series-defined functions. -/
theorem euler_formula_real (x : ℝ) :
    Complex.exp ((x : ℂ) * I) = cosSeries x + Complex.I * sinSeries x :=
  euler_formula x

/-- **Euler's identity** `e^{iπ} = −1`, recovered within the series framework. -/
theorem euler_identity : Complex.exp ((Real.pi : ℂ) * I) = -1 := by
  rw [euler_formula, cosSeries_eq_cos, sinSeries_eq_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]
  norm_num

end EulerIdentityOQ01OQ02OQ01
