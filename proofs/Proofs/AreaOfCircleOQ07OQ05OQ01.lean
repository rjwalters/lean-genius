import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-
# The General Even Moment of the Gaussian  (area-of-circle-oq-07-oq-05-oq-01)

## Open Question (area-of-circle-oq-07-oq-05-oq-01)
"Evaluate the general even moment
`∫_ℝ x^{2n} e^{-x²} dx = (2n-1)!!·√π / 2^n` by induction on `n`, with the
second moment (`n = 1`) as the base case, exhibiting the double-factorial
recursion that integration by parts generates."

## Answer

For every `n : ℕ`,

  `∫_{-∞}^{∞} x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2^n`.

The parent entry `area-of-circle-oq-07-oq-05` evaluated the second moment
(`n = 1`, value `√π/2`) by a single integration by parts on the whole line.
This entry lifts that one computation to **all** `n` by isolating the
double-factorial recursion it generates:

  `∫ x^{2(n+1)} e^{-x²} = (2n+1)/2 · ∫ x^{2n} e^{-x²}`     (`gaussian_even_moment_recursion`)

obtained by integrating `x^{2n+1} · (x e^{-x²})` by parts (with `x e^{-x²}` the
derivative of `-½ e^{-x²}`, boundary terms killed by Gaussian decay).  Folding
this recursion into the base value `∫ e^{-x²} = √π` and matching the
double-factorial step `(2(n+1)-1)‼ = (2n+1)·(2n-1)‼` gives the closed form
(`gaussian_even_moment`).

As a corollary the integral equals the half-integer Gamma special value
`Γ(n + 1/2)` (`gaussian_even_moment_eq_Gamma`): Mathlib records `Γ(n+1/2)` as a
double-factorial expression (`Real.Gamma_nat_add_half`), and our integral hits
exactly the same value — so the IBP-derived moment is the Gaussian integral
representation of that Gamma value.

No new axioms: every step is a routine consequence of existing Mathlib results
(`integral_gaussian`, the integration-by-parts lemma on `(-∞,∞)`, Gaussian-decay
`tendsto`, and the double-factorial API).
-/

open Real MeasureTheory Filter Topology Set
open scoped Nat

namespace AreaOfCircleOQ07OQ05OQ01

/-- **Integrability of `x^k e^{-x²}` for every natural power `k`.**
A power weight never beats the Gaussian decay, so each polynomial weighting of
the Gaussian is integrable over the whole line. -/
theorem integrable_pow_mul_gaussian (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-x ^ 2)) := by
  have hk : (-1 : ℝ) < (k : ℝ) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (k : ℝ)) hk
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Real.rpow_natCast, neg_one_mul]

/-- **Gaussian decay of a polynomial weight.** For every power `m`, the function
`x ↦ x^m e^{-x²}` tends to `0` at both ends of the real line, because the
Gaussian factor decays faster than any polynomial. This supplies the boundary
terms that vanish in the integration-by-parts recursion. -/
theorem tendsto_pow_mul_gaussian_cocompact (m : ℕ) :
    Tendsto (fun x : ℝ => x ^ m * Real.exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := 1) one_pos (m : ℝ)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h.congr (fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
    abs_of_pos (Real.exp_pos _), Real.rpow_natCast, neg_one_mul]

/-- **The even-moment recursion.**
`∫ x^{2(n+1)} e^{-x²} = (2n+1)/2 · ∫ x^{2n} e^{-x²}`, the double-factorial step
produced by integrating `x^{2n+1} · (x e^{-x²})` by parts on `(-∞, ∞)`. -/
theorem gaussian_even_moment_recursion (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * (n + 1)) * Real.exp (-x ^ 2)
      = (2 * (n : ℝ) + 1) / 2 * ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) := by
  -- `u = x^(2n+1)`, `u' = (2n+1) x^(2n)`.
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * n + 1))
      ((2 * (n : ℝ) + 1) * x ^ (2 * n)) x := by
    intro x
    simpa using hasDerivAt_pow (2 * n + 1) x
  -- `v = -½ e^{-x²}`, `v' = x e^{-x²}`.
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -(2 : ℝ)⁻¹ * Real.exp (-y ^ 2))
      (x * Real.exp (-x ^ 2)) x := by
    intro x
    have hsq : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
      simpa using (hasDerivAt_pow 2 x).neg
    have hexp := hsq.exp
    have hfin := hexp.const_mul (-(2 : ℝ)⁻¹)
    convert hfin using 1
    ring
  -- Integrability of `u·v' = x^{2n+2} e^{-x²}`.
  have huv' : Integrable (fun x : ℝ => x ^ (2 * n + 1) * (x * Real.exp (-x ^ 2))) := by
    have h := integrable_pow_mul_gaussian (2 * n + 2)
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    ring
  -- Integrability of `u'·v = (2n+1) x^{2n} · (-½ e^{-x²})`.
  have hu'v : Integrable (fun x : ℝ =>
      (2 * (n : ℝ) + 1) * x ^ (2 * n) * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2))) := by
    have h := (integrable_pow_mul_gaussian (2 * n)).const_mul
      ((2 * (n : ℝ) + 1) * -(2 : ℝ)⁻¹)
    refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    ring
  -- Boundary terms vanish at ±∞.
  have hbot : Tendsto (fun x : ℝ => x ^ (2 * n + 1) * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2)))
      atBot (𝓝 0) := by
    have hb : atBot ≤ cocompact ℝ := by rw [cocompact_eq_atBot_atTop]; exact le_sup_left
    have h := ((tendsto_pow_mul_gaussian_cocompact (2 * n + 1)).mono_left hb).const_mul
      (-(2 : ℝ)⁻¹)
    rw [mul_zero] at h
    refine Filter.Tendsto.congr (fun x => ?_) h
    ring
  have htop : Tendsto (fun x : ℝ => x ^ (2 * n + 1) * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2)))
      atTop (𝓝 0) := by
    have ht : atTop ≤ cocompact ℝ := by rw [cocompact_eq_atBot_atTop]; exact le_sup_right
    have h := ((tendsto_pow_mul_gaussian_cocompact (2 * n + 1)).mono_left ht).const_mul
      (-(2 : ℝ)⁻¹)
    rw [mul_zero] at h
    refine Filter.Tendsto.congr (fun x => ?_) h
    ring
  -- Integration by parts on `(-∞, ∞)`.
  have key := integral_mul_deriv_eq_deriv_mul (a' := (0 : ℝ)) (b' := (0 : ℝ))
    hu hv huv' hu'v hbot htop
  -- Pull the constants out of the remaining integral.
  have hev : ∫ x : ℝ,
      (2 * (n : ℝ) + 1) * x ^ (2 * n) * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2))
      = ((2 * (n : ℝ) + 1) * -(2 : ℝ)⁻¹) * ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    ring
  calc ∫ x : ℝ, x ^ (2 * (n + 1)) * Real.exp (-x ^ 2)
      = ∫ x : ℝ, x ^ (2 * n + 1) * (x * Real.exp (-x ^ 2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only []
        ring
    _ = (0 : ℝ) - 0 - ∫ x : ℝ,
          (2 * (n : ℝ) + 1) * x ^ (2 * n) * (-(2 : ℝ)⁻¹ * Real.exp (-x ^ 2)) := key
    _ = (2 * (n : ℝ) + 1) / 2 * ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) := by
        rw [hev]; ring

/-- **The general even moment of the standard Gaussian (closed form).**
`∫_{-∞}^{∞} x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2^n`, proved by induction on `n`
folding the integration-by-parts recursion into the base value `√π`. -/
theorem gaussian_even_moment (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2)
      = ((2 * n - 1)‼ : ℝ) * Real.sqrt Real.pi / 2 ^ n := by
  induction n with
  | zero =>
    have hg : ∫ x : ℝ, x ^ (2 * 0) * Real.exp (-x ^ 2) = Real.sqrt Real.pi := by
      simp only [Nat.mul_zero, pow_zero, one_mul]
      have := integral_gaussian 1
      simpa [neg_one_mul, div_one] using this
    rw [hg]
    norm_num [Nat.doubleFactorial]
  | succ n ih =>
    rw [gaussian_even_moment_recursion, ih]
    have hdf : ((2 * (n + 1) - 1)‼ : ℝ) = (2 * (n : ℝ) + 1) * ((2 * n - 1)‼ : ℝ) := by
      have h1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
      rw [h1, Nat.doubleFactorial_add_one]
      push_cast
      ring
    rw [hdf, pow_succ]
    ring

/-- **The even moment is the half-integer Gamma special value.**
`∫_{-∞}^{∞} x^{2n} e^{-x²} dx = Γ(n + 1/2)`. Mathlib records the right-hand side
as the double-factorial expression `(2n-1)‼ √π / 2^n` (`Real.Gamma_nat_add_half`);
our integration-by-parts moment hits exactly that value, so this integral is the
Gaussian representation of `Γ(n + 1/2)`. -/
theorem gaussian_even_moment_eq_Gamma (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) = Real.Gamma (n + 1 / 2) := by
  rw [gaussian_even_moment, Real.Gamma_nat_add_half]

/-- Sanity check: the `n = 1` instance recovers the parent's second moment
`∫ x² e^{-x²} = √π / 2`. -/
theorem gaussian_second_moment :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt Real.pi / 2 := by
  have h := gaussian_even_moment 1
  norm_num [Nat.doubleFactorial] at h
  simpa using h

end AreaOfCircleOQ07OQ05OQ01
