import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
import Proofs.AreaOfCircleOQ07OQ05

/-
# The Gaussian Second Moment as a Gamma Value  (area-of-circle-oq-07-oq-05-oq-02)

## Open Question (area-of-circle-oq-07-oq-05-oq-02)
"Recover √π/2 as the Gamma value `Γ(3/2)` via the substitution `u = x²` and
`Real.Gamma`, connecting the parent's Gaussian second moment to the
special-function world."

## Answer

The parent entry `area-of-circle-oq-07-oq-05` evaluates the **full-line second
moment** `∫_{ℝ} x² e^{-x²} dx = √π/2` by integration by parts.  This entry
re-derives the same value through the **Gamma function**, exposing the
substitution `u = x²` that turns the Gaussian moment into the Euler integral.

### The substitution bridge (the heart of the entry)

Euler's integral for the Gamma function reads
`Γ(s) = ∫_{0}^{∞} e^{-u} u^{s-1} du`.  For `s = 3/2` the exponent is `u^{1/2}`,
so substituting `u = x²` (`du = 2x dx`, `u^{1/2} = x` on the half-line) gives

  `Γ(3/2) = ∫_{0}^{∞} e^{-x²} · x · 2x dx = 2 ∫_{0}^{∞} x² e^{-x²} dx`,

i.e. the **half-line second moment equals `½·Γ(3/2)`**:

  **`gaussian_second_moment_Ioi`**:  `∫_{x>0} x² e^{-x²} = Γ(3/2) / 2`.

Lean's change-of-variables `integral_comp_rpow_Ioi_of_pos` (the very lemma
Mathlib uses for `Γ(1/2) = √π`) supplies the substitution; `Gamma_eq_integral`
supplies Euler's integral.

### The special value

`Γ(3/2) = √π/2` follows from the functional equation
`Γ(s+1) = s·Γ(s)` (`Real.Gamma_add_one`) and `Γ(1/2) = √π`
(`Real.Gamma_one_half_eq`):

  **`gamma_three_half`**:  `Γ(3/2) = √π/2`.

### Resolving the factor of two

The open question's phrasing "`√π/2 = ½·Γ(3/2)`" mixes the two moments: the
**half-line** moment is `½·Γ(3/2) = √π/4`, while the **full-line** moment — the
parent's headline value — is its double, `Γ(3/2) = √π/2`.  We record the clean
identification of the parent value with the Gamma value:

  **`gaussian_second_moment_eq_gamma`**:  `∫_{ℝ} x² e^{-x²} = Γ(3/2)`,

which combined with `gamma_three_half` reproduces the parent's `√π/2` as a
special value of the Gamma function — the requested connection.

## Relation to Mathlib

Mathlib has the Gamma machinery (`Gamma_eq_integral`, `Gamma_add_one`,
`Gamma_one_half_eq`, the half-integer values `Gamma_nat_add_one_add_half`) and
the substitution lemma `integral_comp_rpow_Ioi_of_pos`, but it does not connect
the Gaussian second moment to `Γ(3/2)`.  We assemble that bridge here, reusing
the parent's `gaussian_second_moment` for the full-line value.  No new axioms.
-/

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace AreaOfCircleOQ07OQ05OQ02

/-! ## Part I: The special value `Γ(3/2) = √π/2` -/

/-- **`Γ(3/2) = √π/2`.** From the functional equation `Γ(s+1) = s·Γ(s)` with
`s = 1/2` and the Gaussian special value `Γ(1/2) = √π`. -/
theorem gamma_three_half : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
  have h : Real.Gamma (1 / 2 + 1) = (1 / 2 : ℝ) * Real.Gamma (1 / 2) :=
    Real.Gamma_add_one (by norm_num)
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, h, Real.Gamma_one_half_eq]
  ring

/-! ## Part II: The substitution `u = x²` -/

/-- **The substitution bridge.**  Euler's integral `Γ(3/2) = ∫_{u>0} e^{-u}·u^{1/2}`
becomes, under `u = x²`, twice the half-line Gaussian second moment.  Hence

  `∫_{x>0} x² e^{-x²} = Γ(3/2) / 2`. -/
theorem gaussian_second_moment_Ioi :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x ^ 2) = Real.Gamma (3 / 2) / 2 := by
  -- Euler's integral form of `Γ(3/2)`.
  have hΓ : Real.Gamma (3 / 2)
      = ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ ((3 / 2 : ℝ) - 1) :=
    Real.Gamma_eq_integral (by norm_num)
  -- Substitute `u = x ^ 2` via the change-of-variables lemma.
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun u : ℝ => Real.exp (-u) * u ^ ((3 / 2 : ℝ) - 1)) (p := 2)
    (by norm_num)
  -- `hsub : ∫ x>0, (2 * x^(2-1)) • (e^{-x^2} * (x^2)^(1/2)) = ∫ u>0, e^{-u} u^{1/2}`.
  rw [hΓ, ← hsub]
  -- Reduce both sides to `∫ x>0, 2 * (x² e^{-x²})`.
  rw [eq_div_iff (two_ne_zero), mul_comm, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  -- rewrite the rpow occurrences `x ^ (2:ℝ)` to the monomial `x ^ 2`.
  have hpow2 : x ^ (2 : ℝ) = x ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hexp1 : x ^ ((2 : ℝ) - 1) = x := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have hhalf : (x ^ (2 : ℝ)) ^ ((3 / 2 : ℝ) - 1) = x := by
    rw [← Real.rpow_mul hx0.le, show (2 : ℝ) * ((3 / 2 : ℝ) - 1) = 1 by norm_num,
      Real.rpow_one]
  rw [smul_eq_mul, hexp1]
  dsimp only
  rw [hhalf, hpow2]
  ring

/-! ## Part III: The full-line moment is `Γ(3/2)` -/

/-- **The parent value as a Gamma value.**  The full-line Gaussian second moment
equals `Γ(3/2)`.  Combined with `gamma_three_half` this reproduces the parent's
`∫_{ℝ} x² e^{-x²} = √π/2` as a special value of the Gamma function. -/
theorem gaussian_second_moment_eq_gamma :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.Gamma (3 / 2) := by
  rw [AreaOfCircleOQ07OQ05.gaussian_second_moment, gamma_three_half]

/-- Consistency: the half-line moment is `√π/4`, i.e. `½·Γ(3/2)` — the value the
open question refers to. -/
theorem gaussian_second_moment_Ioi_eq :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt π / 4 := by
  rw [gaussian_second_moment_Ioi, gamma_three_half]; ring

end AreaOfCircleOQ07OQ05OQ02
