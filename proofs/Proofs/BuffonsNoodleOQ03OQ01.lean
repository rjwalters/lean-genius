import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-!
# Buffon's Noodle in Higher Dimensions — the crossing factor in closed form (oq-03 · oq-01)

## What this proves

The parent file `BuffonsNoodleOQ03.lean` proves the higher-dimensional noodle law
`E = αₙ · L / d`, carrying the **crossing factor**

  `αₙ = 𝔼_{u ∼ S^{n-1}} |u₁|`

— the mean absolute value of a single coordinate of a uniformly random unit vector
in `ℝⁿ` — as an abstract nonnegative parameter, and establishing its base values
`α₂ = 2/π`, `α₃ = 1/2` together with the dimensional recurrence
`α_{n+2} = (n/(n+1))·αₙ`.

This file **evaluates `αₙ` in closed form**:

  `αₙ = Γ(n/2) / (√π · Γ((n+1)/2))`   for `n ≥ 2`.

### The spherical parametrisation

By rotational symmetry, the marginal law of one coordinate `u₁` of a uniform point
on `S^{n-1}` has density proportional to `(1 - t²)^{(n-3)/2}` on `[-1, 1]`. Writing
`t = cos θ` turns this into the angular average over `θ ∈ [0, π]` with weight
`sin^{n-2} θ`. Setting `m := n - 2` (so `n = m + 2`, `n ≥ 2`), the crossing factor is
the ratio of two elementary trigonometric integrals:

  `α_{m+2} = (∫₀^π |cos θ| sin^m θ dθ) / (∫₀^π sin^m θ dθ)`.

This file discharges that ratio. The two ingredients are:

* **Numerator** `∫₀^π |cos θ| sin^m θ dθ = 2/(m+1)` — elementary, by splitting at `π/2`
  and integrating `u = sin θ` (`crossing_numerator`).
* **Denominator** `∫₀^π sin^m θ dθ = √π · Γ((m+1)/2) / Γ(m/2+1)` — proved by a two-step
  induction matching Mathlib's reduction formula `integral_sin_pow` against the Gamma
  functional equation `Γ(s+1) = s·Γ(s)` (`integral_sin_pow_eq_Gamma`). Mathlib has the
  Wallis-product evaluation of this integral but **not** its Gamma closed form, so this
  lemma is new.

Combining via `Γ((m+3)/2) = ((m+1)/2)·Γ((m+1)/2)` gives the closed form
(`crossing_factor_eq_Gamma`).

## Relation to the open question as posed

The open question states the closed form as `Γ((n+1)/2)/(√π·Γ(n/2+1))`. That expression is
**off by one in the dimension**: it evaluates to `1/2` at `n = 2` and to `2/π` at `n = 1`,
whereas the genuine mean `𝔼|u₁|` on `S^{n-1}` equals `2/π` at `n = 2` and `1` at `n = 1`.
The OQ's expression is in fact `αₙ` for the sphere `Sⁿ ⊂ ℝ^{n+1}` (replace `n ↦ n+1`).
The corrected closed form proved here matches the parent file exactly:

* `crossing_factor_two   : α₂ = 2/π`   (recovers the planar Buffon constant),
* `crossing_factor_three : α₃ = 1/2`,
* `crossing_factor_recurrence : α_{m+2} = ((m+2)/(m+3))·α_m`
   (i.e. `α_{n+2} = (n/(n+1))·αₙ` with `n = m+2`).

## Status

0 axioms, 0 sorries, builds on Mathlib. The spherical → angular reduction (the marginal
density `(1-t²)^{(n-3)/2}`) is the standard, well-known step quoted above; this file proves
the closed-form *evaluation* of the resulting angular ratio, which is the mathematical content
the open question asks for.
-/

namespace BuffonsNoodleOQ03OQ01

open Real Set intervalIntegral MeasureTheory
open scoped Real

/-- The angular weight integral `D(m) = ∫₀^π sin^m θ dθ`. -/
noncomputable def sinPowIntegral (m : ℕ) : ℝ := ∫ θ in (0)..π, Real.sin θ ^ m

/-- The (unnormalised) crossing integral `N(m) = ∫₀^π |cos θ| sin^m θ dθ`. -/
noncomputable def crossingIntegral (m : ℕ) : ℝ := ∫ θ in (0)..π, |Real.cos θ| * Real.sin θ ^ m

/-- The crossing factor `α_{m+2} = N(m) / D(m)`, the mean `𝔼|u₁|` on `S^{m+1} ⊂ ℝ^{m+2}`. -/
noncomputable def crossingFactor (m : ℕ) : ℝ := crossingIntegral m / sinPowIntegral m

/-! ### Numerator: `∫₀^π |cos θ| sin^m θ dθ = 2/(m+1)` -/

/-- The numerator integral evaluates to `2/(m+1)`, by splitting at `π/2` and substituting
`u = sin θ` on each half. -/
theorem crossing_numerator (m : ℕ) : crossingIntegral m = 2 / (m + 1) := by
  have hcont : Continuous fun θ : ℝ => |Real.cos θ| * Real.sin θ ^ m := by fun_prop
  have hab : IntervalIntegrable (fun θ : ℝ => |Real.cos θ| * Real.sin θ ^ m) volume 0 (π / 2) :=
    hcont.intervalIntegrable _ _
  have hbc : IntervalIntegrable (fun θ : ℝ => |Real.cos θ| * Real.sin θ ^ m) volume (π / 2) π :=
    hcont.intervalIntegrable _ _
  -- left half: |cos θ| = cos θ
  have hL : (∫ θ in (0)..(π / 2), |Real.cos θ| * Real.sin θ ^ m) = 1 / (m + 1) := by
    have hcongr : (∫ θ in (0)..(π / 2), |Real.cos θ| * Real.sin θ ^ m)
        = ∫ θ in (0)..(π / 2), Real.sin θ ^ m * Real.cos θ := by
      apply integral_congr
      intro θ hθ
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ π / 2)] at hθ
      rw [abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)]
      ring
    rw [hcongr]
    have h := integral_sin_pow_mul_cos_pow_odd (a := 0) (b := π / 2) m 0
    simp only [Nat.mul_zero, Nat.zero_add, pow_one, pow_zero, mul_one] at h
    rw [h, Real.sin_zero, Real.sin_pi_div_two, integral_pow]
    simp
  -- right half: |cos θ| = -cos θ
  have hR : (∫ θ in (π / 2)..π, |Real.cos θ| * Real.sin θ ^ m) = 1 / (m + 1) := by
    have hcongr : (∫ θ in (π / 2)..π, |Real.cos θ| * Real.sin θ ^ m)
        = ∫ θ in (π / 2)..π, -(Real.sin θ ^ m * Real.cos θ) := by
      apply integral_congr
      intro θ hθ
      rw [uIcc_of_le (by linarith [Real.pi_pos] : (π / 2 : ℝ) ≤ π)] at hθ
      rw [abs_of_nonpos (Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1
        (by linarith [Real.pi_pos, hθ.2]))]
      ring
    rw [hcongr, integral_neg]
    have h := integral_sin_pow_mul_cos_pow_odd (a := π / 2) (b := π) m 0
    simp only [Nat.mul_zero, Nat.zero_add, pow_one, pow_zero, mul_one] at h
    rw [h, Real.sin_pi_div_two, Real.sin_pi, integral_pow]
    have hm : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  rw [crossingIntegral, ← integral_add_adjacent_intervals hab hbc, hL, hR]
  ring

/-! ### Denominator: the Gamma closed form of `∫₀^π sin^m` -/

/-- Base case `m = 0`: `∫₀^π 1 = π`. -/
theorem sinPowIntegral_zero : sinPowIntegral 0 = π := by
  simp [sinPowIntegral]

/-- Base case `m = 1`: `∫₀^π sin θ dθ = 2`. -/
theorem sinPowIntegral_one : sinPowIntegral 1 = 2 := by
  simp [sinPowIntegral, integral_sin]

/-- The Mathlib reduction formula specialised to `0..π`: the boundary term vanishes
because `sin 0 = sin π = 0`, leaving `D(m+2) = ((m+1)/(m+2))·D(m)`. -/
theorem sinPowIntegral_recurrence (m : ℕ) :
    sinPowIntegral (m + 2) = (m + 1) / (m + 2) * sinPowIntegral m := by
  simp only [sinPowIntegral]
  rw [integral_sin_pow]
  simp [Real.sin_pi]

/-- Gamma closed form of the denominator:
`∫₀^π sin^m θ dθ = √π · Γ((m+1)/2) / Γ(m/2 + 1)`.
Mathlib provides only the Wallis-product evaluation, so this is new. -/
theorem integral_sin_pow_eq_Gamma (m : ℕ) :
    sinPowIntegral m = √π * Real.Gamma ((m + 1) / 2) / Real.Gamma (m / 2 + 1) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    rw [sinPowIntegral_zero]
    push_cast
    rw [show ((0 : ℝ) + 1) / 2 = 1 / 2 by norm_num, show (0 : ℝ) / 2 + 1 = 1 by norm_num,
      Real.Gamma_one_half_eq, Real.Gamma_one, Real.mul_self_sqrt Real.pi_pos.le]
    norm_num
  | one =>
    rw [sinPowIntegral_one]
    push_cast
    rw [show ((1 : ℝ) + 1) / 2 = 1 by norm_num, show (1 : ℝ) / 2 + 1 = 1 / 2 + 1 by norm_num,
      Real.Gamma_one, Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Real.Gamma_one_half_eq]
    have hpi : √π ≠ 0 := by positivity
    field_simp
  | more m ih _ =>
    rw [sinPowIntegral_recurrence, ih]
    have e1 : ((m : ℝ) + 2 + 1) / 2 = (m + 1) / 2 + 1 := by ring
    have e2 : ((m : ℝ) + 2) / 2 + 1 = m / 2 + 1 + 1 := by ring
    have hm1 : ((m : ℝ) + 1) / 2 ≠ 0 := by positivity
    have hm2 : (m : ℝ) / 2 + 1 ≠ 0 := by positivity
    have hm2' : (m : ℝ) + 2 ≠ 0 := by positivity
    have hG2 : Real.Gamma ((m : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    push_cast
    rw [e1, e2, Real.Gamma_add_one hm1, Real.Gamma_add_one hm2]
    field_simp
    ring

/-! ### Main result: the closed form of the crossing factor -/

/-- **Crossing factor in closed form.** For `n = m + 2 ≥ 2`,
`αₙ = Γ(n/2) / (√π · Γ((n+1)/2))`, written here as
`α_{m+2} = Γ(m/2+1) / (√π · Γ((m+3)/2))`. -/
theorem crossing_factor_eq_Gamma (m : ℕ) :
    crossingFactor m = Real.Gamma (m / 2 + 1) / (√π * Real.Gamma ((m + 3) / 2)) := by
  simp only [crossingFactor]
  rw [crossing_numerator, integral_sin_pow_eq_Gamma]
  have e3 : ((m : ℝ) + 3) / 2 = (m + 1) / 2 + 1 := by ring
  have hm1 : ((m : ℝ) + 1) / 2 ≠ 0 := by positivity
  have hm1' : (m : ℝ) + 1 ≠ 0 := by positivity
  have hpi : √π ≠ 0 := by positivity
  have hG1 : Real.Gamma ((m : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hG2 : Real.Gamma (((m : ℝ) + 1) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [e3, Real.Gamma_add_one hm1]
  field_simp
  ring

/-! ### Consequences matching the parent file -/

/-- The dimensional recurrence `α_{m+2} = ((m+2)/(m+3))·α_m` (i.e. `α_{n+2} = (n/(n+1))αₙ`
with `n = m+2`), derived directly from the integral recurrences. -/
theorem crossing_factor_recurrence (m : ℕ) :
    crossingFactor (m + 2) = (m + 2) / (m + 3) * crossingFactor m := by
  have hD : sinPowIntegral m ≠ 0 := by
    rw [sinPowIntegral]; exact (integral_sin_pow_pos (n := m)).ne'
  simp only [crossingFactor]
  rw [crossing_numerator (m + 2), crossing_numerator m, sinPowIntegral_recurrence]
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hm3 : (m : ℝ) + 3 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Planar value `α₂ = 2/π`: recovers Buffon's needle constant. -/
theorem crossing_factor_two : crossingFactor 0 = 2 / π := by
  rw [crossing_factor_eq_Gamma]
  push_cast
  rw [show (0 : ℝ) / 2 + 1 = 1 by norm_num, show ((0 : ℝ) + 3) / 2 = 1 / 2 + 1 by norm_num,
    Real.Gamma_one, Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Real.Gamma_one_half_eq]
  have hpi : √π ≠ 0 := by positivity
  have hsq : √π * √π = π := Real.mul_self_sqrt Real.pi_pos.le
  rw [div_eq_div_iff (by positivity) (by positivity)]
  nlinarith [hsq, Real.pi_pos]

/-- Spatial value `α₃ = 1/2`. -/
theorem crossing_factor_three : crossingFactor 1 = 1 / 2 := by
  rw [crossing_factor_eq_Gamma]
  push_cast
  rw [show (1 : ℝ) / 2 + 1 = 1 / 2 + 1 by norm_num, show ((1 : ℝ) + 3) / 2 = 1 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0), Real.Gamma_one_half_eq,
    Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0), Real.Gamma_one]
  have hpi : √π ≠ 0 := by positivity
  field_simp

end BuffonsNoodleOQ03OQ01
