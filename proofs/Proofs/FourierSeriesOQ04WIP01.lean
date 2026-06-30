import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Fourier Series OQ-04 (wip-01): a genuine multi-dimensional Fourier coefficient

The parent scaffold (`FourierSeriesOQ04.lean`) models the `n`-torus as `Fin n → ℝ` and
leaves the Fourier coefficient as a **placeholder**:
```
noncomputable def fourierCoeff (f : Torus n → ℂ) (k : MultiIndex n) : ℂ := 0  -- placeholder
```
Its OQ-04 asks:

> *Can the placeholder `fourierCoeff` be implemented in Lean 4 using Mathlib's integration
> and Haar measure on compact groups? A concrete path is `Fin n → AddCircle (1 : ℝ)` with
> the product Haar measure, integrating `f(x) · conj(e^{2πi k·x})`.*

This file follows exactly that path. We model the `n`-torus as `Fin n → AddCircle (1 : ℝ)`,
build the `n`-dimensional Fourier character `e_k(x) = ∏ᵢ eᵢ(xᵢ)` from Mathlib's
`fourier : ℤ → C(AddCircle T, ℂ)`, and define the genuine Fourier coefficient

`f̂(k) = ∫_{Tⁿ} f(x) · conj(e_k(x)) dHaar`

with the product Haar measure (the default `volume`, since for `T = 1` the circle Haar
measure is `volume`). We then prove the defining algebraic properties of the character —
it is a group homomorphism `ℤⁿ → ℂˣ` of modulus `1` — and the linearity of the coefficient.

## Main results

* `torusChar` / `fourierCoeffND` : the genuine character and coefficient (no placeholders).
* `torusChar_zero`, `torusChar_add`, `torusChar_neg`, `norm_torusChar` : the character is a
  unimodular homomorphism `(ℤⁿ, +) → (ℂ, ×)`.
* `fourierCoeffND_const_mul`, `fourierCoeffND_zero_fun` : linearity facts for the coefficient.
-/

namespace FourierSeriesOQ04WIP01

open MeasureTheory Complex Finset
open scoped Real
open ComplexConjugate

/-- The `n`-torus `(ℝ/ℤ)ⁿ`, modelled as a product of unit circles `AddCircle (1 : ℝ)`. -/
abbrev Torus (n : ℕ) : Type := Fin n → AddCircle (1 : ℝ)

/-- A multi-index `k ∈ ℤⁿ` indexing the `n`-dimensional Fourier characters. -/
abbrev MultiIndex (n : ℕ) : Type := Fin n → ℤ

/-- **The `n`-dimensional Fourier character** `e_k(x) = ∏ᵢ e^{2πi kᵢ xᵢ}`, built as the
    product of Mathlib's one-dimensional characters `fourier (kᵢ) (xᵢ)`. -/
noncomputable def torusChar {n : ℕ} (k : MultiIndex n) (x : Torus n) : ℂ :=
  ∏ i, fourier (k i) (x i)

/-- **The genuine multi-dimensional Fourier coefficient**, replacing the parent scaffold's
    placeholder `fourierCoeff := 0`:
    `f̂(k) = ∫_{Tⁿ} f(x) · conj(e_k(x)) dHaar`, integrated against the product Haar measure
    (`volume` on `Fin n → AddCircle 1`). -/
noncomputable def fourierCoeffND {n : ℕ} (f : Torus n → ℂ) (k : MultiIndex n) : ℂ :=
  ∫ x, f x * conj (torusChar k x)

/-- Each one-dimensional character has modulus one. -/
theorem norm_fourier_apply {n : ℤ} (x : AddCircle (1 : ℝ)) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The character at the zero multi-index is constantly `1`. -/
theorem torusChar_zero {n : ℕ} (x : Torus n) : torusChar (0 : MultiIndex n) x = 1 := by
  unfold torusChar
  apply Finset.prod_eq_one
  intro i _
  simp [fourier_zero]

/-- **Homomorphism property.** The character converts addition of multi-indices into
    multiplication: `e_{j+k} = e_j · e_k`. -/
theorem torusChar_add {n : ℕ} (j k : MultiIndex n) (x : Torus n) :
    torusChar (j + k) x = torusChar j x * torusChar k x := by
  unfold torusChar
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.add_apply, fourier_add]

/-- The character at `-k` is the complex conjugate of the character at `k`. -/
theorem torusChar_neg {n : ℕ} (k : MultiIndex n) (x : Torus n) :
    torusChar (-k) x = conj (torusChar k x) := by
  unfold torusChar
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.neg_apply, fourier_neg]

/-- **Unimodularity.** Every value of the character lies on the unit circle. -/
theorem norm_torusChar {n : ℕ} (k : MultiIndex n) (x : Torus n) :
    ‖torusChar k x‖ = 1 := by
  unfold torusChar
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i _
  exact norm_fourier_apply (x i)

/-- The character `k ↦ e_k(x)` is a monoid homomorphism from `(ℤⁿ, +)` to `(ℂ, ×)`,
    packaging `torusChar_zero` and `torusChar_add`. -/
noncomputable def torusCharHom {n : ℕ} (x : Torus n) : Multiplicative (MultiIndex n) →* ℂ where
  toFun k := torusChar (Multiplicative.toAdd k) x
  map_one' := torusChar_zero x
  map_mul' j k := torusChar_add _ _ x

/-- **Linearity in the function (scalar multiples).** `(c·f)̂(k) = c · f̂(k)`. -/
theorem fourierCoeffND_const_mul {n : ℕ} (c : ℂ) (f : Torus n → ℂ) (k : MultiIndex n) :
    fourierCoeffND (fun x => c * f x) k = c * fourierCoeffND f k := by
  unfold fourierCoeffND
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The Fourier coefficient of the zero function vanishes. -/
theorem fourierCoeffND_zero_fun {n : ℕ} (k : MultiIndex n) :
    fourierCoeffND (fun _ => (0 : ℂ)) k = 0 := by
  unfold fourierCoeffND
  simp

end FourierSeriesOQ04WIP01
