/-
# Orthonormality of the n-dimensional Fourier characters on the torus

Research: fourier-series-oq-04-wip-01-oq-01
Parent:   fourier-series-oq-04-wip-01 (the genuine multi-dimensional Fourier coefficient)

The parent built the `n`-dimensional Fourier character
`e_k(x) = ∏ᵢ fourier (kᵢ) (xᵢ)` on the torus `Tⁿ = (ℝ/ℤ)ⁿ = Fin n → AddCircle 1`
and the genuine Fourier coefficient `f̂(k) = ∫_{Tⁿ} f(x)·conj(e_k(x))`, proving the
*algebraic* facts (the character is a unimodular homomorphism `(ℤⁿ,+) → (ℂ,×)`).

What was missing — and what the parent's open question asks for as the heart of any
Parseval/Plancherel statement — is the **orthonormality** of these characters with
respect to the `L²(Tⁿ)` inner product:

  `∫_{Tⁿ} e_j(x)·conj(e_k(x)) dx = δ_{j,k}`   (`torusChar_orthonormal`).

This is the genuinely multi-dimensional analytic fact. It is proved by reducing to
Mathlib's one-dimensional orthonormality (`orthonormal_fourier`, the orthonormal
basis `fourier n` of `L²(AddCircle 1)`) along **two** bridges:

* **Fubini / product measure** (`MeasureTheory.integral_fintype_prod_volume_eq_prod`):
  the integral of the tensor product `∏ᵢ gᵢ(xᵢ)` over the product torus factors as
  the product `∏ᵢ ∫ gᵢ` of one-dimensional integrals.
* **The 1-D orthogonality relation** (`char1d_integral`): the concrete-integral form
  `∫_{AddCircle 1} fourier a · conj(fourier b) = δ_{a,b}`, extracted from Mathlib's
  `orthonormal_fourier` via `ContinuousMap.inner_toLp` (and `volume = haarAddCircle`
  on the unit circle, since `T = 1`).

The product of one-dimensional Kronecker deltas `∏ᵢ δ_{jᵢ,kᵢ}` collapses to the
multi-index delta `δ_{j,k}` (a factor vanishes as soon as two coordinates differ).

This is the orthonormality core of Parseval; the full Plancherel identity
`∑_{k∈ℤⁿ} |f̂(k)|² = ∫_{Tⁿ} |f|²` additionally requires *completeness* of the
character system on `Tⁿ` (a tensor-product Hilbert-basis construction not yet in
Mathlib), recorded as the follow-up open question.
-/
import Mathlib
import Proofs.FourierSeriesOQ04WIP01

namespace FourierSeriesOQ04WIP01OQ01

open FourierSeriesOQ04WIP01 MeasureTheory Complex Finset AddCircle
open scoped Real
open ComplexConjugate

/-- **One-dimensional orthogonality, concrete-integral form.**
`∫_{AddCircle 1} fourier a (x) · conj(fourier b (x)) dx = δ_{a,b}`.

This is the content of Mathlib's `orthonormal_fourier` (the monomials `fourier n`
form an orthonormal family in `L²`) made explicit as an integral against `volume`
(which equals the Haar probability measure `haarAddCircle` on the unit circle, as
`T = 1`), via `ContinuousMap.inner_toLp`. -/
theorem char1d_integral (a b : ℤ) :
    ∫ x : AddCircle (1 : ℝ), fourier a x * conj (fourier b x) = if a = b then 1 else 0 := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) = haarAddCircle := by
    rw [volume_eq_smul_haarAddCircle]; simp
  have ho := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ)))) b a
  rw [ContinuousMap.inner_toLp] at ho
  -- ho : ∫ x, fourier a x * conj (fourier b x) ∂haarAddCircle = if b = a then 1 else 0
  rw [hvol, ho]
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

/-- **Orthonormality of the n-dimensional Fourier characters.**
`∫_{Tⁿ} e_j(x) · conj(e_k(x)) dx = δ_{j,k}`, where `e_k = torusChar k` and the integral
is over the product (Haar = `volume`) measure on `Tⁿ = Fin n → AddCircle 1`.

The tensor character splits the integrand into a product over coordinates; Fubini
factors the integral into one-dimensional integrals, each evaluated by
`char1d_integral`; the resulting product of Kronecker deltas collapses to the
multi-index delta. -/
theorem torusChar_orthonormal {n : ℕ} (j k : MultiIndex n) :
    ∫ x : Torus n, torusChar j x * conj (torusChar k x) = if j = k then 1 else 0 := by
  -- pointwise: the integrand is a product over coordinates
  have hpt : ∀ x : Torus n, torusChar j x * conj (torusChar k x)
      = ∏ i, fourier (j i) (x i) * conj (fourier (k i) (x i)) := by
    intro x
    unfold torusChar
    rw [map_prod, ← Finset.prod_mul_distrib]
  simp_rw [hpt]
  -- Fubini: integral of a tensor product factors
  rw [integral_fintype_prod_volume_eq_prod
        (fun i (x : AddCircle (1 : ℝ)) => fourier (j i) x * conj (fourier (k i) x))]
  -- each factor is a 1-D orthogonality relation
  rw [show (∏ i, ∫ x : AddCircle (1 : ℝ), fourier (j i) x * conj (fourier (k i) x))
        = ∏ i, (if j i = k i then (1 : ℂ) else 0) from
      Finset.prod_congr rfl (fun i _ => char1d_integral (j i) (k i))]
  -- product of coordinate-wise deltas is the multi-index delta
  by_cases hjk : j = k
  · subst hjk; simp
  · rw [if_neg hjk]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hjk
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- **Restated as the Fourier coefficient of a character.** The `j`-th Fourier
coefficient of the character `e_k` is `δ_{j,k}`: `fourierCoeffND (torusChar k) j = δ_{j,k}`.
This is the orthonormality relation phrased through the parent's coefficient
`fourierCoeffND`, the precise sense in which the characters are "an orthonormal system
read off by the Fourier transform". -/
theorem fourierCoeffND_torusChar {n : ℕ} (j k : MultiIndex n) :
    fourierCoeffND (torusChar k) j = if k = j then 1 else 0 := by
  unfold fourierCoeffND
  rw [torusChar_orthonormal k j]

end FourierSeriesOQ04WIP01OQ01
