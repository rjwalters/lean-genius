import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

/-
# Complex Polarization Identity

## What This Proves
On any complex inner product space the inner product is completely determined by
the norm via the **complex polarization identity**:

  ⟪f, g⟫ = (‖f + g‖² - ‖f - g‖² + i‖f - i·g‖² - i‖f + i·g‖²) / 4

This is the ℂ-companion to the real polarization identity
`⟪f, g⟫_ℝ = (‖f + g‖² - ‖f - g‖²)/4` already in the gallery
(`CauchySchwarzOQ02.lean`, `polarization_identity`). The real identity only
recovers a *symmetric* bilinear form; over ℂ the inner product is *sesquilinear*,
so two extra norm evaluations (at `f ± i·g`) are needed to recover the imaginary
part. Together the real and complex versions show that on every (real or complex)
Hilbert space **the norm determines the inner product**.

## Convention
Mathlib's `inner` is conjugate-linear in the first argument and linear in the
second, with `RCLike.I` denoting the abstract imaginary unit (`= Complex.I` for
`𝕜 = ℂ`). All statements below follow that convention; the sign of the imaginary
terms is fixed by it.

## Status
- [x] Complex polarization identity over `RCLike 𝕜` (headline, wraps Mathlib)
- [x] Specialization to `𝕜 = ℂ` with `Complex.I`
- [x] Real part of the inner product from norms
- [x] Imaginary part of the inner product from norms
- [x] Complex parallelogram law
- [x] Norm determines the inner product (uniqueness corollary)

## References
- Mathlib `inner_eq_sum_norm_sq_div_four` (Analysis.InnerProductSpace.Basic)
- Jordan–von Neumann (1935): the parallelogram law characterises inner product
  spaces among normed spaces; polarization then reconstructs the product.
-/

noncomputable section

open RCLike

namespace ComplexPolarization

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Complex polarization identity** (general `RCLike` field).

The inner product is recovered from four squared norms:
`⟪f, g⟫ = (‖f+g‖² - ‖f-g‖² + (‖f - i·g‖² - ‖f + i·g‖²)·i) / 4`.
This is a typed wrapper of Mathlib's `inner_eq_sum_norm_sq_div_four`. -/
theorem polarization_identity_complex (f g : E) :
    inner 𝕜 f g =
      ((‖f + g‖ : 𝕜) ^ 2 - (‖f - g‖ : 𝕜) ^ 2 +
        ((‖f - (RCLike.I : 𝕜) • g‖ : 𝕜) ^ 2 - (‖f + (RCLike.I : 𝕜) • g‖ : 𝕜) ^ 2)
          * (RCLike.I : 𝕜)) / 4 :=
  inner_eq_sum_norm_sq_div_four f g

/-- **Real part** of the inner product from the norm:
`re ⟪f, g⟫ = (‖f+g‖² - ‖f-g‖²)/4`. Matches the real polarization identity. -/
theorem re_inner_eq_norm_polarization (f g : E) :
    RCLike.re (inner 𝕜 f g) = (‖f + g‖ ^ 2 - ‖f - g‖ ^ 2) / 4 := by
  simp only [pow_two]
  exact re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four f g

/-- **Imaginary part** of the inner product from the norm:
`im ⟪f, g⟫ = (‖f - i·g‖² - ‖f + i·g‖²)/4`. -/
theorem im_inner_eq_norm_polarization (f g : E) :
    RCLike.im (inner 𝕜 f g) =
      (‖f - (RCLike.I : 𝕜) • g‖ ^ 2 - ‖f + (RCLike.I : 𝕜) • g‖ ^ 2) / 4 := by
  simp only [pow_two]
  exact im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four f g

include 𝕜 in
/-- **Complex parallelogram law**: `‖f+g‖² + ‖f-g‖² = 2‖f‖² + 2‖g‖²`.
The norm of an inner product space satisfies the parallelogram law over any field. -/
theorem parallelogram_law_complex (f g : E) :
    ‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 = 2 * ‖f‖ ^ 2 + 2 * ‖g‖ ^ 2 := by
  have h := parallelogram_law_with_norm 𝕜 f g
  simp only [pow_two]
  linarith [h]

/-- **Uniqueness corollary**: the inner product is completely determined by the
norm. If `f₁, g₁` and `f₂, g₂` are pairwise equinormed in the four polarization
arguments, their inner products coincide. In particular the norm fixes `⟪f, g⟫`. -/
theorem inner_eq_of_norm_eq {f₁ g₁ f₂ g₂ : E}
    (h₁ : ‖f₁ + g₁‖ = ‖f₂ + g₂‖) (h₂ : ‖f₁ - g₁‖ = ‖f₂ - g₂‖)
    (h₃ : ‖f₁ - (RCLike.I : 𝕜) • g₁‖ = ‖f₂ - (RCLike.I : 𝕜) • g₂‖)
    (h₄ : ‖f₁ + (RCLike.I : 𝕜) • g₁‖ = ‖f₂ + (RCLike.I : 𝕜) • g₂‖) :
    inner 𝕜 f₁ g₁ = inner 𝕜 f₂ g₂ := by
  rw [polarization_identity_complex, polarization_identity_complex,
    h₁, h₂, h₃, h₄]

end ComplexPolarization

namespace ComplexPolarization

/-- **Complex polarization identity over ℂ**, stated with `Complex.I`.

`⟪f, g⟫ = (‖f+g‖² - ‖f-g‖² + (‖f - i·g‖² - ‖f + i·g‖²)·i) / 4`,
the concrete `𝕜 = ℂ` instance of `polarization_identity_complex`
(`Complex.I = RCLike.I` for the ℂ field). -/
theorem polarization_identity_C {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (f g : E) :
    inner ℂ f g =
      ((‖f + g‖ : ℂ) ^ 2 - (‖f - g‖ : ℂ) ^ 2 +
        ((‖f - Complex.I • g‖ : ℂ) ^ 2 - (‖f + Complex.I • g‖ : ℂ) ^ 2)
          * Complex.I) / 4 :=
  inner_eq_sum_norm_sq_div_four f g

end ComplexPolarization
