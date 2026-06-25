/-
# Cauchy–Schwarz OQ-02 (leaf oq-05): the Riesz representation theorem in L²

The parent entry `cauchy-schwarz-oq-02` ("Hölder, L² Theory, and Minkowski") lists,
as its fifth open question:

> Formalize the Riesz representation theorem in L²: every bounded linear functional
> on L² is given by inner product with a unique element.

This file answers it. `L² = α →₂[μ] 𝕜` (Mathlib's `Lp 𝕜 2 μ`) is, for `RCLike 𝕜`, a
complete inner product space, so Mathlib's abstract Fréchet–Riesz representation
`InnerProductSpace.toDual 𝕜 E : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E` specializes to it. We
extract from that isometric equivalence the four statements that make up the
classical L² Riesz theorem:

* `riesz_L2_exists`        — existence of a representing element;
* `riesz_L2_inner_ext`     — an element of L² is determined by its inner products,
                              giving uniqueness;
* `riesz_L2_existsUnique`  — the packaged `∃!` form (the verbatim open question);
* `riesz_L2_integral`      — the **concrete L² form**: the functional is integration
                              against the representing element,
                              `g h = ∫ a, ⟪f a, h a⟫ ∂μ` (via `L2.inner_def`);
* `riesz_L2_norm`          — the representation is **isometric**, `‖f‖ = ‖g‖`,
                              because `toDual` is a linear isometry.

The integral form and the isometry are the genuinely L²-specific content beyond the
abstract Hilbert-space statement. This is the inner-product (Hilbert) route to Riesz,
complementary to the general-`Lp` duality entries in this tree, which take the harder
Radon–Nikodým / Hölder route valid for all `p`.

*Reference:* Riesz (1907); see also Mathlib `Mathlib.Analysis.InnerProductSpace.Dual`.
-/

import Mathlib

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace CauchySchwarzOQ02OQ05

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {𝕜 : Type*} [RCLike 𝕜]

/- `α →₂[μ] 𝕜` is `MeasureTheory.Lp 𝕜 2 μ`, the space of (a.e.-equivalence classes of)
square-integrable scalar functions. For `RCLike 𝕜` it is automatically a complete
inner product space, so all instances below are found by typeclass resolution. -/

/-- **Existence (Fréchet–Riesz in L²).** Every bounded linear functional `g` on `L²`
is given by inner product with some element `f`: `g h = ⟪f, h⟫` for all `h`.
The witness is `(InnerProductSpace.toDual 𝕜 _).symm g`. -/
theorem riesz_L2_exists (g : (α →₂[μ] 𝕜) →L[𝕜] 𝕜) :
    ∃ f : α →₂[μ] 𝕜, ∀ h : α →₂[μ] 𝕜, g h = ⟪f, h⟫_𝕜 :=
  ⟨(InnerProductSpace.toDual 𝕜 _).symm g,
    fun _ => (InnerProductSpace.toDual_symm_apply).symm⟩

/-- **Inner-product extensionality in L².** An element of `L²` is determined by its
inner products against all of `L²`. This furnishes the uniqueness half of Riesz. -/
theorem riesz_L2_inner_ext {f₁ f₂ : α →₂[μ] 𝕜}
    (h : ∀ h : α →₂[μ] 𝕜, ⟪f₁, h⟫_𝕜 = ⟪f₂, h⟫_𝕜) :
    f₁ = f₂ := by
  have := ext_inner_right 𝕜 (x := f₁) (y := f₂)
  exact this h

/-- **Riesz representation theorem in L² (∃! form).** Every bounded linear functional
on `L²` is inner product with a *unique* element. This is the parent's open question
verbatim: `∃! f, ∀ h, g h = ⟪f, h⟫`. -/
theorem riesz_L2_existsUnique (g : (α →₂[μ] 𝕜) →L[𝕜] 𝕜) :
    ∃! f : α →₂[μ] 𝕜, ∀ h : α →₂[μ] 𝕜, g h = ⟪f, h⟫_𝕜 := by
  obtain ⟨f, hf⟩ := riesz_L2_exists g
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  exact riesz_L2_inner_ext (fun h => by rw [← hf', ← hf])

/-- **Concrete L² form.** The representing element acts by integration: the functional
is `g h = ∫ a, ⟪f a, h a⟫ ∂μ`, the L² inner product unfolded pointwise (`L2.inner_def`).
This is the form in which the Riesz theorem is usually stated for `L²`. -/
theorem riesz_L2_integral (g : (α →₂[μ] 𝕜) →L[𝕜] 𝕜) :
    ∃ f : α →₂[μ] 𝕜, ∀ h : α →₂[μ] 𝕜,
      g h = ∫ a, ⟪f a, h a⟫_𝕜 ∂μ := by
  obtain ⟨f, hf⟩ := riesz_L2_exists g
  exact ⟨f, fun h => by rw [hf h, L2.inner_def]⟩

/-- **The representation is isometric.** The representing element has the same norm as
the functional, `‖f‖ = ‖g‖`, because `InnerProductSpace.toDual` is a linear isometry.
Equivalently, Riesz identifies `L²` with its dual norm-preservingly. -/
theorem riesz_L2_norm (g : (α →₂[μ] 𝕜) →L[𝕜] 𝕜) :
    ‖(InnerProductSpace.toDual 𝕜 (α →₂[μ] 𝕜)).symm g‖ = ‖g‖ :=
  LinearIsometryEquiv.norm_map _ g

end CauchySchwarzOQ02OQ05
