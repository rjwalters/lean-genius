/-
  Norm-rigidity of the real inner product (cauchy-schwarz-oq-08).

  Open question.  Formalize the polarization identity in a real inner-product space,
      ⟪x, y⟫ = (‖x + y‖² − ‖x − y‖²) / 4,
  and push it to its structural payoff: the inner product is *uniquely determined* by
  the norm.

  The bare identity is already in the gallery (cauchy-schwarz-oq-07,
  `real_inner_eq_norm_sq_diff_div_four`), where it appears as a one-line corollary of the
  parallelogram cross-term expansion.  This file takes the next step the identity is
  really *for*: because the inner product is a function of the norm alone, any map that
  preserves the norm must preserve the inner product.  Concretely we prove

      * polarization (recalled here so the file is self-contained), then
      * `inner_map_eq`: every **norm-preserving additive map** `f : F →+ F'` between real
        inner-product spaces satisfies `⟪f x, f y⟫ = ⟪x, y⟫`.  Note the hypothesis is only
        additivity (no ℝ-linearity) — polarization needs `f (x ± y) = f x ± f y` and
        nothing more.

  From this single theorem the usual rigidity facts follow as corollaries: norm-preserving
  additive maps preserve orthogonality, are injective, and ℝ-linear isometries are
  inner-product isometries.  This is the elementary reason isometries of Hilbert spaces are
  unitary, derived from polarization without Mathlib's bundled `LinearIsometry` machinery.

  Sorry-free and axiom-free.
-/
import Mathlib

open scoped InnerProductSpace RealInnerProductSpace

namespace CauchySchwarzOQ08

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

/-- **Polarization identity** over a real inner-product space (recalled, self-contained):
the inner product is recovered from the norm via the diagonals of the parallelogram,
`⟪x, y⟫ = (‖x + y‖² − ‖x − y‖²) / 4`.  Proved by expanding `‖x ± y‖²` through
`inner_self`; the two cross terms `±2⟪x, y⟫` combine. -/
theorem polarization (x y : F) :
    ⟪x, y⟫_ℝ = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 := by
  rw [norm_add_sq_real, norm_sub_sq_real]; ring

/-- **Norm-rigidity of the real inner product.**  Any *additive* map `f : F →+ F'` between
real inner-product spaces that preserves the norm automatically preserves the inner
product: `⟪f x, f y⟫ = ⟪x, y⟫`.

This is the structural content of polarization: since the inner product is a function of
the norm alone, a map that fixes the norm cannot move the inner product.  Only additivity
is used — `f (x + y) = f x + f y` and `f (x − y) = f x − f y` — not ℝ-linearity. -/
theorem inner_map_eq (f : F →+ F') (h : ∀ x, ‖f x‖ = ‖x‖) (x y : F) :
    ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [polarization (f x) (f y), polarization x y, ← map_add, ← map_sub, h, h]

/-- Norm-preserving additive maps **preserve orthogonality**: `f x ⟂ f y ↔ x ⟂ y`. -/
theorem inner_map_eq_zero_iff (f : F →+ F') (h : ∀ x, ‖f x‖ = ‖x‖) (x y : F) :
    ⟪f x, f y⟫_ℝ = 0 ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [inner_map_eq f h]

omit [InnerProductSpace ℝ F] [InnerProductSpace ℝ F'] in
/-- Norm-preserving additive maps are **injective** (a vector of norm `0` is `0`). -/
theorem injective_of_norm_preserving (f : F →+ F') (h : ∀ x, ‖f x‖ = ‖x‖) :
    Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : ‖a‖ = 0 := by rw [← h a, ha, norm_zero]
  exact norm_eq_zero.mp this

/-- ℝ-linear specialization: a **norm-preserving linear map preserves the inner product**.
The defining property of a linear isometry, obtained from `inner_map_eq` by forgetting
linearity down to the additive structure. -/
theorem inner_linearMap_eq (f : F →ₗ[ℝ] F') (h : ∀ x, ‖f x‖ = ‖x‖) (x y : F) :
    ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ :=
  inner_map_eq f.toAddMonoidHom h x y

/-- A bundled `LinearIsometry` over `ℝ` preserves the inner product, recovered through the
elementary polarization route of this file. -/
theorem inner_linearIsometry_eq (f : F →ₗᵢ[ℝ] F') (x y : F) :
    ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ :=
  inner_linearMap_eq f.toLinearMap f.norm_map x y

end CauchySchwarzOQ08
