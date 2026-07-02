/-
  Norm-rigidity of the complex inner product (cauchy-schwarz-oq-08-oq-01).

  The parent entry `cauchy-schwarz-oq-08` (`Norm-Rigidity of the Real Inner Product`)
  proves that over a *real* inner-product space the inner product is a function of the
  norm alone, so any **norm-preserving additive** map `f : F →+ F'` automatically
  preserves the inner product:
      ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ.
  The engine is the real polarization identity ⟪x,y⟫ = (‖x+y‖² − ‖x−y‖²)/4 — additivity
  alone lets one rewrite ‖f x ± f y‖ = ‖f (x ± y)‖ = ‖x ± y‖.

  Over ℂ (or any `RCLike` field) the norm no longer determines the inner product from the
  two "real-axis" diagonals ‖x ± y‖ alone: the imaginary part needs the *rotated*
  diagonals ‖x ± i·y‖.  The complex polarization identity (Mathlib
  `inner_eq_sum_norm_sq_div_four`) is

      ⟪x, y⟫ = ( ‖x+y‖² − ‖x−y‖²
                 + (‖x − i·y‖² − ‖x + i·y‖²)·i ) / 4,      i = RCLike.I.

  ## What this file adds

  The complex analogue of the parent's rigidity theorem.  For an ℝ-additive map `f`
  between `RCLike`-inner-product spaces we impose **two** metric hypotheses:

    * `hnorm : ∀ x, ‖f x‖ = ‖x‖`                       (preserves the norm), and
    * `hI    : ∀ x y, ‖f x + i·(f y)‖ = ‖x + i·y‖`      (preserves the rotated diagonal),

  and conclude `⟪f x, f y⟫ = ⟪x, y⟫`.  The second hypothesis is exactly the extra data the
  complex polarization identity consumes; the minus-diagonal version is *derived* from it
  by additivity (`hI x (−y)`), so a single rotated-diagonal hypothesis suffices.

  Because `RCLike.I = 0` when `𝕜 = ℝ`, the hypothesis `hI` becomes vacuous there and the
  statement collapses to the parent's real theorem — so this genuinely subsumes
  `cauchy-schwarz-oq-08`.  As corollaries we record orthogonality preservation, injectivity,
  the explicit ℂ specialization, and that a bundled `𝕜`-linear isometry preserves the inner
  product (its `hI` hypothesis is automatic, since a linear map commutes with `i·(·)`).

  Sorry-free and axiom-free.

  ## Main results
  - `inner_map_eq`              : norm- and rotated-diagonal-preserving additive `f` has
                                  `⟪f x, f y⟫ = ⟪x, y⟫`   (over any `RCLike 𝕜`)
  - `inner_map_eq_zero_iff`     : such maps preserve orthogonality
  - `injective_of_norm_preserving` : such maps are injective
  - `inner_map_eq_real`         : the `𝕜 = ℝ` collapse — `hI` is automatic (parent theorem)
  - `inner_map_eq_complex`      : the explicit `𝕜 = ℂ` statement with `Complex.I`
  - `inner_linearIsometry_eq`   : a bundled `𝕜`-linear isometry preserves the inner product
-/
import Mathlib

open scoped InnerProductSpace ComplexConjugate
open RCLike

namespace CauchySchwarzOQ08OQ01

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

/-- **Norm-rigidity of the `RCLike` inner product.**  Let `f : E →+ E'` be an *additive*
map between `𝕜`-inner-product spaces (`𝕜 = ℝ` or `ℂ`) that preserves the norm and the
rotated diagonal:
* `hnorm : ‖f x‖ = ‖x‖` for all `x`, and
* `hI    : ‖f x + RCLike.I • f y‖ = ‖x + RCLike.I • y‖` for all `x y`.

Then `f` preserves the inner product: `⟪f x, f y⟫ = ⟪x, y⟫`.

Only additivity is used (no `𝕜`-linearity): the four norms appearing in the complex
polarization identity are rewritten to the corresponding norms of `x, y`, three of them via
additivity (`f x ± f y = f (x ± y)`) and the last (`‖f x − i·f y‖`) from `hI` at `-y`. -/
theorem inner_map_eq (f : E →+ E') (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (hI : ∀ x y, ‖f x + (I : 𝕜) • f y‖ = ‖x + (I : 𝕜) • y‖) (x y : E) :
    inner 𝕜 (f x) (f y) = inner 𝕜 x y := by
  -- The rotated *minus*-diagonal follows from `hI` applied at `-y`, using additivity.
  have hIm : ‖f x - (I : 𝕜) • f y‖ = ‖x - (I : 𝕜) • y‖ := by
    have h := hI x (-y)
    simpa only [map_neg, smul_neg, sub_eq_add_neg] using h
  rw [inner_eq_sum_norm_sq_div_four (f x) (f y), ← map_add, ← map_sub, hnorm, hnorm,
    hI, hIm, ← inner_eq_sum_norm_sq_div_four x y]

/-- Norm- and rotated-diagonal-preserving additive maps **preserve orthogonality**. -/
theorem inner_map_eq_zero_iff (f : E →+ E') (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (hI : ∀ x y, ‖f x + (I : 𝕜) • f y‖ = ‖x + (I : 𝕜) • y‖) (x y : E) :
    inner 𝕜 (f x) (f y) = 0 ↔ inner 𝕜 x y = 0 := by
  rw [inner_map_eq f hnorm hI]

omit [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] in
/-- Norm-preserving additive maps are **injective** (a vector of norm `0` is `0`).  Needs
only the norm hypothesis. -/
theorem injective_of_norm_preserving (f : E →+ E') (hnorm : ∀ x, ‖f x‖ = ‖x‖) :
    Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : ‖a‖ = 0 := by rw [← hnorm a, ha, norm_zero]
  exact norm_eq_zero.mp this

/-- **Real collapse.**  When `𝕜 = ℝ` the rotated-diagonal hypothesis is automatic
(`RCLike.I = 0`), so norm preservation alone forces preservation of the inner product.
This recovers the parent theorem `cauchy-schwarz-oq-08`. -/
theorem inner_map_eq_real {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']
    (f : F →+ F') (hnorm : ∀ x, ‖f x‖ = ‖x‖) (x y : F) :
    inner ℝ (f x) (f y) = inner ℝ x y := by
  refine inner_map_eq f hnorm ?_ x y
  intro a b
  simp only [RCLike.I_to_real, zero_smul, add_zero, hnorm]

/-- **Complex specialization.**  Over a complex inner-product space, an additive map
preserving the norm and the rotated diagonal `‖f x + i·f y‖ = ‖x + i·y‖` (with `i =
Complex.I`) preserves the complex inner product. -/
theorem inner_map_eq_complex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    (f : E →+ E') (hnorm : ∀ x, ‖f x‖ = ‖x‖)
    (hI : ∀ x y, ‖f x + Complex.I • f y‖ = ‖x + Complex.I • y‖) (x y : E) :
    inner ℂ (f x) (f y) = inner ℂ x y :=
  -- `(RCLike.I : ℂ) = Complex.I` definitionally (the `RCLike ℂ` instance sets `I := Complex.I`),
  -- so `hI` already has the shape `inner_map_eq` expects.
  inner_map_eq f hnorm hI x y

/-- A bundled `𝕜`-linear isometry preserves the inner product.  Its rotated-diagonal
hypothesis is automatic: `𝕜`-linearity gives `f x + i·f y = f (x + i·y)`, whose norm is
`‖x + i·y‖` by the isometry property.  This is the elementary reason Hilbert-space
isometries are unitary, obtained here purely from polarization. -/
theorem inner_linearIsometry_eq (f : E →ₗᵢ[𝕜] E') (x y : E) :
    inner 𝕜 (f x) (f y) = inner 𝕜 x y := by
  refine inner_map_eq f.toLinearMap.toAddMonoidHom f.norm_map ?_ x y
  intro a b
  rw [show f.toLinearMap.toAddMonoidHom a + (I : 𝕜) • f.toLinearMap.toAddMonoidHom b
        = f (a + (I : 𝕜) • b) by simp [map_add, map_smul], f.norm_map]

end CauchySchwarzOQ08OQ01
