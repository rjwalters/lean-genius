/-
Cauchy-Schwarz Inequality for Complex Inner Product Spaces

Open Question (cauchy-schwarz-oq-01):
"Can the Cauchy-Schwarz formalization be extended to complex inner product
spaces using Mathlib's inner product machinery?"

**Answer: YES** — Mathlib's `norm_inner_le_norm` works for any
`[RCLike 𝕜] [InnerProductSpace 𝕜 E]`, which includes both ℝ and ℂ cases.

This file formalizes:
1. Complex Cauchy-Schwarz: ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ · ‖v‖
2. The RCLike-uniform version (simultaneously covers ℝ and ℂ)
3. Derived inequalities:
   - Re(⟪u, v⟫_ℂ) ≤ ‖u‖ · ‖v‖
   - ‖⟪u, v⟫_ℂ‖² ≤ ‖u‖² · ‖v‖²
4. Complex self-inner product identity
5. Applications: Pythagorean theorem and triangle inequality for inner products

References:
- Schwarz, "Über ein die Flächen kleinsten Flächeninhalts betreffendes Problem" (1885)
- Mathlib: norm_inner_le_norm, inner_self_eq_norm_sq_to_K
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open scoped InnerProductSpace

namespace CauchySchwarzOQ01

-- ============================================================
-- PART 1: Complex Cauchy-Schwarz from Mathlib's RCLike
-- ============================================================

/-- **Complex Cauchy-Schwarz**
    ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ · ‖v‖ for u, v in a complex inner product space.
    Follows directly from Mathlib's `norm_inner_le_norm`. -/
theorem cauchy_schwarz_complex {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u v : E) :
    ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ :=
  norm_inner_le_norm u v

/-- **Real Cauchy-Schwarz** (uniform formulation via RCLike)
    ‖⟪u, v⟫_ℝ‖ ≤ ‖u‖ · ‖v‖ for real inner product spaces. -/
theorem cauchy_schwarz_real {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    ‖⟪u, v⟫_ℝ‖ ≤ ‖u‖ * ‖v‖ :=
  norm_inner_le_norm u v

/-- **Uniform Cauchy-Schwarz for any RCLike field 𝕜**
    Works simultaneously for 𝕜 = ℝ or 𝕜 = ℂ (or any [RCLike 𝕜]).
    This is the most general form Mathlib provides. -/
theorem cauchy_schwarz_rclike {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u v : E) : ‖⟪u, v⟫_𝕜‖ ≤ ‖u‖ * ‖v‖ :=
  norm_inner_le_norm u v

-- ============================================================
-- PART 2: Derived Inequalities for Complex Inner Products
-- ============================================================

/-- The real part of a complex inner product is bounded: Re(⟪u,v⟫_ℂ) ≤ ‖u‖·‖v‖ -/
theorem re_inner_le_norm_mul {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u v : E) :
    RCLike.re ⟪u, v⟫_ℂ ≤ ‖u‖ * ‖v‖ := by
  calc RCLike.re ⟪u, v⟫_ℂ
      ≤ ‖RCLike.re ⟪u, v⟫_ℂ‖ := le_abs_self _
    _ ≤ ‖⟪u, v⟫_ℂ‖ := RCLike.norm_re_le_norm _
    _ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v

/-- Complex Cauchy-Schwarz in squared form: ‖⟪u,v⟫_ℂ‖² ≤ ‖u‖² · ‖v‖² -/
theorem cauchy_schwarz_complex_sq {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u v : E) :
    ‖⟪u, v⟫_ℂ‖ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := cauchy_schwarz_complex u v
  have hinner : 0 ≤ ‖⟪u, v⟫_ℂ‖ := norm_nonneg _
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ * ‖v‖ - ‖⟪u, v⟫_ℂ‖), mul_nonneg hu hv]

-- ============================================================
-- PART 3: Complex Self-Inner Product Identity
-- ============================================================

/-- The complex inner product ⟪u, u⟫_ℂ equals ‖u‖² cast to ℂ -/
theorem inner_self_eq_norm_sq_complex {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : E) :
    ⟪u, u⟫_ℂ = (‖u‖ ^ 2 : ℂ) :=
  inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u

/-- The imaginary part of ⟪u, u⟫_ℂ is zero -/
theorem im_inner_self_zero {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : E) :
    (⟪u, u⟫_ℂ).im = 0 := by
  simp [inner_self_eq_norm_sq_complex, sq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]

-- ============================================================
-- PART 4: Triangle Inequality and Pythagorean Theorem
-- ============================================================

/-- Triangle inequality for inner products: ‖⟪u, v⟫ + ⟪v, w⟫‖ ≤ ‖u‖·‖v‖ + ‖v‖·‖w‖ -/
theorem inner_triangle {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u v w : E) :
    ‖⟪u, v⟫_𝕜 + ⟪v, w⟫_𝕜‖ ≤ ‖u‖ * ‖v‖ + ‖v‖ * ‖w‖ :=
  calc ‖⟪u, v⟫_𝕜 + ⟪v, w⟫_𝕜‖
      ≤ ‖⟪u, v⟫_𝕜‖ + ‖⟪v, w⟫_𝕜‖ := norm_add_le _ _
    _ ≤ ‖u‖ * ‖v‖ + ‖v‖ * ‖w‖ :=
        add_le_add (norm_inner_le_norm u v) (norm_inner_le_norm v w)

/-- Orthogonality implies Pythagoras: if ⟪u, v⟫_𝕜 = 0 then ‖u + v‖² = ‖u‖² + ‖v‖² -/
theorem pythagorean_from_orthogonal {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u v : E) (h : ⟪u, v⟫_𝕜 = 0) :
    ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := 𝕜), h, map_zero]
  ring

-- ============================================================
-- PART 5: Summary
-- ============================================================

/-- Summary: norm_inner_le_norm works uniformly for ℝ and ℂ -/
theorem cauchy_schwarz_works_for_complex :
    -- Direct statement for ℂ
    (∀ {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E] (u v : E),
      ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖) ∧
    -- Uniform statement for RCLike (covers both ℝ and ℂ)
    (∀ {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [SeminormedAddCommGroup E]
       [InnerProductSpace 𝕜 E] (u v : E), ‖⟪u, v⟫_𝕜‖ ≤ ‖u‖ * ‖v‖) :=
  ⟨fun u v => norm_inner_le_norm u v, fun u v => norm_inner_le_norm u v⟩

end CauchySchwarzOQ01
