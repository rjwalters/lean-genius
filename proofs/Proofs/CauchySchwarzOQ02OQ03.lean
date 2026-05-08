/-
  Complex Polarization Identity for Inner Product Spaces
  (cauchy-schwarz-oq-02-oq-03)

  The polarization identity recovers the inner product from the norm. In a
  REAL inner product space (parent OQ-02 file `CauchySchwarzOQ02.lean`,
  theorem `polarization_identity`), the identity is

      ⟪x, y⟫_ℝ = (‖x + y‖² - ‖x - y‖²) / 4.

  In a COMPLEX inner product space, the imaginary part of ⟪x, y⟫_ℂ is also
  needed. The classical "physics convention" (linear in the FIRST argument)
  formula is

      ⟪x, y⟫_phys = (‖x+y‖² - ‖x-y‖² + i (‖x+iy‖² - ‖x-iy‖²)) / 4.

  Mathlib uses the "math convention" (sesquilinear in the FIRST argument:
  `⟪c • x, y⟫ = star c * ⟪x, y⟫`, equivalently linear in the SECOND
  argument), so for Mathlib's `⟪·,·⟫_ℂ` the physics formula computes the
  COMPLEX CONJUGATE of the inner product:

      conj ⟪x, y⟫_ℂ = (‖x+y‖² - ‖x-y‖² + i (‖x+iy‖² - ‖x-iy‖²)) / 4
                    = ⟪y, x⟫_ℂ.

  In Mathlib's convention the polarization identity for `⟪x, y⟫_ℂ` itself
  reads

      ⟪x, y⟫_ℂ = (‖x+y‖² - ‖x-y‖² + i (‖x-iy‖² - ‖x+iy‖²)) / 4.

  This file proves all three statements and documents the convention
  mismatch. Results delegate to Mathlib's `norm_add_sq` + standard inner-
  product algebra (`inner_smul_right`, `inner_neg_right`, `inner_conj_symm`,
  `Complex.re_add_im`).

  Status: 0 sorries, 0 axioms.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace CauchySchwarzOQ02OQ03

open scoped ComplexConjugate
open Complex RCLike

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- ============================================================
-- Section 1: Squared-norm expansion (real and imaginary helpers)
-- ============================================================

/-- **Squared-norm expansion** in a complex inner product space:
    ‖x + y‖² = ‖x‖² + 2 · re ⟪x, y⟫_ℂ + ‖y‖². Direct restatement of `norm_add_sq` for ℂ. -/
theorem norm_add_sq_complex (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫_ℂ + ‖y‖ ^ 2 :=
  norm_add_sq (𝕜 := ℂ) x y

/-- **Squared-norm expansion** for subtraction: ‖x - y‖² = ‖x‖² - 2 · re ⟪x, y⟫_ℂ + ‖y‖².
    Derived from `norm_add_sq` by negating `y` (using `inner_neg_right` and `norm_neg`). -/
theorem norm_sub_sq_complex (x y : E) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫_ℂ + ‖y‖ ^ 2 := by
  have h : ‖x + (-y)‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, -y⟫_ℂ + ‖-y‖ ^ 2 :=
    norm_add_sq (𝕜 := ℂ) x (-y)
  rw [inner_neg_right, map_neg, norm_neg, sub_eq_add_neg] at h ⊢
  linarith

-- ============================================================
-- Section 2: Real-part recovery (‖x+y‖² - ‖x-y‖² = 4 · re ⟪x,y⟫)
-- ============================================================

/-- **Real-part recovery**: the difference of squared norms of `x ± y` equals
    `4 · re ⟪x, y⟫_ℂ`. -/
theorem norm_add_sq_sub_norm_sub_sq_eq_four_re (x y : E) :
    ‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 = 4 * re ⟪x, y⟫_ℂ := by
  rw [norm_add_sq_complex x y, norm_sub_sq_complex x y]; ring

-- ============================================================
-- Section 3: Imaginary-part recovery via I-shift
-- ============================================================

/-- The squared norm is invariant under multiplying by `Complex.I`:
    ‖I • y‖² = ‖y‖². -/
theorem norm_smul_I_sq (y : E) :
    ‖(Complex.I : ℂ) • y‖ ^ 2 = ‖y‖ ^ 2 := by
  rw [norm_smul, Complex.norm_I, one_mul]

/-- `re (I * z) = -(im z)` — multiplication by `I` rotates by π/2. -/
theorem re_I_mul (z : ℂ) : re (Complex.I * z) = -(im z) := by
  simp [Complex.mul_re, Complex.I_re, Complex.I_im]

/-- **Imaginary-part recovery** (Mathlib convention): the difference of squared
    norms of `x ± I•y` equals `-4 · im ⟪x, y⟫_ℂ`. The negative sign reflects
    Mathlib's sesquilinear-in-FIRST-argument convention; in the physics
    convention the same formula gives `+4 · im⟪x,y⟫`. -/
theorem norm_add_smul_I_sq_sub_eq_neg_four_im (x y : E) :
    ‖x + (Complex.I : ℂ) • y‖ ^ 2 - ‖x - (Complex.I : ℂ) • y‖ ^ 2 = -4 * im ⟪x, y⟫_ℂ := by
  -- Apply the (real-part) norm expansion to the pair (x, I•y).
  have h₁ := norm_add_sq_complex x ((Complex.I : ℂ) • y)
  have h₂ := norm_sub_sq_complex x ((Complex.I : ℂ) • y)
  -- ⟪x, I•y⟫ = I * ⟪x,y⟫ (linear in second argument).
  have hsmul : ⟪x, (Complex.I : ℂ) • y⟫_ℂ = (Complex.I : ℂ) * ⟪x, y⟫_ℂ :=
    inner_smul_right _ _ _
  -- Substitute into h₁ and h₂ and use re(I*z) = -im z, ‖I•y‖² = ‖y‖².
  rw [hsmul, re_I_mul, norm_smul_I_sq] at h₁ h₂
  linarith

-- ============================================================
-- Section 4: Per-component recovery formulas
-- ============================================================

/-- The real part of `⟪x, y⟫_ℂ` is recovered from norms — the same as the real
    polarization identity in `CauchySchwarzOQ02`. -/
theorem re_inner_eq_quarter_norm_diff (x y : E) :
    re ⟪x, y⟫_ℂ = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 := by
  have h := norm_add_sq_sub_norm_sub_sq_eq_four_re x y
  linarith

/-- The imaginary part of `⟪x, y⟫_ℂ` is recovered from norms with a NEGATIVE
    sign relative to the physics convention. -/
theorem im_inner_eq_quarter_norm_diff (x y : E) :
    im ⟪x, y⟫_ℂ = (‖x - (Complex.I : ℂ) • y‖ ^ 2 - ‖x + (Complex.I : ℂ) • y‖ ^ 2) / 4 := by
  have h := norm_add_smul_I_sq_sub_eq_neg_four_im x y
  linarith

-- ============================================================
-- Section 5: Main complex polarization identity (Mathlib convention)
-- ============================================================

/-- **Complex polarization identity (Mathlib convention)**: the complex inner
    product is recovered from norms via

      ⟪x, y⟫_ℂ = (‖x+y‖² - ‖x-y‖² + i (‖x-iy‖² - ‖x+iy‖²)) / 4.

    The sign on the imaginary correction is FLIPPED from the standard
    "physics convention" formula, because Mathlib's inner product is
    sesquilinear in the FIRST argument (`⟪c•x, y⟫ = star c * ⟪x,y⟫`),
    while the physics convention is sesquilinear in the SECOND. -/
theorem complex_polarization_mathlib (x y : E) :
    ⟪x, y⟫_ℂ =
      (((‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 : ℝ) : ℂ) +
       (Complex.I : ℂ) *
         (((‖x - (Complex.I : ℂ) • y‖ ^ 2 - ‖x + (Complex.I : ℂ) • y‖ ^ 2 : ℝ) : ℂ))) / 4 := by
  -- Decompose ⟪x,y⟫_ℂ = re + im*I via Complex.re_add_im, then substitute.
  have h_re := re_inner_eq_quarter_norm_diff x y
  have h_im := im_inner_eq_quarter_norm_diff x y
  have hz : ⟪x, y⟫_ℂ = (re ⟪x, y⟫_ℂ : ℂ) + (im ⟪x, y⟫_ℂ : ℂ) * Complex.I :=
    (Complex.re_add_im ⟪x, y⟫_ℂ).symm
  rw [hz, h_re, h_im]
  push_cast
  ring

-- ============================================================
-- Section 6: Slug's physics-convention formula computes ⟨y, x⟩ (= conj⟨x,y⟩)
-- ============================================================

/-- **Physics-convention polarization computes `⟪y, x⟫_ℂ` in Mathlib**: the
    slug's stated formula

      (‖f+g‖² - ‖f-g‖² + i (‖f+ig‖² - ‖f-ig‖²)) / 4

    equals `⟪y, x⟫_ℂ` in Mathlib (equivalently `conj ⟪x, y⟫_ℂ`), NOT
    `⟪x, y⟫_ℂ`. This is the convention-mismatch theorem. -/
theorem physics_polarization_eq_inner_swap (x y : E) :
    (((‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 : ℝ) : ℂ) +
     (Complex.I : ℂ) *
       (((‖x + (Complex.I : ℂ) • y‖ ^ 2 - ‖x - (Complex.I : ℂ) • y‖ ^ 2 : ℝ) : ℂ))) / 4
    = ⟪y, x⟫_ℂ := by
  -- Use ⟪y, x⟫_ℂ = conj ⟪x, y⟫_ℂ = re - i·im, and re = (‖x+y‖²-‖x-y‖²)/4,
  -- im = (‖x-iy‖²-‖x+iy‖²)/4 (with a SIGN FLIP from the physics formula).
  have h_re := re_inner_eq_quarter_norm_diff x y
  have h_im := im_inner_eq_quarter_norm_diff x y
  have hconj : (⟪y, x⟫_ℂ : ℂ) = conj ⟪x, y⟫_ℂ := (inner_conj_symm x y).symm
  rw [hconj]
  -- conj z = (re z : ℂ) - (im z : ℂ) * I
  have hconj_decomp : conj ⟪x, y⟫_ℂ =
      (re ⟪x, y⟫_ℂ : ℂ) - (im ⟪x, y⟫_ℂ : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp [Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
            Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
  rw [hconj_decomp, h_re, h_im]
  push_cast
  ring

/-- **Equivalent restatement**: the slug's physics formula equals `conj ⟪x, y⟫_ℂ`. -/
theorem physics_polarization_eq_conj (x y : E) :
    (((‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 : ℝ) : ℂ) +
     (Complex.I : ℂ) *
       (((‖x + (Complex.I : ℂ) • y‖ ^ 2 - ‖x - (Complex.I : ℂ) • y‖ ^ 2 : ℝ) : ℂ))) / 4
    = conj ⟪x, y⟫_ℂ := by
  rw [physics_polarization_eq_inner_swap x y]
  exact (inner_conj_symm x y).symm

-- ============================================================
-- Section 7: Equivalent algebraic forms and corollaries
-- ============================================================

/-- The two polarization formulas differ by exactly the imaginary correction:
    `mathlib_RHS - physics_RHS = ⟪x,y⟫_ℂ - ⟪y,x⟫_ℂ = 2i · im ⟪x, y⟫_ℂ`. -/
theorem mathlib_minus_physics (x y : E) :
    ⟪x, y⟫_ℂ - ⟪y, x⟫_ℂ = (2 * Complex.I) * (im ⟪x, y⟫_ℂ : ℂ) := by
  have hconj : (⟪y, x⟫_ℂ : ℂ) = conj ⟪x, y⟫_ℂ := (inner_conj_symm x y).symm
  rw [hconj]
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im]

#check @complex_polarization_mathlib
#check @physics_polarization_eq_inner_swap
#check @physics_polarization_eq_conj
#check @norm_add_sq_sub_norm_sub_sq_eq_four_re
#check @norm_add_smul_I_sq_sub_eq_neg_four_im
#check @re_inner_eq_quarter_norm_diff
#check @im_inner_eq_quarter_norm_diff
#check @mathlib_minus_physics

end CauchySchwarzOQ02OQ03
