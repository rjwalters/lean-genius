/-
  The full complex polarization identity (cauchy-schwarz-oq-07-oq-02).

  Open question (from cauchy-schwarz-oq-07, "The Parallelogram Law").  The parent
  entry recovers the *real* inner product from the norm via the diagonals of a
  parallelogram,
      ⟪x, y⟫_ℝ = (‖x + y‖² − ‖x − y‖²) / 4,
  and asks to "extend the polarization corollary to the full complex form including
  the imaginary part".  Over ℂ the real diagonals alone no longer determine the inner
  product: one also needs the two *rotated* diagonals ‖x ± i·y‖, which read off the
  imaginary part.

  This file packages the full complex polarization identity in several equivalent
  shapes over an arbitrary complex inner-product space `G`:

  * the **complex form**
      ⟪x, y⟫ = (‖x+y‖² − ‖x−y‖² + (‖x − i•y‖² − ‖x + i•y‖²)·i) / 4,
    the ℂ specialization of Mathlib's `inner_eq_sum_norm_sq_div_four`;
  * the **split form**
      ⟪x, y⟫ = (‖x+y‖² − ‖x−y‖²)/4  +  i·(‖x − i•y‖² − ‖x + i•y‖²)/4,
    real part = the parent's diagonal formula, imaginary part = the rotated diagonals;
  * the **roots-of-unity form**
      ⟪x, y⟫ = (1/4) · Σ_{k<4} (−i)^k · ‖x + i^k • y‖²,
    a single cyclic sum over the four fourth-roots of unity 1, i, −1, −i — the discrete
    Fourier / character-sum packaging that makes the appearance of `i` structural rather
    than ad hoc;
  * the separated **real and imaginary parts** in the parent's squared (`^2`) style.

  As corollaries we record that the inner product is completely determined by the four
  diagonal norms ‖x±y‖, ‖x±i•y‖, and the resulting **orthogonality-from-norms** criterion
      ⟪x, y⟫ = 0  ↔  ‖x+y‖ = ‖x−y‖ ∧ ‖x + i•y‖ = ‖x − i•y‖,
  the complex refinement of the fact that in a real space perpendicularity is the single
  equal-diagonals condition ‖x+y‖ = ‖x−y‖.

  Everything is derived from Mathlib's `inner_eq_sum_norm_sq_div_four`; the value added
  over that lemma is the cyclic roots-of-unity reformulation, the clean split/`^2`
  packaging matching the parent entry, and the orthogonality criterion.

  Sorry-free and axiom-free.
-/
import Mathlib

open scoped InnerProductSpace

namespace CauchySchwarzOQ07OQ02

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- **The full complex polarization identity, complex form.**  The ℂ specialization of
Mathlib's `inner_eq_sum_norm_sq_div_four`, with the imaginary unit written as
`Complex.I`:
`⟪x, y⟫ = (‖x+y‖² − ‖x−y‖² + (‖x − i•y‖² − ‖x + i•y‖²)·i) / 4`. -/
theorem inner_eq_polarization_complex (x y : G) :
    ⟪x, y⟫_ℂ =
      ((‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2
        + ((‖x - Complex.I • y‖ : ℂ) ^ 2 - (‖x + Complex.I • y‖ : ℂ) ^ 2) * Complex.I) / 4 := by
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ), show (RCLike.I : ℂ) = Complex.I from rfl]
  norm_cast

/-- **The full complex polarization identity, split form.**  The inner product is
recovered from the norm as its real part (ordinary diagonals) plus `i` times its
imaginary part (rotated diagonals):
`⟪x, y⟫ = (‖x+y‖² − ‖x−y‖²)/4 + i·(‖x − i•y‖² − ‖x + i•y‖²)/4`. -/
theorem inner_eq_polarization_split (x y : G) :
    ⟪x, y⟫_ℂ =
      (((‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 : ℝ) : ℂ)
        + Complex.I * (((‖x - Complex.I • y‖ ^ 2 - ‖x + Complex.I • y‖ ^ 2) / 4 : ℝ) : ℂ) := by
  rw [inner_eq_polarization_complex]; push_cast; ring

/-- **Real part of the complex inner product**, in the parent entry's squared form:
`re ⟪x, y⟫ = (‖x + y‖² − ‖x − y‖²) / 4`.  Identical to the real polarization identity
of the parent — the real part sees only the two ordinary diagonals. -/
theorem re_inner_eq_diag_sq_div_four (x y : G) :
    (⟪x, y⟫_ℂ).re = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2) / 4 := by
  rw [inner_eq_polarization_split]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Imaginary part of the complex inner product**, in squared form:
`im ⟪x, y⟫ = (‖x − i•y‖² − ‖x + i•y‖²) / 4`.  The imaginary part is read off from the
two *rotated* diagonals ‖x ± i•y‖ — the genuinely complex content of polarization. -/
theorem im_inner_eq_rot_diag_sq_div_four (x y : G) :
    (⟪x, y⟫_ℂ).im = (‖x - Complex.I • y‖ ^ 2 - ‖x + Complex.I • y‖ ^ 2) / 4 := by
  rw [inner_eq_polarization_split]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **The full complex polarization identity, roots-of-unity form.**  The inner product
is a single cyclic sum over the four fourth-roots of unity `1, i, −1, −i`:
`⟪x, y⟫ = (1/4) · Σ_{k<4} (−i)^k · ‖x + i^k • y‖²`.
Expanding the sum recovers the split form: the coefficients `(−i)^k = 1, −i, −1, i`
weight the four diagonals `‖x+y‖, ‖x+i•y‖, ‖x−y‖, ‖x−i•y‖`.  This is the discrete
Fourier / character-sum packaging of polarization — the shape that generalizes to the
recovery of a sesquilinear form from its associated quadratic form. -/
theorem inner_eq_sum_fourth_roots (x y : G) :
    ⟪x, y⟫_ℂ =
      (∑ k ∈ Finset.range 4,
        (-Complex.I) ^ k * ((‖x + Complex.I ^ k • y‖ : ℂ) ^ 2)) / 4 := by
  have hI2 : (Complex.I) ^ 2 = -1 := Complex.I_sq
  have hI3 : (Complex.I) ^ 3 = -Complex.I := by rw [pow_succ, hI2]; ring
  have hnI2 : (-Complex.I) ^ 2 = -1 := by
    rw [show (-Complex.I) ^ 2 = Complex.I ^ 2 by ring, hI2]
  have hnI3 : (-Complex.I) ^ 3 = Complex.I := by
    rw [show (-Complex.I) ^ 3 = -(Complex.I ^ 3) by ring, hI3]; ring
  have hI2s : Complex.I ^ 2 • y = -y := by rw [hI2, neg_one_smul]
  have hI3s : Complex.I ^ 3 • y = -(Complex.I • y) := by rw [hI3, neg_smul]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one, one_smul, one_mul, zero_add]
  rw [hI2s, hI3s, ← sub_eq_add_neg x y, ← sub_eq_add_neg x (Complex.I • y),
    hnI2, hnI3, inner_eq_polarization_complex]
  ring

/-- **The inner product is determined by the norm.**  If two pairs of vectors realize the
same four diagonal lengths `‖x+y‖, ‖x−y‖, ‖x + i•y‖, ‖x − i•y‖`, their inner products
coincide.  This is the precise sense in which polarization *recovers* the inner product
from the norm alone. -/
theorem inner_eq_of_diag_norms_eq {x y x' y' : G}
    (h₁ : ‖x + y‖ = ‖x' + y'‖) (h₂ : ‖x - y‖ = ‖x' - y'‖)
    (h₃ : ‖x + Complex.I • y‖ = ‖x' + Complex.I • y'‖)
    (h₄ : ‖x - Complex.I • y‖ = ‖x' - Complex.I • y'‖) :
    ⟪x, y⟫_ℂ = ⟪x', y'⟫_ℂ := by
  rw [inner_eq_polarization_split x y, inner_eq_polarization_split x' y',
    h₁, h₂, h₃, h₄]

/-- **Orthogonality from norms** (complex form).  Two vectors are orthogonal exactly when
both the ordinary diagonals *and* the rotated diagonals are equal:
`⟪x, y⟫ = 0 ↔ ‖x+y‖ = ‖x−y‖ ∧ ‖x + i•y‖ = ‖x − i•y‖`.
Over a real space perpendicularity is the single equal-diagonals condition
`‖x+y‖ = ‖x−y‖`; the complex case needs the rotated diagonals as well, to kill the
imaginary part. -/
theorem inner_eq_zero_iff_diags (x y : G) :
    ⟪x, y⟫_ℂ = 0 ↔ ‖x + y‖ = ‖x - y‖ ∧ ‖x + Complex.I • y‖ = ‖x - Complex.I • y‖ := by
  have hsq : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a ^ 2 = b ^ 2 ↔ a = b) := by
    intro a b ha hb
    constructor
    · intro h; nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
    · intro h; rw [h]
  rw [Complex.ext_iff, Complex.zero_re, Complex.zero_im,
    re_inner_eq_diag_sq_div_four, im_inner_eq_rot_diag_sq_div_four,
    div_eq_zero_iff, div_eq_zero_iff]
  simp only [sub_eq_zero, OfNat.ofNat_ne_zero, or_false]
  rw [hsq _ _ (norm_nonneg _) (norm_nonneg _), hsq _ _ (norm_nonneg _) (norm_nonneg _)]
  exact and_congr_right' ⟨Eq.symm, Eq.symm⟩

end CauchySchwarzOQ07OQ02

