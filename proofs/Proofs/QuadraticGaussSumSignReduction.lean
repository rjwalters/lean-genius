/-
  Reducing Gauss's hard sign theorem to a single positivity.

  Background.  For an odd prime `p` and a primitive additive character
  `ψ : ZMod p → ℂ`, write `g = gaussSum (chiC p) ψ` for the quadratic Gauss sum.
  The parent file proves the SQUARE identity
      g² = (-1)^((p-1)/2) · p,
  and `QuadraticGaussSumSquareOQ01` extracts from it the elementary
  real/imaginary DICHOTOMY together with the magnitude `‖g‖² = p`:
      p ≡ 1 (mod 4)  ⟹  g.im = 0   (g real),
      p ≡ 3 (mod 4)  ⟹  g.re = 0   (g imaginary).

  Gauss's *hard* theorem fixes the leading sign:
      g = √p     if p ≡ 1 (mod 4),
      g = i·√p   if p ≡ 3 (mod 4).
  This is genuinely deep (Schur's eigenvalue computation on the finite Fourier
  transform, or Dirichlet's analytic evaluation) and is NOT proved here.

  What this file contributes — entirely by elementary complex arithmetic on top
  of the dichotomy + magnitude — is twofold:

    1. The **four-point pinning**: strengthen "g is real / imaginary" to the
       exact statement `g = ±√p` (resp. `g = ±i√p`).  Dichotomy + magnitude
       force `g.re² = p` (resp. `g.im² = p`), and `|·| = √p` splits into the two
       signs.

    2. The **reduction to a single positivity**: Gauss's sign theorem is
       EQUIVALENT to one real inequality,
           g = √p    ↔    0 < g.re      (p ≡ 1 mod 4),
           g = i·√p  ↔    0 < g.im      (p ≡ 3 mod 4).
       This isolates the precise open crux: every classical proof (Schur,
       Dirichlet, Kronecker) ultimately establishes exactly this positivity,
       and nothing in this file assumes it.

  All results below are sorry-free and axiom-free; only the positivity itself
  remains open.
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare
import Proofs.QuadraticGaussSumSquareOQ01

open scoped BigOperators
open QuadraticGaussSumSquare QuadraticGaussSumSquareOQ01

namespace QuadraticGaussSumSignReduction

variable {p : ℕ} [Fact p.Prime]

/-- Helper: the Gauss sum's magnitude is positive (`0 < √p`). -/
theorem sqrt_p_pos : (0 : ℝ) < Real.sqrt p :=
  Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)

/-! ### Four-point pinning -/

/-- **Pinning, case `p ≡ 1 (mod 4)`.** The Gauss sum is exactly `±√p`. -/
theorem gaussSum_eq_pm_sqrt (hp4 : p % 4 = 1)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ = (Real.sqrt p : ℂ) ∨
    gaussSum (chiC p) ψ = -(Real.sqrt p : ℂ) := by
  set g := gaussSum (chiC p) ψ with hg
  have him : g.im = 0 := gaussSum_im_eq_zero_of_one_mod_four hp4 hψ
  have hns : Complex.normSq g = p := gaussSum_normSq_eq (by omega) hψ
  have hre2 : g.re ^ 2 = (p : ℝ) := by
    have h := Complex.normSq_apply g
    rw [him] at h
    nlinarith [hns, h]
  have habs : |g.re| = Real.sqrt p := by
    rw [← Real.sqrt_sq_eq_abs, hre2]
  have hgre : g = (g.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rcases (abs_eq (Real.sqrt_nonneg (p : ℝ))).mp habs with h | h
  · left; rw [hgre, h]
  · right; rw [hgre, h]; push_cast; ring

/-- **Pinning, case `p ≡ 3 (mod 4)`.** The Gauss sum is exactly `±i·√p`. -/
theorem gaussSum_eq_pm_I_sqrt (hp4 : p % 4 = 3)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ = (Real.sqrt p : ℂ) * Complex.I ∨
    gaussSum (chiC p) ψ = -((Real.sqrt p : ℂ) * Complex.I) := by
  set g := gaussSum (chiC p) ψ with hg
  have hre : g.re = 0 := gaussSum_re_eq_zero_of_three_mod_four hp4 hψ
  have hns : Complex.normSq g = p := gaussSum_normSq_eq (by omega) hψ
  have him2 : g.im ^ 2 = (p : ℝ) := by
    have h := Complex.normSq_apply g
    rw [hre] at h
    nlinarith [hns, h]
  have habs : |g.im| = Real.sqrt p := by
    rw [← Real.sqrt_sq_eq_abs, him2]
  have hgim : g = (g.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hre]
  rcases (abs_eq (Real.sqrt_nonneg (p : ℝ))).mp habs with h | h
  · left; rw [hgim, h]
  · right; rw [hgim, h]; push_cast; ring

/-! ### Reduction of Gauss's sign theorem to a single positivity -/

/-- **Reduction, case `p ≡ 1 (mod 4)`.** Gauss's sign theorem `g = √p` holds
iff the (already real) Gauss sum has positive real part.  This isolates the
entire open content into the single inequality `0 < g.re`. -/
theorem gaussSum_eq_sqrt_iff_re_pos (hp4 : p % 4 = 1)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ = (Real.sqrt p : ℂ) ↔ 0 < (gaussSum (chiC p) ψ).re := by
  constructor
  · intro h; rw [h]; simpa using (sqrt_p_pos (p := p))
  · intro h
    rcases gaussSum_eq_pm_sqrt hp4 hψ with hpos | hneg
    · exact hpos
    · exfalso
      rw [hneg] at h
      simp only [Complex.neg_re, Complex.ofReal_re] at h
      linarith [sqrt_p_pos (p := p)]

/-- **Reduction, case `p ≡ 3 (mod 4)`.** Gauss's sign theorem `g = i·√p` holds
iff the (already imaginary) Gauss sum has positive imaginary part. -/
theorem gaussSum_eq_I_sqrt_iff_im_pos (hp4 : p % 4 = 3)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    gaussSum (chiC p) ψ = (Real.sqrt p : ℂ) * Complex.I ↔
      0 < (gaussSum (chiC p) ψ).im := by
  constructor
  · intro h
    rw [h]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    exact sqrt_p_pos (p := p)
  · intro h
    rcases gaussSum_eq_pm_I_sqrt hp4 hψ with hpos | hneg
    · exact hpos
    · exfalso
      rw [hneg] at h
      simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at h
      linarith [sqrt_p_pos (p := p)]

end QuadraticGaussSumSignReduction
