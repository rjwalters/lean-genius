/-
  Real / imaginary dichotomy of the quadratic Gauss sum.

  Parent (`Proofs/QuadraticGaussSumSquare.lean`) establishes, for an odd prime `p`
  and a primitive additive character `ψ : ZMod p → ℂ`, the SQUARE of the quadratic
  Gauss sum `g = gaussSum (chiC p) ψ`:

      g² = (-1)^((p-1)/2) · p.

  This pins `g` down only up to sign.  Gauss's *hard* theorem fixes the sign:

      g = √p          if p ≡ 1 (mod 4),
      g = i·√p        if p ≡ 3 (mod 4).

  The full sign is genuinely deep (Schur's eigenvalue argument / Dirichlet's
  analytic evaluation) and is NOT formalized here.  This file proves the
  *elementary half* — the real/imaginary DICHOTOMY — which already follows from
  the parent's square identity by pure complex arithmetic:

    * p ≡ 1 (mod 4)  ⟹  g² = +p > 0  ⟹  g is real      (`g.im = 0`),
    * p ≡ 3 (mod 4)  ⟹  g² = −p < 0  ⟹  g is imaginary  (`g.re = 0`),

  together with the magnitude `‖g‖² = p` (so `g = ±√p` resp. `±i√p`).  The
  remaining `±` choice is exactly the open hard theorem.
-/
import Mathlib
import Proofs.QuadraticGaussSumSquare

open scoped BigOperators
open QuadraticGaussSumSquare

namespace QuadraticGaussSumSquareOQ01

variable {p : ℕ} [Fact p.Prime]

/-- A complex number whose square is a **positive real** is itself real. -/
theorem im_eq_zero_of_sq_eq_pos_real {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ^ 2 = (r : ℂ)) : z.im = 0 := by
  -- imaginary part of `z² = r`:  z.re·z.im + z.im·z.re = 0
  have h1 : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im hz
    rwa [pow_two, Complex.mul_im, Complex.ofReal_im] at this
  -- real part of `z² = r`:  z.re·z.re − z.im·z.im = r
  have h2 : z.re * z.re - z.im * z.im = r := by
    have := congrArg Complex.re hz
    rwa [pow_two, Complex.mul_re, Complex.ofReal_re] at this
  -- hence z.re·z.im = 0
  have hprod : z.re * z.im = 0 := by linarith [h1, mul_comm z.im z.re]
  rcases mul_eq_zero.mp hprod with hre0 | him0
  · -- z.re = 0 forces −z.im² = r > 0, impossible
    rw [hre0] at h2
    nlinarith [mul_self_nonneg z.im]
  · exact him0

/-- A complex number whose square is a **negative real** is purely imaginary. -/
theorem re_eq_zero_of_sq_eq_neg_real {z : ℂ} {r : ℝ} (hr : r < 0)
    (hz : z ^ 2 = (r : ℂ)) : z.re = 0 := by
  have h1 : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im hz
    rwa [pow_two, Complex.mul_im, Complex.ofReal_im] at this
  have h2 : z.re * z.re - z.im * z.im = r := by
    have := congrArg Complex.re hz
    rwa [pow_two, Complex.mul_re, Complex.ofReal_re] at this
  have hprod : z.re * z.im = 0 := by linarith [h1, mul_comm z.im z.re]
  rcases mul_eq_zero.mp hprod with hre0 | him0
  · exact hre0
  · -- z.im = 0 forces z.re² = r < 0, impossible
    rw [him0] at h2
    nlinarith [mul_self_nonneg z.re]

/-- **Dichotomy, case `p ≡ 1 (mod 4)`.** The quadratic Gauss sum is real. -/
theorem gaussSum_im_eq_zero_of_one_mod_four (hp4 : p % 4 = 1)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    (gaussSum (chiC p) ψ).im = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hsq := gaussSum_quadratic_sq (p := p) hp2 hψ
  have heven : Even ((p - 1) / 2) := by rw [Nat.even_iff]; omega
  rw [heven.neg_one_pow, one_mul] at hsq
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  refine im_eq_zero_of_sq_eq_pos_real hppos ?_
  rw [hsq]; push_cast; ring

/-- **Dichotomy, case `p ≡ 3 (mod 4)`.** The quadratic Gauss sum is purely imaginary. -/
theorem gaussSum_re_eq_zero_of_three_mod_four (hp4 : p % 4 = 3)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    (gaussSum (chiC p) ψ).re = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hsq := gaussSum_quadratic_sq (p := p) hp2 hψ
  have hodd : Odd ((p - 1) / 2) := by rw [Nat.odd_iff]; omega
  rw [hodd.neg_one_pow] at hsq
  have hpneg : (-(p : ℝ)) < 0 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    linarith
  refine re_eq_zero_of_sq_eq_neg_real hpneg ?_
  rw [hsq]; push_cast; ring

/-- **Magnitude.** `‖g‖² = p`, so the Gauss sum has absolute value `√p`.
Combined with the dichotomy this gives `g = ±√p` (p ≡ 1) resp. `g = ±i√p`
(p ≡ 3); only the leading sign remains open. -/
theorem gaussSum_normSq_eq (hp2 : p ≠ 2) {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) : Complex.normSq (gaussSum (chiC p) ψ) = p := by
  have hsq := gaussSum_quadratic_sq (p := p) hp2 hψ
  -- `normSq` is multiplicative: normSq (g²) = (normSq g)²
  have h := congrArg Complex.normSq hsq
  rw [map_pow, map_mul, map_pow] at h
  -- normSq (-1) = 1 and normSq (p : ℂ) = p²
  have hneg : Complex.normSq (-1 : ℂ) = 1 := by simp
  have hpc : Complex.normSq (p : ℂ) = (p : ℝ) ^ 2 := by
    rw [Complex.normSq_natCast]; ring
  rw [hneg, one_pow, one_mul, hpc] at h
  -- h : (normSq g)² = p²; both sides nonneg ⟹ equal
  have hnn : (0 : ℝ) ≤ Complex.normSq (gaussSum (chiC p) ψ) := Complex.normSq_nonneg _
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := by positivity
  nlinarith [h, hnn, hpnn]

end QuadraticGaussSumSquareOQ01
