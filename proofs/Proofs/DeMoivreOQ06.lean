/-
Finite geometric sum of complex exponentials and the Lagrange trigonometric identities

Source: Open question from the de-moivre gallery family (de-moivre-oq-06)
Status: VERIFIED (0 axioms, 0 sorries)

De Moivre's theorem turns a geometric sum of unit-modulus complex numbers into a
closed form.  Summing the ratio `z = e^{iθ}` and taking real / imaginary parts
yields the two classical *Lagrange trigonometric identities* (the Dirichlet
kernel and its conjugate):

      ∑_{k=0}^{n} cos(kθ) = 1/2 + sin((n+1/2)θ) / (2 sin(θ/2))
      ∑_{k=0}^{n} sin(kθ) = (cos(θ/2) − cos((n+1/2)θ)) / (2 sin(θ/2))

valid whenever `sin(θ/2) ≠ 0` (i.e. `θ` is not an integer multiple of `2π`).

Mathlib records the *infinite* power series `Complex.cos_eq_tsum` and the raw
geometric-series identity `geom_sum_eq`, but it does **not** record these
closed forms for the *finite partial sums* of `cos(kθ)` and `sin(kθ)`.  This file
supplies them, together with the underlying complex closed form

      ∑_{k=0}^{n} e^{ikθ} = (e^{i(n+1)θ} − 1)/(e^{iθ} − 1)      (e^{iθ} ≠ 1).

## Main results

* `geom_exp_partial_sum` — the finite geometric sum of complex exponentials.
* `two_sin_half_mul_cos`, `two_sin_half_mul_sin` — product-to-sum telescoping steps.
* `lagrange_cos_key`, `lagrange_sin_key` — the telescoped (denominator-cleared) identities.
* `lagrange_cos_sum` — **Lagrange's cosine identity** (real part of the Dirichlet kernel).
* `lagrange_sin_sum` — **Lagrange's sine identity** (the conjugate Dirichlet kernel).
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

open Finset

namespace DeMoivreOQ06

/-- **Finite geometric sum of complex exponentials.**
For `e^{iθ} ≠ 1`,
`∑_{k=0}^{n} e^{ikθ} = (e^{i(n+1)θ} − 1)/(e^{iθ} − 1)`. -/
theorem geom_exp_partial_sum (θ : ℝ) (h : Complex.exp (θ * Complex.I) ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Complex.exp ((k : ℂ) * (θ * Complex.I))
      = (Complex.exp (((n : ℂ) + 1) * (θ * Complex.I)) - 1) /
          (Complex.exp (θ * Complex.I) - 1) := by
  have hx : ∀ k : ℕ, Complex.exp ((k : ℂ) * (θ * Complex.I))
      = Complex.exp (θ * Complex.I) ^ k := fun k => Complex.exp_nat_mul (θ * Complex.I) k
  simp_rw [hx]
  rw [geom_sum_eq h (n + 1)]
  have hnum : Complex.exp (θ * Complex.I) ^ (n + 1)
      = Complex.exp (((n : ℂ) + 1) * (θ * Complex.I)) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [hnum]

/-- Product-to-sum telescoping step for cosines:
`2 sin(θ/2) cos(mθ) = sin((m+1/2)θ) − sin((m−1/2)θ)`. -/
theorem two_sin_half_mul_cos (θ m : ℝ) :
    2 * Real.sin (θ / 2) * Real.cos (m * θ)
      = Real.sin ((m + 1 / 2) * θ) - Real.sin ((m - 1 / 2) * θ) := by
  have h1 : (m + 1 / 2) * θ = m * θ + θ / 2 := by ring
  have h2 : (m - 1 / 2) * θ = m * θ - θ / 2 := by ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

/-- Product-to-sum telescoping step for sines:
`2 sin(θ/2) sin(mθ) = cos((m−1/2)θ) − cos((m+1/2)θ)`. -/
theorem two_sin_half_mul_sin (θ m : ℝ) :
    2 * Real.sin (θ / 2) * Real.sin (m * θ)
      = Real.cos ((m - 1 / 2) * θ) - Real.cos ((m + 1 / 2) * θ) := by
  have h1 : (m + 1 / 2) * θ = m * θ + θ / 2 := by ring
  have h2 : (m - 1 / 2) * θ = m * θ - θ / 2 := by ring
  rw [h1, h2, Real.cos_add, Real.cos_sub]
  ring

/-- Telescoped (denominator-cleared) Lagrange cosine identity:
`2 sin(θ/2) · ∑_{k=0}^{n} cos(kθ) = sin((n+1/2)θ) + sin(θ/2)`. -/
theorem lagrange_cos_key (θ : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * (∑ k ∈ Finset.range (n + 1), Real.cos (k * θ))
      = Real.sin (((n : ℝ) + 1 / 2) * θ) + Real.sin (θ / 2) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_one, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one,
          show ((0 : ℝ) + 1 / 2) * θ = θ / 2 by ring]
      ring
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, two_sin_half_mul_cos]
      have e1 : ((↑(n + 1) : ℝ) + 1 / 2) * θ = ((n : ℝ) + 1 + 1 / 2) * θ := by push_cast; ring
      have e2 : ((↑(n + 1) : ℝ) - 1 / 2) * θ = ((n : ℝ) + 1 / 2) * θ := by push_cast; ring
      rw [e1, e2]
      ring

/-- Telescoped (denominator-cleared) Lagrange sine identity:
`2 sin(θ/2) · ∑_{k=0}^{n} sin(kθ) = cos(θ/2) − cos((n+1/2)θ)`. -/
theorem lagrange_sin_key (θ : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * (∑ k ∈ Finset.range (n + 1), Real.sin (k * θ))
      = Real.cos (θ / 2) - Real.cos (((n : ℝ) + 1 / 2) * θ) := by
  induction n with
  | zero =>
      rw [Finset.sum_range_one, Nat.cast_zero, zero_mul, Real.sin_zero, mul_zero,
          show ((0 : ℝ) + 1 / 2) * θ = θ / 2 by ring]
      ring
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih, two_sin_half_mul_sin]
      have e1 : ((↑(n + 1) : ℝ) + 1 / 2) * θ = ((n : ℝ) + 1 + 1 / 2) * θ := by push_cast; ring
      have e2 : ((↑(n + 1) : ℝ) - 1 / 2) * θ = ((n : ℝ) + 1 / 2) * θ := by push_cast; ring
      rw [e1, e2]
      ring

/-- **Lagrange's cosine identity (Dirichlet kernel).**
For `sin(θ/2) ≠ 0`,
`∑_{k=0}^{n} cos(kθ) = 1/2 + sin((n+1/2)θ) / (2 sin(θ/2))`. -/
theorem lagrange_cos_sum (θ : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Real.cos (k * θ)
      = 1 / 2 + Real.sin (((n : ℝ) + 1 / 2) * θ) / (2 * Real.sin (θ / 2)) := by
  have hk := lagrange_cos_key θ n
  have hden : (2 : ℝ) * Real.sin (θ / 2) ≠ 0 := mul_ne_zero two_ne_zero hθ
  have hS : ∑ k ∈ Finset.range (n + 1), Real.cos (k * θ)
      = (Real.sin (((n : ℝ) + 1 / 2) * θ) + Real.sin (θ / 2)) / (2 * Real.sin (θ / 2)) := by
    rw [eq_div_iff hden]
    linear_combination hk
  have hhalf : Real.sin (θ / 2) / (2 * Real.sin (θ / 2)) = 1 / 2 := by
    rw [div_eq_iff hden]; ring
  rw [hS, add_div, hhalf]
  ring

/-- **Lagrange's sine identity (conjugate Dirichlet kernel).**
For `sin(θ/2) ≠ 0`,
`∑_{k=0}^{n} sin(kθ) = (cos(θ/2) − cos((n+1/2)θ)) / (2 sin(θ/2))`. -/
theorem lagrange_sin_sum (θ : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Real.sin (k * θ)
      = (Real.cos (θ / 2) - Real.cos (((n : ℝ) + 1 / 2) * θ)) / (2 * Real.sin (θ / 2)) := by
  have hk := lagrange_sin_key θ n
  have hden : (2 : ℝ) * Real.sin (θ / 2) ≠ 0 := mul_ne_zero two_ne_zero hθ
  rw [eq_div_iff hden]
  linear_combination hk

/-- **Dirichlet kernel bound (cosine form).**
The classical Fourier-analysis estimate: the (one-sided, normalised) Dirichlet
kernel `D_n(θ) = ∑_{k=0}^{n} cos(kθ) − 1/2 = sin((n+1/2)θ)/(2 sin(θ/2))` is
bounded by `1/(2|sin(θ/2)|)` uniformly in `n`, since `|sin((n+1/2)θ)| ≤ 1`.
This is the estimate underlying Dirichlet's test for the pointwise convergence
of Fourier series. -/
theorem dirichlet_kernel_bound (θ : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    |(∑ k ∈ Finset.range (n + 1), Real.cos ((k : ℝ) * θ)) - 1 / 2|
      ≤ 1 / (2 * |Real.sin (θ / 2)|) := by
  rw [lagrange_cos_sum θ hθ n]
  have hrw : (1 / 2 + Real.sin (((n : ℝ) + 1 / 2) * θ) / (2 * Real.sin (θ / 2))) - 1 / 2
      = Real.sin (((n : ℝ) + 1 / 2) * θ) / (2 * Real.sin (θ / 2)) := by ring
  rw [hrw, abs_div, abs_mul, abs_two]
  have hden : (0 : ℝ) < 2 * |Real.sin (θ / 2)| := mul_pos two_pos (abs_pos.mpr hθ)
  rw [div_le_div_iff hden hden]
  have hnum : |Real.sin (((n : ℝ) + 1 / 2) * θ)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  nlinarith [mul_le_mul_of_nonneg_right hnum (le_of_lt hden)]

/-- **Conjugate Dirichlet kernel bound (sine form).**
The partial sums of `sin(kθ)` are bounded by `1/|sin(θ/2)|` uniformly in `n`:
from the closed form `∑_{k=0}^{n} sin(kθ) = (cos(θ/2) − cos((n+1/2)θ))/(2 sin(θ/2))`
the numerator is a difference of two cosines, hence at most `2` in absolute value. -/
theorem dirichlet_conjugate_bound (θ : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    |∑ k ∈ Finset.range (n + 1), Real.sin ((k : ℝ) * θ)|
      ≤ 1 / |Real.sin (θ / 2)| := by
  have hA : (0 : ℝ) < |Real.sin (θ / 2)| := abs_pos.mpr hθ
  rw [lagrange_sin_sum θ hθ n, abs_div, abs_mul, abs_two]
  rw [div_le_div_iff (mul_pos two_pos hA) hA]
  have hnum : |Real.cos (θ / 2) - Real.cos (((n : ℝ) + 1 / 2) * θ)| ≤ 2 :=
    abs_le.mpr ⟨by
      have := Real.cos_le_one (θ / 2)
      have := Real.neg_one_le_cos (((n : ℝ) + 1 / 2) * θ)
      linarith, by
      have := Real.neg_one_le_cos (θ / 2)
      have := Real.cos_le_one (((n : ℝ) + 1 / 2) * θ)
      linarith⟩
  nlinarith [mul_le_mul_of_nonneg_right hnum (le_of_lt hA)]

end DeMoivreOQ06
