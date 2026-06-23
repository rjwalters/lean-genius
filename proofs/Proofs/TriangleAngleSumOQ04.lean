import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-
# Werner product-to-sum identities and the finite Dirichlet kernel

## What This Proves

The four **Werner product-to-sum identities** convert a product of two sinusoids into
a sum of two sinusoids:

  2·cos x·cos y = cos(x − y) + cos(x + y)
  2·sin x·sin y = cos(x − y) − cos(x + y)
  2·sin x·cos y = sin(x − y) + sin(x + y)
  2·cos x·sin y = sin(x + y) − sin(x − y)

These are the building blocks. The substantive content of this entry is their
**telescoping application** — the closed forms of the finite cosine and sine sums
(the *Dirichlet kernel* / *Lagrange trigonometric identity*):

  2·sin(x/2)·∑_{k=1}^{n} cos(kx) = sin((n + ½)x) − sin(x/2)
  2·sin(x/2)·∑_{k=1}^{n} sin(kx) = cos(x/2) − cos((n + ½)x)

and, when sin(x/2) ≠ 0, the kernel form

  ½ + ∑_{k=1}^{n} cos(kx) = sin((n + ½)x) / (2·sin(x/2)).

## What Mathlib has — and what this adds

Mathlib supplies the Werner identities `Real.two_mul_cos_mul_cos`,
`Real.two_mul_sin_mul_sin`, `Real.two_mul_sin_mul_cos` and the sum-to-product
identities `Real.cos_add_cos` etc. It does **not** record the finite telescoped
trigonometric sums (the Dirichlet kernel `D_n`): a search of Mathlib's trigonometric
files turns up only the infinite power-series `Real.cos_eq_tsum`, not the finite
`∑_{k=1}^{n} cos(kx)` closed form. Those finite telescoped identities, the heart of
classical Fourier analysis (partial sums of Fourier series are convolutions with
`D_n`), are the original content here. The crux is that each summand is a telescoping
difference produced by a single Werner identity:

  2·sin(x/2)·cos((k+1)x) = sin((k + 1 + ½)x) − sin((k + ½)x).

Summing collapses to the endpoints.

Verified: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace TriangleAngleSumOQ04

open Real Finset

/-! ## The four Werner product-to-sum identities

These convert a product of two sinusoids into a sum. They are proved directly from
the addition formulas (and agree with Mathlib's `Real.two_mul_*` lemmas); they serve
as the building blocks for the telescoping sums below. -/

/-- Werner: `2·cos x·cos y = cos(x − y) + cos(x + y)`. -/
theorem werner_cos_cos (x y : ℝ) :
    2 * cos x * cos y = cos (x - y) + cos (x + y) := by
  rw [cos_add, cos_sub]; ring

/-- Werner: `2·sin x·sin y = cos(x − y) − cos(x + y)`. -/
theorem werner_sin_sin (x y : ℝ) :
    2 * sin x * sin y = cos (x - y) - cos (x + y) := by
  rw [cos_add, cos_sub]; ring

/-- Werner: `2·sin x·cos y = sin(x − y) + sin(x + y)`. -/
theorem werner_sin_cos (x y : ℝ) :
    2 * sin x * cos y = sin (x - y) + sin (x + y) := by
  rw [sin_add, sin_sub]; ring

/-- Werner: `2·cos x·sin y = sin(x + y) − sin(x − y)` (the mixed identity not stated
in Mathlib in this orientation). -/
theorem werner_cos_sin (x y : ℝ) :
    2 * cos x * sin y = sin (x + y) - sin (x - y) := by
  rw [sin_add, sin_sub]; ring

/-! ## The single-step telescoping identities

Each summand of the Dirichlet sum is, after multiplying by `2·sin(x/2)`, a difference
of consecutive sines (resp. cosines) — a direct consequence of a Werner identity. -/

/-- Cosine step: `2·sin(x/2)·cos((k+1)x) = sin((k+1+½)x) − sin((k+½)x)`. The two
arguments `x/2 ± (k+1)x` collapse to `±(k+½)x` shifted by one, giving a telescoping
difference. -/
theorem step_cos (x : ℝ) (k : ℕ) :
    2 * sin (x / 2) * cos (((k : ℝ) + 1) * x)
      = sin ((((k : ℝ) + 1) + 1 / 2) * x) - sin (((k : ℝ) + 1 / 2) * x) := by
  have h := Real.two_mul_sin_mul_cos (x / 2) (((k : ℝ) + 1) * x)
  rw [h, show x / 2 - ((k : ℝ) + 1) * x = -(((k : ℝ) + 1 / 2) * x) by ring,
      show x / 2 + ((k : ℝ) + 1) * x = (((k : ℝ) + 1) + 1 / 2) * x by ring, sin_neg]
  ring

/-- Sine step: `2·sin(x/2)·sin((k+1)x) = cos((k+½)x) − cos((k+1+½)x)`. -/
theorem step_sin (x : ℝ) (k : ℕ) :
    2 * sin (x / 2) * sin (((k : ℝ) + 1) * x)
      = cos (((k : ℝ) + 1 / 2) * x) - cos ((((k : ℝ) + 1) + 1 / 2) * x) := by
  have h := Real.two_mul_sin_mul_sin (x / 2) (((k : ℝ) + 1) * x)
  rw [h, show x / 2 - ((k : ℝ) + 1) * x = -(((k : ℝ) + 1 / 2) * x) by ring,
      show x / 2 + ((k : ℝ) + 1) * x = (((k : ℝ) + 1) + 1 / 2) * x by ring, cos_neg]

/-! ## The finite telescoped sums (Dirichlet kernel) -/

/-- **Telescoped cosine sum.** For every real `x` and natural `n`,
`2·sin(x/2)·∑_{k=1}^{n} cos(kx) = sin((n + ½)x) − sin(x/2)`. Proved by induction:
the inductive step adds one `step_cos` term and the consecutive sines cancel. -/
theorem two_sin_half_mul_sum_cos (x : ℝ) (n : ℕ) :
    2 * sin (x / 2) * (∑ k ∈ range n, cos (((k : ℝ) + 1) * x))
      = sin (((n : ℝ) + 1 / 2) * x) - sin (x / 2) := by
  induction n with
  | zero =>
    simp only [range_zero, sum_empty, mul_zero, Nat.cast_zero]
    rw [show ((0 : ℝ) + 1 / 2) * x = x / 2 by ring]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, step_cos]
    push_cast
    ring

/-- **Telescoped sine sum.** For every real `x` and natural `n`,
`2·sin(x/2)·∑_{k=1}^{n} sin(kx) = cos(x/2) − cos((n + ½)x)`. -/
theorem two_sin_half_mul_sum_sin (x : ℝ) (n : ℕ) :
    2 * sin (x / 2) * (∑ k ∈ range n, sin (((k : ℝ) + 1) * x))
      = cos (x / 2) - cos (((n : ℝ) + 1 / 2) * x) := by
  induction n with
  | zero =>
    simp only [range_zero, sum_empty, mul_zero, Nat.cast_zero]
    rw [show ((0 : ℝ) + 1 / 2) * x = x / 2 by ring]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, step_sin]
    push_cast
    ring

/-- **Closed form for the cosine sum** when `sin(x/2) ≠ 0`:
`∑_{k=1}^{n} cos(kx) = (sin((n + ½)x) − sin(x/2)) / (2·sin(x/2))`. -/
theorem sum_cos_eq (x : ℝ) (n : ℕ) (hx : sin (x / 2) ≠ 0) :
    (∑ k ∈ range n, cos (((k : ℝ) + 1) * x))
      = (sin (((n : ℝ) + 1 / 2) * x) - sin (x / 2)) / (2 * sin (x / 2)) := by
  rw [eq_div_iff (mul_ne_zero two_ne_zero hx)]
  linear_combination two_sin_half_mul_sum_cos x n

/-- **Dirichlet kernel.** When `sin(x/2) ≠ 0`,
`½ + ∑_{k=1}^{n} cos(kx) = sin((n + ½)x) / (2·sin(x/2)) = D_n(x)`,
the `n`-th Dirichlet kernel — the convolution kernel of the partial sums of a Fourier
series. -/
theorem dirichlet_kernel (x : ℝ) (n : ℕ) (hx : sin (x / 2) ≠ 0) :
    1 / 2 + ∑ k ∈ range n, cos (((k : ℝ) + 1) * x)
      = sin (((n : ℝ) + 1 / 2) * x) / (2 * sin (x / 2)) := by
  rw [eq_div_iff (mul_ne_zero two_ne_zero hx)]
  linear_combination two_sin_half_mul_sum_cos x n

/-! ## Worked instances -/

/-- Instance `n = 2` of the cosine sum (symbolic in `x`):
`2·sin(x/2)·(cos x + cos 2x) = sin(5x/2) − sin(x/2)`.
Proved directly from two Werner steps, showing the telescoping cancellation of the
intermediate `sin(3x/2)`. -/
example (x : ℝ) :
    2 * sin (x / 2) * (cos x + cos (2 * x)) = sin (5 / 2 * x) - sin (x / 2) := by
  have e1 : 2 * sin (x / 2) * cos x = sin (3 / 2 * x) - sin (x / 2) := by
    have h := Real.two_mul_sin_mul_cos (x / 2) x
    rw [h, show x / 2 - x = -(x / 2) by ring, show x / 2 + x = 3 / 2 * x by ring, sin_neg]
    ring
  have e2 : 2 * sin (x / 2) * cos (2 * x) = sin (5 / 2 * x) - sin (3 / 2 * x) := by
    have h := Real.two_mul_sin_mul_cos (x / 2) (2 * x)
    rw [h, show x / 2 - 2 * x = -(3 / 2 * x) by ring, show x / 2 + 2 * x = 5 / 2 * x by ring,
        sin_neg]
    ring
  linear_combination e1 + e2

/-- Numeric sanity check: at `x = π`, `cos(kπ) = (−1)^k`, and the `n = 2` cosine sum
gives `cos π + cos 2π = -1 + 1 = 0`, matching the telescoped right-hand side
`sin(5π/2) − sin(π/2) = 1 − 1 = 0`. -/
example : Real.cos Real.pi + Real.cos (2 * Real.pi) = 0 := by
  rw [Real.cos_pi, show (2 : ℝ) * Real.pi = Real.pi + Real.pi by ring, Real.cos_add]
  rw [Real.cos_pi, Real.sin_pi]; ring

end TriangleAngleSumOQ04
