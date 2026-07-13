/-
The Fejér kernel as the Cesàro average of the Dirichlet kernels

Source: Open question from the de-moivre gallery family (de-moivre-oq-06-oq-02-oq-01)
Status: VERIFIED (0 axioms, 0 sorries)

The parent file `DeMoivreOQ06OQ02` supplies *uniform* bounds for the Dirichlet
kernel on an arc `θ ∈ [δ, 2π − δ]` bounded away from the singularities `θ ∈ 2πℤ`.
The grandparent `DeMoivreOQ06` gives Lagrange's closed forms

      ∑_{k=0}^{n} cos(kθ) = 1/2 + sin((n+1/2)θ) / (2 sin(θ/2)).

The (symmetric) **Dirichlet kernel** is
      Dₙ(θ) = ∑_{k=−n}^{n} e^{ikθ} = 1 + 2 ∑_{k=1}^{n} cos(kθ)
            = 2·(∑_{k=0}^{n} cos(kθ)) − 1 = sin((n+1/2)θ) / sin(θ/2).

Its Cesàro average is the **Fejér kernel**
      F_N(θ) = (1/(N+1)) ∑_{n=0}^{N} Dₙ(θ).

This file establishes the three defining facts about `F_N`, all reusing the
parent's product-to-sum telescoping:

* `sum_sin_half_odd` — the telescoping identity
  `2 sin(θ/2) · ∑_{m=0}^{N} sin((m+1/2)θ) = 1 − cos((N+1)θ)`.
* `fejerKernel_closed_form` — the celebrated closed form
  `F_N(θ) = sin²((N+1)θ/2) / ((N+1) sin²(θ/2))`.  Being a perfect square over a
  positive quantity, the Fejér kernel is **nonnegative** — the property that
  makes `{F_N}` an *approximate identity* (unlike the sign-changing Dirichlet
  kernel), the engine behind Fejér's theorem on Cesàro summability of Fourier
  series.
* `fejerKernel_nonneg` — `0 ≤ F_N(θ)`.
* `fejerKernel_uniform_bound` — on the arc `θ ∈ [δ, 2π − δ]`,
  `F_N(θ) ≤ 1 / ((N+1) sin²(δ/2))`, so the mass of `F_N` concentrates at the
  origin as `N → ∞`.
-/

import Proofs.DeMoivreOQ06OQ02
import Mathlib.Tactic

open Finset

namespace DeMoivreOQ06OQ02OQ01

/-- Product-to-sum telescoping step for the half-integer sines:
`2 sin(θ/2) sin((m+1/2)θ) = cos(mθ) − cos((m+1)θ)`.

The identity `cos(X−Y) − cos(X+Y) = 2 sin X sin Y` with `X = (m+1/2)θ`,
`Y = θ/2` (so `X−Y = mθ` and `X+Y = (m+1)θ`). -/
theorem two_sin_half_mul_sin_odd (θ m : ℝ) :
    2 * Real.sin (θ / 2) * Real.sin ((m + 1 / 2) * θ)
      = Real.cos (m * θ) - Real.cos ((m + 1) * θ) := by
  have h1 : m * θ = (m + 1 / 2) * θ - θ / 2 := by ring
  have h2 : (m + 1) * θ = (m + 1 / 2) * θ + θ / 2 := by ring
  rw [h1, h2, Real.cos_sub, Real.cos_add]
  ring

/-- **Telescoped half-integer sine sum.**
`2 sin(θ/2) · ∑_{m=0}^{N} sin((m+1/2)θ) = 1 − cos((N+1)θ)`.

Distributing `2 sin(θ/2)` across the sum and applying `two_sin_half_mul_sin_odd`
term-by-term makes the sum telescope: consecutive `cos(mθ)` cancel, leaving the
endpoints `cos(0) − cos((N+1)θ) = 1 − cos((N+1)θ)`. -/
theorem sum_sin_half_odd (θ : ℝ) (N : ℕ) :
    2 * Real.sin (θ / 2) * (∑ m ∈ Finset.range (N + 1), Real.sin (((m : ℝ) + 1 / 2) * θ))
      = 1 - Real.cos (((N : ℝ) + 1) * θ) := by
  induction N with
  | zero =>
      rw [Finset.sum_range_one]
      have h := two_sin_half_mul_sin_odd θ 0
      simp only [zero_mul, Real.cos_zero] at h
      push_cast
      linear_combination h
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have h := two_sin_half_mul_sin_odd θ ((N : ℝ) + 1)
      push_cast
      push_cast at h
      linear_combination h

/-- The (symmetric) **Dirichlet kernel**
`Dₙ(θ) = 1 + 2 ∑_{k=1}^{n} cos(kθ) = 2·(∑_{k=0}^{n} cos(kθ)) − 1`. -/
noncomputable def dirichletKernel (n : ℕ) (θ : ℝ) : ℝ :=
  2 * (∑ k ∈ Finset.range (n + 1), Real.cos ((k : ℝ) * θ)) - 1

/-- Closed form of the Dirichlet kernel: `Dₙ(θ) = sin((n+1/2)θ) / sin(θ/2)`
for `sin(θ/2) ≠ 0`. Immediate from Lagrange's cosine identity in `DeMoivreOQ06`. -/
theorem dirichletKernel_closed_form (θ : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    dirichletKernel n θ = Real.sin (((n : ℝ) + 1 / 2) * θ) / Real.sin (θ / 2) := by
  unfold dirichletKernel
  rw [DeMoivreOQ06.lagrange_cos_sum θ hθ n]
  field_simp
  ring

/-- The **Fejér kernel** `F_N(θ) = (1/(N+1)) ∑_{n=0}^{N} Dₙ(θ)`, the Cesàro
(arithmetic) mean of the first `N+1` Dirichlet kernels. -/
noncomputable def fejerKernel (N : ℕ) (θ : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (N + 1), dirichletKernel n θ) / ((N : ℝ) + 1)

/-- **Sum of Dirichlet kernels in closed form.**
`∑_{n=0}^{N} Dₙ(θ) = sin²((N+1)θ/2) / sin²(θ/2)` for `sin(θ/2) ≠ 0`.

Rewrite each `Dₙ` by its closed form, factor out `1/sin(θ/2)`, apply the
telescoping `sum_sin_half_odd`, and convert `1 − cos((N+1)θ) = 2 sin²((N+1)θ/2)`
via the double-angle formula. -/
theorem sum_dirichletKernel (θ : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), dirichletKernel n θ
      = (Real.sin (((N : ℝ) + 1) * θ / 2)) ^ 2 / (Real.sin (θ / 2)) ^ 2 := by
  -- Sum of the closed forms, with `1/sin(θ/2)` factored out.
  have hsum : ∑ n ∈ Finset.range (N + 1), dirichletKernel n θ
      = (∑ n ∈ Finset.range (N + 1), Real.sin (((n : ℝ) + 1 / 2) * θ)) / Real.sin (θ / 2) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun n _ => dirichletKernel_closed_form θ hθ n
  -- Half-angle identity `1 − cos((N+1)θ) = 2 sin²((N+1)θ/2)`.
  have hcos : 1 - Real.cos (((N : ℝ) + 1) * θ) = 2 * (Real.sin (((N : ℝ) + 1) * θ / 2)) ^ 2 := by
    set y := ((N : ℝ) + 1) * θ / 2 with hy
    have h2y : ((N : ℝ) + 1) * θ = 2 * y := by rw [hy]; ring
    rw [h2y, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq y]
  -- `sin(θ/2) · ∑ sin((n+1/2)θ) = sin²((N+1)θ/2)`.
  have hS : Real.sin (θ / 2) * (∑ n ∈ Finset.range (N + 1), Real.sin (((n : ℝ) + 1 / 2) * θ))
      = (Real.sin (((N : ℝ) + 1) * θ / 2)) ^ 2 := by
    have hodd := sum_sin_half_odd θ N
    rw [hcos] at hodd
    linarith
  rw [hsum]
  rw [div_eq_div_iff hθ (pow_ne_zero 2 hθ)]
  linear_combination Real.sin (θ / 2) * hS

/-- **Fejér kernel closed form.**
`F_N(θ) = sin²((N+1)θ/2) / ((N+1) sin²(θ/2))` for `sin(θ/2) ≠ 0`. -/
theorem fejerKernel_closed_form (θ : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) (N : ℕ) :
    fejerKernel N θ
      = (Real.sin (((N : ℝ) + 1) * θ / 2)) ^ 2
          / (((N : ℝ) + 1) * (Real.sin (θ / 2)) ^ 2) := by
  unfold fejerKernel
  rw [sum_dirichletKernel θ hθ N, div_div, mul_comm ((Real.sin (θ / 2)) ^ 2)]

/-- **The Fejér kernel is nonnegative.**
`0 ≤ F_N(θ)` for `sin(θ/2) ≠ 0`.  A perfect square over the positive quantity
`(N+1) sin²(θ/2)`.  This is the property that fails for the Dirichlet kernel and
makes `{F_N}` a genuine approximate identity. -/
theorem fejerKernel_nonneg (θ : ℝ) (hθ : Real.sin (θ / 2) ≠ 0) (N : ℕ) :
    0 ≤ fejerKernel N θ := by
  rw [fejerKernel_closed_form θ hθ N]
  apply div_nonneg
  · positivity
  · have : 0 < (Real.sin (θ / 2)) ^ 2 := by positivity
    positivity

/-- **Uniform bound for the Fejér kernel on the arc.**
On `θ ∈ [δ, 2π − δ]` (with `0 < δ ≤ π`),
`F_N(θ) ≤ 1 / ((N+1) sin²(δ/2))`, uniformly in `θ`, and `→ 0` as `N → ∞`.

The numerator `sin²((N+1)θ/2) ≤ 1`, while the denominator is bounded below using
the parent's `sin(θ/2) ≥ sin(δ/2) > 0`.  Concentration of the Fejér mass at the
origin is the analytic heart of Fejér's theorem. -/
theorem fejerKernel_uniform_bound (δ θ : ℝ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi)
    (hθ1 : δ ≤ θ) (hθ2 : θ ≤ 2 * Real.pi - δ) (N : ℕ) :
    fejerKernel N θ ≤ 1 / (((N : ℝ) + 1) * (Real.sin (δ / 2)) ^ 2) := by
  have hpi := Real.pi_pos
  have hδpos : 0 < Real.sin (δ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hθge : Real.sin (δ / 2) ≤ Real.sin (θ / 2) :=
    DeMoivreOQ06OQ02.sin_half_ge_of_mem_arc δ θ hδ0 hδπ hθ1 hθ2
  have hθpos : 0 < Real.sin (θ / 2) := lt_of_lt_of_le hδpos hθge
  have hθne : Real.sin (θ / 2) ≠ 0 := ne_of_gt hθpos
  rw [fejerKernel_closed_form θ hθne N]
  -- numerator ≤ 1
  have hnum : (Real.sin (((N : ℝ) + 1) * θ / 2)) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (((N : ℝ) + 1) * θ / 2),
      sq_nonneg (Real.cos (((N : ℝ) + 1) * θ / 2))]
  -- denominators are positive and comparable
  have hNpos : 0 < (N : ℝ) + 1 := by positivity
  have hden_arc : 0 < ((N : ℝ) + 1) * (Real.sin (δ / 2)) ^ 2 := by positivity
  have hden_θ : 0 < ((N : ℝ) + 1) * (Real.sin (θ / 2)) ^ 2 := by positivity
  have hden_le : ((N : ℝ) + 1) * (Real.sin (δ / 2)) ^ 2
      ≤ ((N : ℝ) + 1) * (Real.sin (θ / 2)) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hNpos)
    nlinarith [hθge, hδpos.le, hθpos.le]
  calc (Real.sin (((N : ℝ) + 1) * θ / 2)) ^ 2 / (((N : ℝ) + 1) * (Real.sin (θ / 2)) ^ 2)
      ≤ 1 / (((N : ℝ) + 1) * (Real.sin (θ / 2)) ^ 2) := by
        rw [div_le_div_iff_of_pos_right hden_θ]; exact hnum
    _ ≤ 1 / (((N : ℝ) + 1) * (Real.sin (δ / 2)) ^ 2) :=
        one_div_le_one_div_of_le hden_arc hden_le

end DeMoivreOQ06OQ02OQ01
