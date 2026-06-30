import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-
# Closed-Form 2×2 Matrix Exponential from Cayley–Hamilton

## What This Proves

For a `2×2` real matrix `A` with `tr A = τ` and `det A = δ`, the explicit
Cayley–Hamilton relation `A² = τ • A − δ • 1` collapses every power `Aᵏ` into the
two-dimensional span `{1, A}`. This file pushes that collapse through the matrix
exponential and proves the closed form

  `exp(t • A) = α(t) • 1 + β(t) • A`,

where the scalar coefficients `α, β : ℝ → ℝ` are *any* pair solving the Putzer ODE
system

  `α'(t) = −δ · β(t)`,  `β'(t) = α(t) + τ · β(t)`,  `α(0) = 1`,  `β(0) = 0`.

The headline theorem `exp_eq_of_coeffs` proves this for an arbitrary such pair, by
an integrating-factor / uniqueness argument: the matrix-valued function
`φ(t) = exp(−t • A) · (α(t) • 1 + β(t) • A)` has identically-zero derivative, hence
is the constant `φ(0) = 1`, which rearranges to the closed form.

Two corollaries instantiate the classical explicit coefficients from the
eigenvalues `λ₁, λ₂` (roots of `λ² − τλ + δ`):

* `exp_two_two_distinct` (`λ₁ ≠ λ₂`):
  `β(t) = (e^{λ₁t} − e^{λ₂t})/(λ₁ − λ₂)`, `α(t) = e^{λ₁t} − λ₁ β(t)`;
* `exp_two_two_repeated` (`λ₁ = λ₂ = λ`):
  `β(t) = t e^{λt}`, `α(t) = e^{λt} − λ t e^{λt}`.

## Why This Is Not Just a Re-export

Mathlib provides `Matrix.exp` and its derivative `hasDerivAt_exp_smul_const`, but no
result reduces the 2×2 exponential to the finite span `{1, A}` with explicit scalar
coefficients. The reduction here is genuinely new: it is the analytic completion of
the algebraic parent `CayleyHamiltonOQ04` (`A² = τ•A − δ•1`), turning the infinite
series `Σ tᵏAᵏ/k!` into a two-term closed form governed by the eigenvalue ODE. The
uniqueness step is proved from scratch via `is_const_of_deriv_eq_zero`.

## Mathematical Significance

The 2×2 matrix exponential is the engine of planar linear ODE systems, rotation and
shear flows, and the `SL₂`/`SU₂` Lie-group exponential maps. The closed form
`exp(tA) = α(t)I + β(t)A` (no infinite series) is a reusable building block and a
clean showcase of Cayley–Hamilton reducing an analytic matrix function to a scalar
problem (E. J. Putzer, *Amer. Math. Monthly* 73 (1966)).

## Extends
- CayleyHamiltonOQ04.lean (open question OQ-04 of the Cayley–Hamilton entry)
- CayleyHamilton.lean (Wiedijk #49)

## Status
- [x] Complete proof (no sorries). Inherits only the standard foundational axioms
      used by `Matrix.exp` (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace CayleyHamiltonOQ04OQ02

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

/-- **Explicit 2×2 Cayley–Hamilton** (`A * A = τ • A − δ • 1`), proved by direct
entrywise expansion. This is the `A * A` form of the parent `sq_eq`. -/
theorem mul_self_eq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A * A = A.trace • A - A.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      Matrix.sub_apply, Matrix.smul_apply] <;> ring

/-- **Headline closed form.** If the scalar coefficients `α, β` solve the Putzer ODE
system `α' = −(det A)·β`, `β' = α + (tr A)·β` with `α(0) = 1`, `β(0) = 0`, then the
matrix exponential is the two-term combination `exp(t • A) = α(t) • 1 + β(t) • A`.

The proof is an integrating-factor uniqueness argument: `exp(−t•A) · (α•1 + β•A)` has
zero derivative everywhere (using `A² = τ•A − δ•1` to cancel), hence equals its value
`1` at `t = 0`. -/
theorem exp_eq_of_coeffs (A : Matrix (Fin 2) (Fin 2) ℝ) (α β : ℝ → ℝ)
    (hα : ∀ t, HasDerivAt α (-(A.det) * β t) t)
    (hβ : ∀ t, HasDerivAt β (α t + A.trace * β t) t)
    (h0 : α 0 = 1) (h0' : β 0 = 0) (t : ℝ) :
    exp ℝ (t • A) = α t • 1 + β t • A := by
  -- The algebraic cancellation underlying `φ' = 0`.
  have key : ∀ s : ℝ, (-A) * (α s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β s • A)
      + ((-(A.det) * β s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
          + (α s + A.trace * β s) • A) = 0 := by
    intro s
    have hexpand : (-A) * (α s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β s • A)
        = α s • (-A) + β s • (-(A * A)) := by
      rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, neg_mul]
    rw [hexpand, mul_self_eq]
    module
  -- `φ s = exp(−s•A) · (α s • 1 + β s • A)` has zero derivative at every `s`.
  have hφderiv : ∀ s : ℝ, HasDerivAt
      (fun x => exp ℝ (x • (-A)) * (α x • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β x • A)) 0 s := by
    intro s
    have hu : HasDerivAt (fun u : ℝ => exp ℝ (u • (-A))) (exp ℝ (s • (-A)) * (-A)) s :=
      hasDerivAt_exp_smul_const (-A) s
    have hMd : HasDerivAt (fun x => α x • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β x • A)
        ((-(A.det) * β s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
          + (α s + A.trace * β s) • A) s :=
      ((hα s).smul_const _).add ((hβ s).smul_const _)
    have hprod := hu.mul hMd
    have hzero : exp ℝ (s • (-A)) * (-A) * (α s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β s • A)
        + exp ℝ (s • (-A)) * ((-(A.det) * β s) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
          + (α s + A.trace * β s) • A) = 0 := by
      rw [mul_assoc, ← mul_add, key s, mul_zero]
    rw [hzero] at hprod
    exact hprod
  -- Zero derivative everywhere ⇒ constant ⇒ equals its value `1` at `0`.
  have hdiff : Differentiable ℝ
      (fun x => exp ℝ (x • (-A)) * (α x • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β x • A)) :=
    fun s => (hφderiv s).differentiableAt
  have hderiv0 : ∀ s : ℝ,
      deriv (fun x => exp ℝ (x • (-A)) * (α x • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β x • A)) s = 0 :=
    fun s => (hφderiv s).deriv
  have hφt : exp ℝ (t • (-A)) * (α t • (1 : Matrix (Fin 2) (Fin 2) ℝ) + β t • A) = 1 := by
    have hconst := is_const_of_deriv_eq_zero hdiff hderiv0 t 0
    simpa [h0, h0'] using hconst
  -- Multiply by `exp(t•A)` on the left to extract the closed form.
  have hcomm : Commute (t • A) (t • (-A)) := by
    rw [smul_neg]; exact (Commute.refl (t • A)).neg_right
  have hinv : exp ℝ (t • A) * exp ℝ (t • (-A)) = 1 := by
    rw [← exp_add_of_commute ℝ _ _ hcomm, smul_neg, add_neg_cancel, exp_zero]
  calc exp ℝ (t • A)
      = exp ℝ (t • A) * 1 := (mul_one _).symm
    _ = exp ℝ (t • A) * (exp ℝ (t • (-A)) * (α t • 1 + β t • A)) := by rw [hφt]
    _ = (exp ℝ (t • A) * exp ℝ (t • (-A))) * (α t • 1 + β t • A) := by rw [mul_assoc]
    _ = 1 * (α t • 1 + β t • A) := by rw [hinv]
    _ = α t • 1 + β t • A := one_mul _

/-- **Distinct-eigenvalue closed form.** If `tr A = λ₁ + λ₂` and `det A = λ₁ λ₂` with
`λ₁ ≠ λ₂`, then
`exp(t•A) = (e^{λ₁t} − λ₁ β(t)) • 1 + β(t) • A` where `β(t) = (e^{λ₁t} − e^{λ₂t})/(λ₁ − λ₂)`. -/
theorem exp_two_two_distinct (A : Matrix (Fin 2) (Fin 2) ℝ) (lam1 lam2 : ℝ)
    (hne : lam1 ≠ lam2) (hτ : A.trace = lam1 + lam2) (hδ : A.det = lam1 * lam2) (t : ℝ) :
    exp ℝ (t • A)
      = (Real.exp (lam1 * t)
          - lam1 * ((Real.exp (lam1 * t) - Real.exp (lam2 * t)) / (lam1 - lam2))) • 1
        + ((Real.exp (lam1 * t) - Real.exp (lam2 * t)) / (lam1 - lam2)) • A := by
  have hd : lam1 - lam2 ≠ 0 := sub_ne_zero.mpr hne
  refine exp_eq_of_coeffs A
    (fun t => Real.exp (lam1 * t)
        - lam1 * ((Real.exp (lam1 * t) - Real.exp (lam2 * t)) / (lam1 - lam2)))
    (fun t => (Real.exp (lam1 * t) - Real.exp (lam2 * t)) / (lam1 - lam2))
    ?_ ?_ ?_ ?_ t
  · -- α' = −(det A)·β
    intro s
    have g1 : HasDerivAt (fun t : ℝ => lam1 * t) lam1 s := by
      simpa using (hasDerivAt_id s).const_mul lam1
    have g2 : HasDerivAt (fun t : ℝ => lam2 * t) lam2 s := by
      simpa using (hasDerivAt_id s).const_mul lam2
    have e1 : HasDerivAt (fun t : ℝ => Real.exp (lam1 * t)) (Real.exp (lam1 * s) * lam1) s := g1.exp
    have e2 : HasDerivAt (fun t : ℝ => Real.exp (lam2 * t)) (Real.exp (lam2 * s) * lam2) s := g2.exp
    have hβ' : HasDerivAt
        (fun t => (Real.exp (lam1 * t) - Real.exp (lam2 * t)) / (lam1 - lam2))
        ((Real.exp (lam1 * s) * lam1 - Real.exp (lam2 * s) * lam2) / (lam1 - lam2)) s :=
      (e1.sub e2).div_const _
    have hα' := e1.sub (hβ'.const_mul lam1)
    convert hα' using 1
    rw [hδ]
    field_simp
    ring
  · -- β' = α + (tr A)·β
    intro s
    have g1 : HasDerivAt (fun t : ℝ => lam1 * t) lam1 s := by
      simpa using (hasDerivAt_id s).const_mul lam1
    have g2 : HasDerivAt (fun t : ℝ => lam2 * t) lam2 s := by
      simpa using (hasDerivAt_id s).const_mul lam2
    have e1 : HasDerivAt (fun t : ℝ => Real.exp (lam1 * t)) (Real.exp (lam1 * s) * lam1) s := g1.exp
    have e2 : HasDerivAt (fun t : ℝ => Real.exp (lam2 * t)) (Real.exp (lam2 * s) * lam2) s := g2.exp
    have hβ' : HasDerivAt
        (fun t => (Real.exp (lam1 * t) - Real.exp (lam2 * t)) / (lam1 - lam2))
        ((Real.exp (lam1 * s) * lam1 - Real.exp (lam2 * s) * lam2) / (lam1 - lam2)) s :=
      (e1.sub e2).div_const _
    convert hβ' using 1
    rw [hτ]
    field_simp
    ring
  · simp
  · simp

/-- **Repeated-eigenvalue closed form.** If `tr A = 2λ` and `det A = λ²`, then
`exp(t•A) = (e^{λt} − λ t e^{λt}) • 1 + (t e^{λt}) • A`. -/
theorem exp_two_two_repeated (A : Matrix (Fin 2) (Fin 2) ℝ) (lam : ℝ)
    (hτ : A.trace = 2 * lam) (hδ : A.det = lam ^ 2) (t : ℝ) :
    exp ℝ (t • A)
      = (Real.exp (lam * t) - lam * (t * Real.exp (lam * t))) • 1
        + (t * Real.exp (lam * t)) • A := by
  refine exp_eq_of_coeffs A
    (fun t => Real.exp (lam * t) - lam * (t * Real.exp (lam * t)))
    (fun t => t * Real.exp (lam * t)) ?_ ?_ ?_ ?_ t
  · -- α' = −(det A)·β
    intro s
    have g1 : HasDerivAt (fun t : ℝ => lam * t) lam s := by
      simpa using (hasDerivAt_id s).const_mul lam
    have e1 : HasDerivAt (fun t : ℝ => Real.exp (lam * t)) (Real.exp (lam * s) * lam) s := g1.exp
    have hβ' : HasDerivAt (fun t => t * Real.exp (lam * t))
        (1 * Real.exp (lam * s) + s * (Real.exp (lam * s) * lam)) s :=
      (hasDerivAt_id s).mul e1
    have hα' := e1.sub (hβ'.const_mul lam)
    convert hα' using 1
    rw [hδ]
    ring
  · -- β' = α + (tr A)·β
    intro s
    have g1 : HasDerivAt (fun t : ℝ => lam * t) lam s := by
      simpa using (hasDerivAt_id s).const_mul lam
    have e1 : HasDerivAt (fun t : ℝ => Real.exp (lam * t)) (Real.exp (lam * s) * lam) s := g1.exp
    have hβ' : HasDerivAt (fun t => t * Real.exp (lam * t))
        (1 * Real.exp (lam * s) + s * (Real.exp (lam * s) * lam)) s :=
      (hasDerivAt_id s).mul e1
    convert hβ' using 1
    rw [hτ]
    ring
  · simp
  · simp

end

end CayleyHamiltonOQ04OQ02
