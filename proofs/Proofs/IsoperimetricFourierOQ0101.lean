/-
The Fourier Method for the Isoperimetric Inequality (Hurwitz–Wirtinger)

Open Question from: Isoperimetric Shapes on Other Surfaces
  (isoperimetric-theorem-oq-01-oq-01)

  "Can the spherical/hyperbolic isoperimetric inequalities be proved in Lean
   using symmetrization or Fourier methods?"

This file formalizes the *Fourier method* in its base (Euclidean) case — the
Hurwitz–Wirtinger proof of the classical isoperimetric inequality L² ≥ 4πA —
which is the exact technique the open question asks to transport to curved
surfaces. We isolate and verify its algebraic heart.

## The Fourier method, in one line

Write a closed curve of period 2π in real Fourier series

    x(s) = a₀ + Σ_{n≥1} (aₙ cos ns + αₙ sin ns)
    y(s) = b₀ + Σ_{n≥1} (bₙ cos ns + βₙ sin ns).

By Parseval the (Dirichlet) length energy and the Green/area functional become

    (1/π) ∮ (x'² + y'²) ds = Σ_{n≥1} n² (aₙ²+αₙ²+bₙ²+βₙ²)   =: E
    (1/π) · A             = Σ_{n≥1} n  (aₙβₙ − αₙbₙ)        =: Ar.

Hurwitz's observation is the pointwise-in-n *sum-of-squares identity*

    n²(aₙ²+αₙ²+bₙ²+βₙ²) − 2n(aₙβₙ − αₙbₙ)
       = (n aₙ − βₙ)² + (n αₙ + bₙ)² + (n²−1)(βₙ² + bₙ²),

whose right-hand side is manifestly ≥ 0 for every n ≥ 1.  Summing gives
E − 2·Ar ≥ 0 (Wirtinger's inequality), and after arc-length normalization
(E = 2, L = 2π, A = π·Ar) this is exactly L² ≥ 4πA, with equality precisely
when only the fundamental mode n = 1 survives — i.e. the curve is a circle.

## What is formalized here

We formalize the Fourier-coefficient core: the per-mode SOS identity, its
summed form (Wirtinger), the isoperimetric inequality under the standard
arc-length normalization, and the equality characterization (all higher modes
vanish ⇒ circle).  This is pure real algebra over finite Fourier data; the
Parseval bridge from the L²-integrals to the coefficient sums is the standard
textbook reduction (Stein–Shakarchi, Ch. 4) and is documented, not re-derived.

The constant translation modes a₀, b₀ drop out of both E and Ar, so only the
modes n ≥ 1 are tracked.

References:
- A. Hurwitz, "Sur le problème des isopérimètres", C. R. Acad. Sci. (1901)
- E. Stein, R. Shakarchi, *Fourier Analysis*, Princeton (2003), Ch. 4
- R. Osserman, "The isoperimetric inequality", Bull. AMS 84 (1978)

Tags: fourier-analysis, isoperimetric, wirtinger, hurwitz, sum-of-squares
-/

import Mathlib

open Finset

namespace IsoperimetricFourier

/- Real Fourier data of a closed plane curve: for each mode `n` the four real
coefficients `a n, α n` (the `x`-component) and `b n, β n` (the `y`-component).
Only modes `n ≥ 1` are relevant; constant modes are translations and drop out. -/
variable (a α b β : ℕ → ℝ)

/-- The length (Dirichlet) energy in Fourier coordinates:
`(1/π) ∮ (x'² + y'²) ds = Σ n² (aₙ²+αₙ²+bₙ²+βₙ²)` by Parseval. -/
def lengthEnergy (s : Finset ℕ) : ℝ :=
  ∑ n ∈ s, (n : ℝ) ^ 2 * (a n ^ 2 + α n ^ 2 + b n ^ 2 + β n ^ 2)

/-- The enclosed signed area in Fourier coordinates:
`(1/π) · A = Σ n (aₙβₙ − αₙbₙ)` by Green's theorem and Parseval. -/
def areaFourier (s : Finset ℕ) : ℝ :=
  ∑ n ∈ s, (n : ℝ) * (a n * β n - α n * b n)

/-- Hurwitz's per-mode sum-of-squares term. Manifestly `≥ 0` when `n ≥ 1`. -/
def hurwitzTerm (n : ℕ) : ℝ :=
  ((n : ℝ) * a n - β n) ^ 2 + ((n : ℝ) * α n + b n) ^ 2
    + ((n : ℝ) ^ 2 - 1) * (β n ^ 2 + b n ^ 2)

/-!
## Part I: The Hurwitz sum-of-squares identity
-/

/-- The algebraic heart, mode by mode:
`n²(aₙ²+αₙ²+bₙ²+βₙ²) − 2n(aₙβₙ − αₙbₙ) = hurwitzTerm n`. -/
theorem hurwitz_mode_identity (n : ℕ) :
    (n : ℝ) ^ 2 * (a n ^ 2 + α n ^ 2 + b n ^ 2 + β n ^ 2)
        - 2 * ((n : ℝ) * (a n * β n - α n * b n))
      = hurwitzTerm a α b β n := by
  simp only [hurwitzTerm]; ring

/-- Summed form: the isoperimetric deficit `E − 2·Ar` equals the (nonnegative)
sum of the per-mode Hurwitz terms. -/
theorem hurwitz_deficit_identity (s : Finset ℕ) :
    lengthEnergy a α b β s - 2 * areaFourier a α b β s
      = ∑ n ∈ s, hurwitzTerm a α b β n := by
  unfold lengthEnergy areaFourier
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => hurwitz_mode_identity a α b β n

/-!
## Part II: Nonnegativity (Wirtinger's inequality)
-/

/-- Each Hurwitz term is nonnegative for a genuine mode `n ≥ 1`. -/
theorem hurwitzTerm_nonneg (n : ℕ) (hn : 1 ≤ n) : 0 ≤ hurwitzTerm a α b β n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by nlinarith [hn1, sq_nonneg ((n : ℝ) - 1)]
  have h3 : (0 : ℝ) ≤ β n ^ 2 + b n ^ 2 := by positivity
  simp only [hurwitzTerm]
  nlinarith [sq_nonneg ((n : ℝ) * a n - β n), sq_nonneg ((n : ℝ) * α n + b n),
    mul_nonneg h2 h3]

/-- **Wirtinger's inequality (Fourier form).** For Fourier data supported on
modes `n ≥ 1`, twice the area functional never exceeds the length energy:
`2·Ar ≤ E`. This is the Fourier-analytic core of the isoperimetric inequality. -/
theorem wirtinger (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) :
    2 * areaFourier a α b β s ≤ lengthEnergy a α b β s := by
  have h : 0 ≤ lengthEnergy a α b β s - 2 * areaFourier a α b β s := by
    rw [hurwitz_deficit_identity]
    exact Finset.sum_nonneg fun n hn => hurwitzTerm_nonneg a α b β n (hs n hn)
  linarith

/-!
## Part III: The isoperimetric inequality

After arc-length parametrization the curve has length `L = 2π`, the energy is
normalized to `E = 2` (since `∮(x'²+y'²) ds = 2π`), and the area is `A = π·Ar`.
Wirtinger's inequality then yields `Ar ≤ 1`, i.e. `A ≤ π`, i.e. `L² ≥ 4πA`.
-/

/-- **The Fourier (Hurwitz) isoperimetric inequality.** A closed curve given by
arc-length-normalized Fourier data (`lengthEnergy = 2`) with length `L = 2π` and
area `A = π · areaFourier` satisfies `4πA ≤ L²`. -/
theorem isoperimetric_fourier (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (L A : ℝ) (hL : L = 2 * π) (hnorm : lengthEnergy a α b β s = 2)
    (hA : A = π * areaFourier a α b β s) :
    4 * π * A ≤ L ^ 2 := by
  have hw := wirtinger a α b β s hs
  rw [hnorm] at hw
  have ha1 : areaFourier a α b β s ≤ 1 := by linarith
  subst hL; subst hA
  nlinarith [mul_nonneg (sq_nonneg π) (sub_nonneg.mpr ha1)]

/-!
## Part IV: The equality case — only a circle saturates the inequality
-/

/-- A higher mode (`n ≥ 2`) with a vanishing Hurwitz term must vanish entirely. -/
theorem hurwitzTerm_eq_zero (n : ℕ) (hn : 2 ≤ n) (h : hurwitzTerm a α b β n = 0) :
    a n = 0 ∧ α n = 0 ∧ b n = 0 ∧ β n = 0 := by
  have hn1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have h2 : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith [hn1, sq_nonneg ((n : ℝ) - 2)]
  simp only [hurwitzTerm] at h
  have s1 := sq_nonneg ((n : ℝ) * a n - β n)
  have s2 := sq_nonneg ((n : ℝ) * α n + b n)
  have s3 : (0 : ℝ) ≤ β n ^ 2 + b n ^ 2 := by positivity
  have hprod : (0 : ℝ) ≤ ((n : ℝ) ^ 2 - 1) * (β n ^ 2 + b n ^ 2) :=
    mul_nonneg (le_of_lt h2) s3
  -- The three nonnegative summands of `h` each vanish.
  have e3 : ((n : ℝ) ^ 2 - 1) * (β n ^ 2 + b n ^ 2) = 0 :=
    le_antisymm (by nlinarith [s1, s2]) hprod
  have hbb : β n ^ 2 + b n ^ 2 = 0 := by
    rcases mul_eq_zero.mp e3 with h' | h'
    · exfalso; linarith
    · exact h'
  have hβ2 : β n ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (b n)]) (sq_nonneg _)
  have hb2 : b n ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg (β n)]) (sq_nonneg _)
  have hβ : β n = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hβ2
  have hbn : b n = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp hb2
  have he1 : ((n : ℝ) * a n - β n) ^ 2 = 0 :=
    le_antisymm (by nlinarith [s2, e3]) (sq_nonneg _)
  have he2 : ((n : ℝ) * α n + b n) ^ 2 = 0 :=
    le_antisymm (by nlinarith [s1, e3]) (sq_nonneg _)
  have ha0 : (n : ℝ) * a n - β n = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp he1
  have hα0 : (n : ℝ) * α n + b n = 0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp he2
  have hna : (n : ℝ) * a n = 0 := by rw [hβ] at ha0; linarith
  have hnα : (n : ℝ) * α n = 0 := by rw [hbn] at hα0; linarith
  exact ⟨(mul_eq_zero.mp hna).resolve_left hnne,
         (mul_eq_zero.mp hnα).resolve_left hnne, hbn, hβ⟩

/-- **Equality case ⇒ circle.** If the isoperimetric inequality is saturated
(`E = 2·Ar`), then every mode `n ≥ 2` vanishes: only the fundamental mode `n = 1`
survives, and a single-mode curve is a circle. -/
theorem equality_implies_circle (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n)
    (heq : lengthEnergy a α b β s = 2 * areaFourier a α b β s) :
    ∀ n ∈ s, 2 ≤ n → a n = 0 ∧ α n = 0 ∧ b n = 0 ∧ β n = 0 := by
  have hsum : ∑ n ∈ s, hurwitzTerm a α b β n = 0 := by
    rw [← hurwitz_deficit_identity]; linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    fun n hn => hurwitzTerm_nonneg a α b β n (hs n hn)).mp hsum
  intro n hn hn2
  exact hurwitzTerm_eq_zero a α b β n hn2 (hz n hn)

/-!
## Part V: The circle achieves equality (non-vacuity)

The fundamental mode alone, `x(s) = r cos s`, `y(s) = r sin s` — a circle of
radius `r` — saturates Wirtinger's inequality. With `r = 1` this is the unit
circle: `E = 2`, `Ar = 1`, hence `L² = 4π² = 4πA`.
-/

/-- The unit circle (`a₁ = β₁ = 1`, all other coefficients `0`) has length
energy `2`. -/
example :
    lengthEnergy (fun n => if n = 1 then 1 else 0) (fun _ => 0)
      (fun _ => 0) (fun n => if n = 1 then 1 else 0) {1} = 2 := by
  norm_num [lengthEnergy, Finset.sum_singleton]

/-- The unit circle saturates Wirtinger: `areaFourier = 1`, half the energy. -/
example :
    areaFourier (fun n => if n = 1 then 1 else 0) (fun _ => 0)
      (fun _ => 0) (fun n => if n = 1 then 1 else 0) {1} = 1 := by
  norm_num [areaFourier, Finset.sum_singleton]

end IsoperimetricFourier
