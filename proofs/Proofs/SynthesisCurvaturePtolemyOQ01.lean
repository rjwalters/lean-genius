import Proofs.SynthesisCurvaturePtolemy
import Mathlib.Tactic

/-!
# Synthesis: curvatureSin satisfies the curvature ODE  y'' + K·y = 0  (OQ-01)

Building on `SynthesisCurvaturePtolemy.lean`, which defines the
curvature-parametrized function

  curvatureSin K t =
    | t                          (K = 0,  Euclidean)
    | sin (√K · t) / √K          (K > 0,  spherical)
    | sinh (√(-K) · t) / √(-K)   (K < 0,  hyperbolic)

and already establishes the initial conditions

  curvatureSin K 0 = 0       (`curvatureSin_zero_right`)
  (curvatureSin K)'(0) = 1   (`curvatureSin_hasDerivAt_zero`),

this file proves the **defining second-order ODE**

  y'' + K · y = 0       where  y = curvatureSin K.

Together with the two initial conditions, this is the unique-solution
characterization referenced in the parent file's docstring: `curvatureSin K`
is THE solution of `y'' + K·y = 0` with `y(0) = 0`, `y'(0) = 1`. This unifies
the three constant-curvature model geometries under a single linear ODE.

## Structure

1. `curvatureCos K t` — the first derivative ("curvature cosine"):
   1 (K=0), cos(√K t) (K>0), cosh(√(-K) t) (K<0).
2. `curvatureSin_hasDerivAt`   :  (curvatureSin K)' t = curvatureCos K t
3. `curvatureCos_hasDerivAt`   :  (curvatureCos K)' t = -K · curvatureSin K t
4. `curvatureSin_deriv_eq`     :  deriv (curvatureSin K) = curvatureCos K
5. `curvatureSin_second_deriv` :  (curvatureSin K)'' t = -K · curvatureSin K t
6. `curvatureSin_satisfies_ode`:  (curvatureSin K)'' t + K · curvatureSin K t = 0

The first-derivative closed forms and the y''+K·y=0 identity are verified
symbolically (exact, no floating point) for all three cases in
`research/problems/synthesis-curvature-ptolemy-oq-01/verify_ode.py`.
-/

namespace SynthesisCurvaturePtolemyOQ01

open Real

/-- Auxiliary: derivative of `Real.sinh` is `Real.cosh` (re-derived from `exp`,
since the parent file's version is `private`). -/
private theorem hasDerivAt_sinh (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x := by
  have h1 := Real.hasDerivAt_exp x
  have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hsinhDef : Real.sinh = fun y => (Real.exp y - Real.exp (-y)) / 2 := by
    ext y; exact Real.sinh_eq y
  rw [hsinhDef]
  have hcoshEq : Real.cosh x = (Real.exp x + Real.exp (-x)) / 2 := Real.cosh_eq x
  rw [hcoshEq]
  convert (h1.sub h2).div_const 2 using 1
  ring

/-- Auxiliary: derivative of `Real.cosh` is `Real.sinh` (re-derived from `exp`). -/
private theorem hasDerivAt_cosh (x : ℝ) : HasDerivAt Real.cosh (Real.sinh x) x := by
  have h1 := Real.hasDerivAt_exp x
  have h2 := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hcoshDef : Real.cosh = fun y => (Real.exp y + Real.exp (-y)) / 2 := by
    ext y; exact Real.cosh_eq y
  rw [hcoshDef]
  have hsinhEq : Real.sinh x = (Real.exp x - Real.exp (-x)) / 2 := Real.sinh_eq x
  rw [hsinhEq]
  convert (h1.add h2).div_const 2 using 1
  ring

/-- The **curvatureCos K** function: the first derivative of `curvatureSin K`.

- K = 0 (Euclidean):   curvatureCos 0 t = 1
- K > 0 (spherical):   curvatureCos K t = cos (√K · t)
- K < 0 (hyperbolic):  curvatureCos K t = cosh (√(-K) · t) -/
noncomputable def curvatureCos (K t : ℝ) : ℝ :=
  if K = 0 then 1
  else if 0 < K then Real.cos (Real.sqrt K * t)
  else Real.cosh (Real.sqrt (-K) * t)

@[simp]
lemma curvatureCos_zero (t : ℝ) : curvatureCos 0 t = 1 := by
  simp [curvatureCos]

lemma curvatureCos_pos {K : ℝ} (hK : 0 < K) (t : ℝ) :
    curvatureCos K t = Real.cos (Real.sqrt K * t) := by
  simp only [curvatureCos, if_neg (ne_of_gt hK), if_pos hK]

lemma curvatureCos_neg {K : ℝ} (hK : K < 0) (t : ℝ) :
    curvatureCos K t = Real.cosh (Real.sqrt (-K) * t) := by
  simp only [curvatureCos, if_neg (ne_of_lt hK), if_neg (not_lt.mpr (le_of_lt hK))]

/-- **First derivative**: `(curvatureSin K)' t = curvatureCos K t` for every `t`.

This generalizes the parent file's `curvatureSin_hasDerivAt_zero` (the `t = 0`
case) to all of `ℝ`. -/
theorem curvatureSin_hasDerivAt (K t : ℝ) :
    HasDerivAt (curvatureSin K) (curvatureCos K t) t := by
  by_cases hK0 : K = 0
  · -- Euclidean: curvatureSin 0 = id, curvatureCos 0 = 1.
    subst hK0
    have hfun : curvatureSin 0 = id := by ext s; simp [curvatureSin]
    rw [hfun, curvatureCos_zero]
    exact hasDerivAt_id t
  · by_cases hKpos : 0 < K
    · -- Spherical: d/dt [sin(√K t)/√K] = cos(√K t)·√K/√K = cos(√K t).
      have hS : (Real.sqrt K : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hKpos
      have hfun : curvatureSin K = fun s => Real.sin (Real.sqrt K * s) / Real.sqrt K := by
        ext s; simp [curvatureSin, if_neg hK0, if_pos hKpos]
      rw [hfun, curvatureCos_pos hKpos]
      have h1 : HasDerivAt (fun s => Real.sqrt K * s) (Real.sqrt K) t :=
        (hasDerivAt_id t).const_mul (Real.sqrt K)
      have h2 : HasDerivAt Real.sin (Real.cos (Real.sqrt K * t)) (Real.sqrt K * t) :=
        Real.hasDerivAt_sin (Real.sqrt K * t)
      have h3 : HasDerivAt (fun s => Real.sin (Real.sqrt K * s))
          (Real.cos (Real.sqrt K * t) * Real.sqrt K) t := h2.comp t h1
      have h4 := h3.div_const (Real.sqrt K)
      rwa [mul_div_assoc, div_self hS, mul_one] at h4
    · -- Hyperbolic: d/dt [sinh(√(-K) t)/√(-K)] = cosh(√(-K) t)·√(-K)/√(-K).
      have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hKpos) hK0
      have hNK : (0 : ℝ) < -K := neg_pos.mpr hKneg
      have hS : (Real.sqrt (-K) : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hNK
      have hfun : curvatureSin K = fun s => Real.sinh (Real.sqrt (-K) * s) / Real.sqrt (-K) := by
        ext s; simp [curvatureSin, if_neg hK0, if_neg (not_lt.mpr (le_of_lt hKneg))]
      rw [hfun, curvatureCos_neg hKneg]
      have h1 : HasDerivAt (fun s => Real.sqrt (-K) * s) (Real.sqrt (-K)) t :=
        (hasDerivAt_id t).const_mul (Real.sqrt (-K))
      have h2 : HasDerivAt Real.sinh (Real.cosh (Real.sqrt (-K) * t)) (Real.sqrt (-K) * t) :=
        hasDerivAt_sinh (Real.sqrt (-K) * t)
      have h3 : HasDerivAt (fun s => Real.sinh (Real.sqrt (-K) * s))
          (Real.cosh (Real.sqrt (-K) * t) * Real.sqrt (-K)) t := h2.comp t h1
      have h4 := h3.div_const (Real.sqrt (-K))
      rwa [mul_div_assoc, div_self hS, mul_one] at h4

/-- **Second derivative**: `(curvatureCos K)' t = -K · curvatureSin K t`.

This is the heart of the ODE: differentiating the curvature cosine returns
`-K` times the curvature sine, in all three geometries. -/
theorem curvatureCos_hasDerivAt (K t : ℝ) :
    HasDerivAt (curvatureCos K) (-K * curvatureSin K t) t := by
  by_cases hK0 : K = 0
  · -- Euclidean: curvatureCos 0 = const 1, derivative 0 = -0 · t.
    subst hK0
    have hfun : curvatureCos 0 = fun _ => (1 : ℝ) := by ext s; simp [curvatureCos]
    rw [hfun]
    have : (-(0 : ℝ)) * curvatureSin 0 t = 0 := by simp
    rw [this]
    exact hasDerivAt_const t 1
  · by_cases hKpos : 0 < K
    · -- Spherical: d/dt cos(√K t) = -sin(√K t)·√K = -K·sin(√K t)/√K.
      have hS : (Real.sqrt K : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hKpos
      have hKK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (le_of_lt hKpos)
      have hfun : curvatureCos K = fun s => Real.cos (Real.sqrt K * s) := by
        ext s; rw [curvatureCos_pos hKpos]
      rw [hfun]
      have h1 : HasDerivAt (fun s => Real.sqrt K * s) (Real.sqrt K) t :=
        (hasDerivAt_id t).const_mul (Real.sqrt K)
      have h2 : HasDerivAt Real.cos (-Real.sin (Real.sqrt K * t)) (Real.sqrt K * t) :=
        Real.hasDerivAt_cos (Real.sqrt K * t)
      have h3 : HasDerivAt (fun s => Real.cos (Real.sqrt K * s))
          (-Real.sin (Real.sqrt K * t) * Real.sqrt K) t := h2.comp t h1
      convert h3 using 1
      rw [curvatureSin_pos hKpos, ← mul_div_assoc, div_eq_iff hS]
      linear_combination Real.sin (Real.sqrt K * t) * hKK
    · -- Hyperbolic: d/dt cosh(√(-K) t) = sinh(√(-K) t)·√(-K) = -K·sinh(√(-K) t)/√(-K).
      have hKneg : K < 0 := lt_of_le_of_ne (not_lt.mp hKpos) hK0
      have hNK : (0 : ℝ) < -K := neg_pos.mpr hKneg
      have hS : (Real.sqrt (-K) : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hNK
      have hKK : Real.sqrt (-K) * Real.sqrt (-K) = -K := Real.mul_self_sqrt (le_of_lt hNK)
      have hfun : curvatureCos K = fun s => Real.cosh (Real.sqrt (-K) * s) := by
        ext s; rw [curvatureCos_neg hKneg]
      rw [hfun]
      have h1 : HasDerivAt (fun s => Real.sqrt (-K) * s) (Real.sqrt (-K)) t :=
        (hasDerivAt_id t).const_mul (Real.sqrt (-K))
      have h2 : HasDerivAt Real.cosh (Real.sinh (Real.sqrt (-K) * t)) (Real.sqrt (-K) * t) :=
        hasDerivAt_cosh (Real.sqrt (-K) * t)
      have h3 : HasDerivAt (fun s => Real.cosh (Real.sqrt (-K) * s))
          (Real.sinh (Real.sqrt (-K) * t) * Real.sqrt (-K)) t := h2.comp t h1
      convert h3 using 1
      rw [curvatureSin_neg hKneg, ← mul_div_assoc, div_eq_iff hS]
      linear_combination (-Real.sinh (Real.sqrt (-K) * t)) * hKK

/-- `deriv (curvatureSin K) = curvatureCos K` as functions. -/
theorem curvatureSin_deriv_eq (K : ℝ) : deriv (curvatureSin K) = curvatureCos K := by
  ext t
  exact (curvatureSin_hasDerivAt K t).deriv

/-- The second derivative of `curvatureSin K` is `-K · curvatureSin K`. -/
theorem curvatureSin_second_deriv (K t : ℝ) :
    deriv (deriv (curvatureSin K)) t = -K * curvatureSin K t := by
  rw [curvatureSin_deriv_eq]
  exact (curvatureCos_hasDerivAt K t).deriv

/-- **Main result (OQ-01)**: `curvatureSin K` satisfies the curvature ODE

  y'' + K · y = 0

for every curvature `K ∈ ℝ` and every `t ∈ ℝ`. Combined with the parent file's
initial conditions `curvatureSin K 0 = 0` and `(curvatureSin K)'(0) = 1`, this
characterizes `curvatureSin K` as the unique solution of the constant-curvature
oscillator equation — unifying the Euclidean, spherical and hyperbolic models. -/
theorem curvatureSin_satisfies_ode (K t : ℝ) :
    deriv (deriv (curvatureSin K)) t + K * curvatureSin K t = 0 := by
  rw [curvatureSin_second_deriv]
  ring

/-- The initial conditions, restated for convenience: `y(0) = 0` and `y'(0) = 1`.
(Both are proved in the parent file; collected here as the IVP companion to the
ODE above.) -/
theorem curvatureSin_initial_conditions (K : ℝ) :
    curvatureSin K 0 = 0 ∧ deriv (curvatureSin K) 0 = 1 :=
  ⟨curvatureSin_zero_right K, curvatureSin_deriv_zero K⟩

end SynthesisCurvaturePtolemyOQ01
