import Proofs.JensenInequalityOQ01OQ01OQ01OQ01
import Mathlib.Analysis.Convex.Function

/-
# Lyapunov's inequality: log-convexity of the weighted moment function

Let `w x : ι → ℝ` be strictly positive families on a finite index type and define the
**weighted moment function**
`A(t) = ∑ i, w i * (x i) ^ t`.

This file proves that `t ↦ A(t)` is **log-convex**, i.e. `t ↦ log A(t)` is convex on `ℝ`.
Equivalently, for all real exponents `p, r` and convex weights `a, b > 0` with `a + b = 1`,
`A(a·p + b·r) ≤ A(p)^a · A(r)^b`  (the **Lyapunov interpolation inequality**), and in the
symmetric three-exponent form, for `p < q < r`,
`A(q)^(r-p) ≤ A(p)^(r-q) · A(r)^(q-p)`.

This is a genuine structural refinement of the monotonicity of power means
(`PowerMeanMonotoneOQ`): monotonicity says `M_r` is increasing in `r`; log-convexity is a
second-order statement pinning the *shape* of the moment curve, and it implies the power-mean
inequality by interpolation.

## Engine

The whole result is a one-application consequence of the **two-function discrete Hölder
inequality** `JensenHolder.inner_le_holder_two` (from the parent file
`JensenInequalityOQ01OQ01OQ01OQ01`): with conjugate exponents `P = a⁻¹`, `Q = b⁻¹` and
`u i = (w i · x i^p)^a`, `v i = (w i · x i^r)^b`, Hölder reads exactly
`A(a·p + b·r) = ∑ u i · v i ≤ (∑ u i^P)^{1/P} · (∑ v i^Q)^{1/Q} = A(p)^a · A(r)^b`.

The pointwise interpolation identity `(w·x^p)^a · (w·x^r)^b = w^{a+b} · x^{a·p+b·r}` is the
only `rpow` bookkeeping required.

## Main results

* `moment_interp_le` — the Lyapunov interpolation inequality `A(a·p+b·r) ≤ A(p)^a · A(r)^b`.
* `logConvexOn_moment` — `t ↦ log A(t)` is convex on `ℝ` (log-convexity of moments).
* `moment_lyapunov` — the symmetric three-exponent form `A(q)^(r-p) ≤ A(p)^(r-q) · A(r)^(q-p)`.

## Mathlib gap

Mathlib has log-convexity statements for specific objects (Gamma function, `Real.Gamma`), but
no general "log-convexity of the discrete weighted moment / power-sum function", which is the
classical Lyapunov inequality underlying the interpolation theory of `Lᵖ` spaces.
-/

open Finset

namespace JensenLyapunov

variable {ι : Type*} [Fintype ι]

/-- The weighted moment function `A(t) = ∑ i, w i · (x i) ^ t`. -/
noncomputable def moment (w x : ι → ℝ) (t : ℝ) : ℝ := ∑ i, w i * (x i) ^ t

/-- The pointwise interpolation identity behind Lyapunov's inequality:
`(w·x^p)^a · (w·x^r)^b = w^{a+b} · x^{a·p+b·r}` for `w, x > 0`. -/
private lemma rpow_interp {w x : ℝ} (hw : 0 < w) (hx : 0 < x) (p r a b : ℝ) :
    (w * x ^ p) ^ a * (w * x ^ r) ^ b = w ^ (a + b) * x ^ (a * p + b * r) := by
  have e1 : (w * x ^ p) ^ a = w ^ a * x ^ (p * a) := by
    rw [Real.mul_rpow hw.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
  have e2 : (w * x ^ r) ^ b = w ^ b * x ^ (r * b) := by
    rw [Real.mul_rpow hw.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
  rw [e1, e2, mul_mul_mul_comm, ← Real.rpow_add hw, ← Real.rpow_add hx,
    show p * a + r * b = a * p + b * r from by ring]

/-- The moment function is nonnegative for nonnegative data. -/
lemma moment_nonneg (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) (t : ℝ) :
    0 ≤ moment w x t :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.rpow_nonneg (hx i) t)

/-- The moment function is strictly positive for strictly positive data (nonempty index). -/
lemma moment_pos (w x : ι → ℝ) [Nonempty ι] (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i) (t : ℝ) :
    0 < moment w x t :=
  Finset.sum_pos (fun i _ => mul_pos (hw i) (Real.rpow_pos_of_pos (hx i) t)) Finset.univ_nonempty

/-- **Lyapunov interpolation inequality.** For strictly positive families `w x : ι → ℝ`, real
exponents `p, r`, and convex weights `a, b > 0` with `a + b = 1`,
`A(a·p + b·r) ≤ A(p)^a · A(r)^b`, where `A(t) = ∑ i, w i · (x i)^t`. -/
theorem moment_interp_le (w x : ι → ℝ) (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i)
    (p r a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    moment w x (a * p + b * r) ≤ (moment w x p) ^ a * (moment w x r) ^ b := by
  calc moment w x (a * p + b * r)
      = ∑ i, (w i * x i ^ p) ^ a * (w i * x i ^ r) ^ b := by
          simp only [moment]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [rpow_interp (hw i) (hx i) p r a b, hab, Real.rpow_one]
    _ ≤ (∑ i, ((w i * x i ^ p) ^ a) ^ (a⁻¹)) ^ (a⁻¹)⁻¹
          * (∑ i, ((w i * x i ^ r) ^ b) ^ (b⁻¹)) ^ (b⁻¹)⁻¹ :=
          JensenHolder.inner_le_holder_two (univ : Finset ι)
            (fun i => (w i * x i ^ p) ^ a) (fun i => (w i * x i ^ r) ^ b)
            (a⁻¹) (b⁻¹)
            (fun i _ => Real.rpow_nonneg (mul_nonneg (hw i).le (Real.rpow_nonneg (hx i).le _)) _)
            (fun i _ => Real.rpow_nonneg (mul_nonneg (hw i).le (Real.rpow_nonneg (hx i).le _)) _)
            (inv_pos.mpr ha) (inv_pos.mpr hb)
            (by rw [inv_inv, inv_inv]; exact hab)
    _ = (moment w x p) ^ a * (moment w x r) ^ b := by
          rw [inv_inv, inv_inv]
          congr 1
          · congr 1
            simp only [moment]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Real.rpow_mul (mul_nonneg (hw i).le (Real.rpow_nonneg (hx i).le _)),
              mul_inv_cancel₀ ha.ne', Real.rpow_one]
          · congr 1
            simp only [moment]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Real.rpow_mul (mul_nonneg (hw i).le (Real.rpow_nonneg (hx i).le _)),
              mul_inv_cancel₀ hb.ne', Real.rpow_one]

/-- **Log-convexity of the weighted moment function.** For strictly positive families
`w x : ι → ℝ` on a nonempty finite index type, `t ↦ log (∑ i, w i · (x i)^t)` is convex on `ℝ`.
This is the conceptual content of Lyapunov's inequality. -/
theorem logConvexOn_moment (w x : ι → ℝ) [Nonempty ι]
    (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i) :
    ConvexOn ℝ Set.univ (fun t => Real.log (moment w x t)) := by
  refine ⟨convex_univ, ?_⟩
  intro p _ r _ a b ha hb hab
  simp only [smul_eq_mul]
  obtain rfl | ha0 := ha.eq_or_lt
  · have hb1 : b = 1 := by linarith
    subst hb1; simp
  obtain rfl | hb0 := hb.eq_or_lt
  · have ha1 : a = 1 := by linarith
    subst ha1; simp
  · have hint := moment_interp_le w x hw hx p r a b ha0 hb0 hab
    calc Real.log (moment w x (a * p + b * r))
        ≤ Real.log ((moment w x p) ^ a * (moment w x r) ^ b) :=
          Real.log_le_log (moment_pos w x hw hx _) hint
      _ = a * Real.log (moment w x p) + b * Real.log (moment w x r) := by
          rw [Real.log_mul (Real.rpow_pos_of_pos (moment_pos w x hw hx p) a).ne'
                (Real.rpow_pos_of_pos (moment_pos w x hw hx r) b).ne',
            Real.log_rpow (moment_pos w x hw hx p), Real.log_rpow (moment_pos w x hw hx r)]

/-- **Lyapunov's inequality (symmetric three-exponent form).** For strictly positive families
`w x : ι → ℝ` and exponents `p < q < r`,
`A(q)^(r-p) ≤ A(p)^(r-q) · A(r)^(q-p)`, where `A(t) = ∑ i, w i · (x i)^t`. -/
theorem moment_lyapunov (w x : ι → ℝ) (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i)
    (p q r : ℝ) (hpq : p < q) (hqr : q < r) :
    (moment w x q) ^ (r - p) ≤ (moment w x p) ^ (r - q) * (moment w x r) ^ (q - p) := by
  have hrp : 0 < r - p := by linarith
  have hrq : 0 < r - q := by linarith
  have hqp : 0 < q - p := by linarith
  have hrp' : r - p ≠ 0 := hrp.ne'
  set a := (r - q) / (r - p) with ha_def
  set b := (q - p) / (r - p) with hb_def
  have ha : 0 < a := div_pos hrq hrp
  have hb : 0 < b := div_pos hqp hrp
  have hab : a + b = 1 := by
    rw [ha_def, hb_def, ← add_div, div_eq_one_iff_eq hrp']; ring
  have hq_eq : a * p + b * r = q := by rw [ha_def, hb_def]; field_simp; ring
  have hexp1 : a * (r - p) = r - q := by rw [ha_def, div_mul_cancel₀ _ hrp']
  have hexp2 : b * (r - p) = q - p := by rw [hb_def, div_mul_cancel₀ _ hrp']
  have hint := moment_interp_le w x hw hx p r a b ha hb hab
  rw [hq_eq] at hint
  calc (moment w x q) ^ (r - p)
      ≤ ((moment w x p) ^ a * (moment w x r) ^ b) ^ (r - p) :=
        Real.rpow_le_rpow (moment_nonneg w x (fun i => (hw i).le) (fun i => (hx i).le) q) hint hrp.le
    _ = (moment w x p) ^ (r - q) * (moment w x r) ^ (q - p) := by
        rw [Real.mul_rpow
              (Real.rpow_nonneg (moment_nonneg w x (fun i => (hw i).le) (fun i => (hx i).le) p) a)
              (Real.rpow_nonneg (moment_nonneg w x (fun i => (hw i).le) (fun i => (hx i).le) r) b),
          ← Real.rpow_mul (moment_nonneg w x (fun i => (hw i).le) (fun i => (hx i).le) p),
          ← Real.rpow_mul (moment_nonneg w x (fun i => (hw i).le) (fun i => (hx i).le) r),
          hexp1, hexp2]

end JensenLyapunov

-- #print axioms JensenLyapunov.moment_interp_le
-- #print axioms JensenLyapunov.logConvexOn_moment
-- #print axioms JensenLyapunov.moment_lyapunov
