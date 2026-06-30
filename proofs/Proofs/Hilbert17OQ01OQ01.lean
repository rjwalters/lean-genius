/-
  Hilbert's 17th problem, univariate case — DEGREE-SHARP refinement (Fejér–Riesz).

  The parent file `Proofs/Hilbert17UnivariatePSDSOS.lean` proves the *existence*
  statement: every non-negative real univariate polynomial `p` is a sum of two
  squares, `p = u² + v²`.  That proof produces concrete `u, v` but says nothing
  about their degrees.

  This file sharpens the result to the classical **Fejér–Riesz degree bound**:
  the two squares can be taken with

      2·deg u ≤ deg p   and   2·deg v ≤ deg p,

  i.e. each summand has degree at most ½·deg p.  This is the natural "full"
  univariate theorem — it pins down not just decomposability but the *size* of a
  certificate, which is what a sum-of-squares solver actually returns.

  The bound is proved by carrying it through the very same strong induction on
  degree used by the parent file (so the analytic crux — even multiplicity of
  real roots, `sq_dvd_of_psd_root` — is reused verbatim):

    * `p = 0` / constant: `u` constant, `v = 0`, both of degree `0 ≤ ½·deg p`.
    * real root `r`: `(X - C r)² ∣ p`, quotient `q` PSD of degree `deg p − 2`;
      `u = (X - C r)·u'`, so `deg u ≤ 1 + deg u' ≤ 1 + ½·deg q = ½·deg p`.
    * non-real root: pull out the positive quadratic `Q = (X-C re)² + (C im)²`,
      quotient `q` PSD of degree `deg p − 2`; Brahmagupta gives
      `u = (X-C re)·u' − (C im)·v'`, `v = (X-C re)·v' + (C im)·u'`, each of
      degree `≤ 1 + max(deg u', deg v') ≤ 1 + ½·deg q = ½·deg p`.

  The parent existence theorem is recovered as an immediate corollary (forget the
  bounds).  Like the parent, this file is fully elementary and 0-axiom.
-/
import Mathlib
import Proofs.Hilbert17UnivariatePSDSOS

namespace Hilbert17OQ01OQ01

open Polynomial Filter Topology
open Hilbert17UnivariatePSDSOS (IsPSD sq_dvd_of_psd_root nonneg_of_forall_gt)

/-- **Degree-sharp strong-induction engine.**  Every PSD polynomial of degree `d`
    is a sum of two squares `u² + v²` whose summands satisfy the Fejér–Riesz
    degree bound `2·deg u ≤ deg p` and `2·deg v ≤ deg p`. -/
theorem psd_eq_sq_add_sq_deg_aux :
    ∀ (d : ℕ) (p : ℝ[X]), p.natDegree = d → IsPSD p →
      ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 ∧
        2 * u.natDegree ≤ p.natDegree ∧ 2 * v.natDegree ≤ p.natDegree := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro p hpd hnn
    by_cases hp0 : p = 0
    · exact ⟨0, 0, by simp [hp0], by simp [hp0], by simp [hp0]⟩
    by_cases hdeg : p.natDegree = 0
    · -- constant polynomial `p = C c` with `c ≥ 0`
      have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hc : 0 ≤ p.coeff 0 := by
        have := hnn 0
        rwa [← coeff_zero_eq_eval_zero] at this
      refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_, ?_, ?_⟩
      · conv_lhs => rw [hpc]
        rw [← C_pow, Real.sq_sqrt hc]; ring
      · simp [natDegree_C]
      · simp
    · -- `deg p ≥ 1`: a complex root exists by the FTA
      have hdpos : 0 < (p.map (algebraMap ℝ ℂ)).degree := by
        rw [degree_map, Polynomial.degree_eq_natDegree hp0]
        exact_mod_cast Nat.pos_of_ne_zero hdeg
      obtain ⟨z, hz⟩ := Complex.exists_root hdpos
      have haeval : aeval z p = 0 := by
        rw [aeval_def, ← eval_map]; exact hz
      by_cases him : z.im = 0
      · -- real root `r = z.re`
        have hzr : z = algebraMap ℝ ℂ z.re := by
          rw [Complex.coe_algebraMap]; apply Complex.ext <;> simp [him]
        have hpr : p.eval z.re = 0 := by
          have h2 := haeval
          rw [hzr, aeval_algebraMap_apply_eq_algebraMap_eval, Complex.coe_algebraMap] at h2
          exact_mod_cast h2
        set r := z.re with hr_def
        obtain ⟨q, hq⟩ := sq_dvd_of_psd_root hp0 hnn hpr
        have hq0 : q ≠ 0 := fun h => hp0 (by rw [hq, h, mul_zero])
        -- the quotient is again PSD
        have hqnn : IsPSD q := by
          intro x
          by_cases hx : x = r
          · subst hx
            refine nonneg_of_forall_gt q.continuousAt (fun y hy => ?_)
            have hsq : (0 : ℝ) < (y - r) ^ 2 :=
              lt_of_le_of_ne (sq_nonneg _)
                (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt hy))))
            have hpy := hnn y
            rw [hq] at hpy
            simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hpy
            exact (mul_nonneg_iff_of_pos_left hsq).mp hpy
          · have hsq : (0 : ℝ) < (x - r) ^ 2 :=
              lt_of_le_of_ne (sq_nonneg _)
                (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hx)))
            have hpx := hnn x
            rw [hq] at hpx
            simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hpx
            exact (mul_nonneg_iff_of_pos_left hsq).mp hpx
        -- degree drops by exactly two
        have hpdeg : p.natDegree = q.natDegree + 2 := by
          rw [hq, natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero r)) hq0, natDegree_pow,
            natDegree_X_sub_C]; omega
        have hlt : q.natDegree < d := by omega
        obtain ⟨u, v, huv, hud, hvd⟩ := ih q.natDegree hlt q rfl hqnn
        refine ⟨(X - C r) * u, (X - C r) * v, by rw [hq, huv]; ring, ?_, ?_⟩
        · have hu_le : ((X - C r) * u).natDegree ≤ 1 + u.natDegree :=
            le_trans (natDegree_mul_le) (by rw [natDegree_X_sub_C])
          omega
        · have hv_le : ((X - C r) * v).natDegree ≤ 1 + v.natDegree :=
            le_trans (natDegree_mul_le) (by rw [natDegree_X_sub_C])
          omega
      · -- non-real root: pull out a positive real quadratic factor
        obtain ⟨q, hq⟩ := quadratic_dvd_of_aeval_eq_zero_im_ne_zero p haeval him
        set Q : ℝ[X] := X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) with hQ_def
        have hns : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        have hQpos : ∀ x, 0 < Q.eval x := by
          intro x
          have hQval : Q.eval x = (x - z.re) ^ 2 + z.im ^ 2 := by
            rw [hQ_def]
            simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
            rw [hns]; ring
          rw [hQval]
          have him2 : (0 : ℝ) < z.im ^ 2 :=
            lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 him))
          nlinarith [sq_nonneg (x - z.re), him2]
        have hq0 : q ≠ 0 := fun h => hp0 (by rw [hq, h, mul_zero])
        have hqnn : IsPSD q := by
          intro x
          have hpx := hnn x
          rw [hq, eval_mul] at hpx
          exact (mul_nonneg_iff_of_pos_left (hQpos x)).mp hpx
        have hQne : Q ≠ 0 := fun h => by simpa [h] using hQpos 0
        have hQdeg : Q.natDegree = 2 := by rw [hQ_def]; compute_degree!
        have hpdeg : p.natDegree = q.natDegree + 2 := by
          rw [hq, natDegree_mul hQne hq0, hQdeg]; omega
        have hlt : q.natDegree < d := by omega
        obtain ⟨u, v, huv, hud, hvd⟩ := ih q.natDegree hlt q rfl hqnn
        have hQpoly : Q = (X - C z.re) ^ 2 + (C z.im) ^ 2 := by
          rw [hQ_def]
          have hC : (C (‖z‖ ^ 2) : ℝ[X]) = C (z.re ^ 2 + z.im ^ 2) := by rw [hns]
          rw [hC]; simp only [C_add, C_pow, C_mul, map_ofNat]; ring
        refine ⟨(X - C z.re) * u - (C z.im) * v, (X - C z.re) * v + (C z.im) * u,
          by rw [hq, huv, hQpoly]; ring, ?_, ?_⟩
        · -- degree of first square
          have h1 : ((X - C z.re) * u - (C z.im) * v).natDegree ≤
              max ((X - C z.re) * u).natDegree ((C z.im) * v).natDegree :=
            natDegree_sub_le _ _
          have h2 : ((X - C z.re) * u).natDegree ≤ 1 + u.natDegree :=
            le_trans (natDegree_mul_le) (by rw [natDegree_X_sub_C])
          have h3 : ((C z.im) * v).natDegree ≤ v.natDegree := natDegree_C_mul_le _ _
          have h4 := le_trans h1 (max_le_max h2 h3)
          rcases le_total (1 + u.natDegree) v.natDegree with hle | hle
          · rw [max_eq_right hle] at h4; omega
          · rw [max_eq_left hle] at h4; omega
        · -- degree of second square
          have h1 : ((X - C z.re) * v + (C z.im) * u).natDegree ≤
              max ((X - C z.re) * v).natDegree ((C z.im) * u).natDegree :=
            natDegree_add_le _ _
          have h2 : ((X - C z.re) * v).natDegree ≤ 1 + v.natDegree :=
            le_trans (natDegree_mul_le) (by rw [natDegree_X_sub_C])
          have h3 : ((C z.im) * u).natDegree ≤ u.natDegree := natDegree_C_mul_le _ _
          have h4 := le_trans h1 (max_le_max h2 h3)
          rcases le_total (1 + v.natDegree) u.natDegree with hle | hle
          · rw [max_eq_right hle] at h4; omega
          · rw [max_eq_left hle] at h4; omega

/-- **Univariate Hilbert 17, degree-sharp (Fejér–Riesz).**  Every non-negative
    real univariate polynomial `p` is a sum of two squares `p = u² + v²` whose
    summands have degree at most `½·deg p`. -/
theorem univariate_psd_is_two_sos_deg (p : ℝ[X]) (h : IsPSD p) :
    ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 ∧
      2 * u.natDegree ≤ p.natDegree ∧ 2 * v.natDegree ≤ p.natDegree :=
  psd_eq_sq_add_sq_deg_aux p.natDegree p rfl h

/-- The plain existence statement (every PSD univariate polynomial is a sum of
    two squares) is the degree-sharp theorem with the bounds forgotten. -/
theorem univariate_psd_is_two_sos (p : ℝ[X]) (h : IsPSD p) :
    ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 := by
  obtain ⟨u, v, huv, _, _⟩ := univariate_psd_is_two_sos_deg p h
  exact ⟨u, v, huv⟩

end Hilbert17OQ01OQ01
