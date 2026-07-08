/-
  Hilbert's 17th problem, univariate case (Hilbert 1888):
  every non-negative real univariate polynomial is a sum of squares of polynomials.

  This file gives a fully elementary, 0-axiom proof of the univariate case, which
  discharges the parent axiom `univariate_psd_is_sos_aux` in
  `Proofs/Hilbert17SumOfSquares.lean`.

  Strategy (strong induction on degree).  A non-negative `p : ℝ[X]` is a sum of
  *two* squares `p = u² + v²`:

    * `p = 0` or `deg p = 0`: trivial (a non-negative constant is `(√c)² + 0²`).
    * `deg p ≥ 1`: by the fundamental theorem of algebra `p` has a complex root `z`.
        - `z` real (`z.im = 0`): a real root of a non-negative polynomial has
          multiplicity `≥ 2` (the analytic crux `sq_dvd_of_psd_root`, proved with
          one-sided limits), so `(X - C r)² ∣ p`; the quotient is again
          non-negative of smaller degree, and `(X - C r)²·(u² + v²)` is a sum of
          two squares.
        - `z` non-real (`z.im ≠ 0`): the real quadratic
          `Q = (X - C z.re)² + (C z.im)²` divides `p` (Mathlib's
          `quadratic_dvd_of_aeval_eq_zero_im_ne_zero`); `Q > 0` everywhere so the
          quotient is non-negative of smaller degree, and the Brahmagupta–Fibonacci
          identity turns `Q·(u² + v²)` into a sum of two squares.

  The only analytic input is continuity of polynomial evaluation; everything else
  is the FTA (`Complex.exists_root`) plus polynomial algebra already in Mathlib.
-/
import Mathlib

namespace Hilbert17UnivariatePSDSOS

open Polynomial Filter Topology

/-- A univariate real polynomial is *positive semidefinite* (PSD) if it is
    non-negative for all real inputs.  (Definitionally equal to
    `Hilbert17SumOfSquares.IsPositiveSemidefinite`.) -/
def IsPSD (p : ℝ[X]) : Prop := ∀ x : ℝ, 0 ≤ p.eval x

/-- Brahmagupta–Fibonacci identity for polynomials: a product of two sums of two
    squares is itself a sum of two squares. -/
theorem brahmagupta (a b c d : ℝ[X]) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring

/-- Continuity helper: if `f` is continuous at `r` and non-negative just to the
    right of `r`, then `f r ≥ 0`. -/
theorem nonneg_of_forall_gt {f : ℝ → ℝ} {r : ℝ} (hf : ContinuousAt f r)
    (hev : ∀ x, r < x → 0 ≤ f x) : 0 ≤ f r := by
  have ht : Tendsto f (𝓝[>] r) (𝓝 (f r)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hev x hx

/-- **Analytic crux.**  A real root `r` of a non-negative polynomial `p ≠ 0` has
    multiplicity at least two, i.e. `(X - C r)²` divides `p`.

    If the multiplicity were exactly one, `p = (X - C r)·g` with `g r ≠ 0`, and
    `p = (x - r)·g(x)` would change sign across `r` (one-sided limits force
    `g r ≥ 0` from the right and `g r ≤ 0` from the left), contradicting `g r ≠ 0`. -/
theorem sq_dvd_of_psd_root {p : ℝ[X]} (hp : p ≠ 0) (hnn : IsPSD p) {r : ℝ}
    (hr : p.eval r = 0) : (X - C r) ^ 2 ∣ p := by
  rw [← le_rootMultiplicity_iff hp]
  by_contra hlt
  push_neg at hlt
  have h1 : 0 < rootMultiplicity r p := (rootMultiplicity_pos hp).mpr hr
  have hk1 : rootMultiplicity r p = 1 := by omega
  obtain ⟨g, hg_eq, hg_ndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp r
  rw [hk1, pow_one] at hg_eq
  have hgr : g.eval r ≠ 0 := fun h0 => hg_ndvd (dvd_iff_isRoot.mpr h0)
  -- From the right: 0 ≤ g r.
  have hR : 0 ≤ g.eval r := by
    refine nonneg_of_forall_gt g.continuousAt (fun x hx => ?_)
    have hxr : (0 : ℝ) < x - r := by linarith
    have hpx := hnn x
    rw [hg_eq] at hpx
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hpx
    exact (mul_nonneg_iff_of_pos_left hxr).mp hpx
  -- From the left: g r ≤ 0.
  have hL : g.eval r ≤ 0 := by
    have ht : Tendsto (fun x => g.eval x) (𝓝[<] r) (𝓝 (g.eval r)) :=
      g.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxr : x - r < 0 := by simp only [Set.mem_Iio] at hx; linarith
    have hpx := hnn x
    rw [hg_eq] at hpx
    simp only [eval_mul, eval_sub, eval_X, eval_C] at hpx
    by_contra h
    push_neg at h
    linarith [mul_neg_of_neg_of_pos hxr h]
  exact hgr (le_antisymm hL hR)

/-- Strong-induction engine: every PSD polynomial of degree `d` is a sum of two
    squares of polynomials. -/
theorem psd_eq_sq_add_sq_aux : ∀ (d : ℕ) (p : ℝ[X]), p.natDegree = d → IsPSD p →
    ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro p hpd hnn
    by_cases hp0 : p = 0
    · exact ⟨0, 0, by simp [hp0]⟩
    by_cases hdeg : p.natDegree = 0
    · -- constant polynomial `p = C c` with `c ≥ 0`
      have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hc : 0 ≤ p.coeff 0 := by
        have := hnn 0
        rwa [← coeff_zero_eq_eval_zero] at this
      refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_⟩
      conv_lhs => rw [hpc]
      rw [← C_pow, Real.sq_sqrt hc]
      ring
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
          rw [Complex.coe_algebraMap]
          apply Complex.ext <;> simp [him]
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
        -- degree strictly drops
        have hlt : q.natDegree < d := by
          have h := hpd
          rw [hq, natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero r)) hq0,
            natDegree_pow, natDegree_X_sub_C] at h
          omega
        obtain ⟨u, v, huv⟩ := ih q.natDegree hlt q rfl hqnn
        exact ⟨(X - C r) * u, (X - C r) * v, by rw [hq, huv]; ring⟩
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
        have hlt : q.natDegree < d := by
          have hQne : Q ≠ 0 := fun h => by simpa [h] using hQpos 0
          have hQdeg : Q.natDegree = 2 := by rw [hQ_def]; compute_degree!
          have h := hpd
          rw [hq, natDegree_mul hQne hq0, hQdeg] at h
          omega
        obtain ⟨u, v, huv⟩ := ih q.natDegree hlt q rfl hqnn
        -- Brahmagupta turns `Q·(u²+v²) = ((X-C z.re)²+(C z.im)²)·(u²+v²)` into two squares
        refine ⟨(X - C z.re) * u - (C z.im) * v, (X - C z.re) * v + (C z.im) * u, ?_⟩
        have hQpoly : Q = (X - C z.re) ^ 2 + (C z.im) ^ 2 := by
          rw [hQ_def]
          have hC : (C (‖z‖ ^ 2) : ℝ[X]) = C (z.re ^ 2 + z.im ^ 2) := by rw [hns]
          rw [hC]
          simp only [C_add, C_pow, C_mul, map_ofNat]
          ring
        rw [hq, huv, hQpoly]; ring

/-- **Univariate case of Hilbert's 17th problem (Hilbert 1888).**
    Every non-negative real univariate polynomial is a sum of squares of
    polynomials.  (Here, in fact, a sum of just two squares.) -/
theorem univariate_psd_is_sos (p : ℝ[X]) (h : IsPSD p) :
    ∃ (m : ℕ) (q : Fin m → ℝ[X]), p = ∑ i, q i ^ 2 := by
  obtain ⟨u, v, huv⟩ := psd_eq_sq_add_sq_aux p.natDegree p rfl h
  refine ⟨2, ![u, v], ?_⟩
  rw [huv, Fin.sum_univ_two]
  simp

end Hilbert17UnivariatePSDSOS
