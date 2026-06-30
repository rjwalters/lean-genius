/-
  Hilbert's 17th problem, univariate case — ASYMMETRIC degree normalization
  (strict Fejér–Riesz).

  The sibling file `Proofs/Hilbert17OQ01OQ01.lean` proves the *symmetric*
  Fejér–Riesz degree bound: every non-negative real univariate polynomial `p`
  is a sum of two squares `p = u² + v²` with **both** summands of degree at most
  `½·deg p`,

      2·deg u ≤ deg p   and   2·deg v ≤ deg p.

  That bound is symmetric in `u` and `v`, so it does not say which of the two
  squares carries the top degree.  The classical complex-factorization picture
  is sharper: writing `p = q · q̄` for a complex polynomial `q` of degree
  `n = ½·deg p` with *real* leading coefficient gives `p = (Re q)² + (Im q)²`
  with `deg (Re q) = n` and `deg (Im q) < n`.  That is, one summand attains the
  full half-degree exactly and the other is **strictly** smaller.

  This file proves that strict asymmetric normalization, working entirely inside
  the real strong-induction engine of the sibling file (no complex factorization
  in the proof itself — only the existence of complex roots, already used to
  extract real linear / quadratic factors).  The invariant carried through the
  induction is

      2·deg u = deg p   and   v.degree < u.degree,

  using the `WithBot ℕ`-valued `Polynomial.degree` so that the zero polynomial
  (`degree 0 = ⊥`) is uniformly the strictly-smaller summand.  This pins down
  that for a non-zero PSD polynomial:

    * `deg p` is even (it equals `2·deg u`);
    * the *leading* square `u²` has degree exactly `deg p`, while the auxiliary
      square `v²` has strictly smaller degree.

  Both steps of the induction preserve the invariant:

    * real root `r`: `u ↦ (X - C r)·u`, `v ↦ (X - C r)·v`; multiplying both by
      the same degree-1 factor preserves `deg v < deg u` and bumps `2·deg u` by 2.
    * non-real root: Brahmagupta gives `u ↦ (X-C re)·u − (C im)·v`,
      `v ↦ (X-C re)·v + (C im)·u`.  The new `u` keeps top degree `deg u + 1`
      (the `(C im)·v` correction has strictly smaller degree), while the new `v`
      has degree `≤ deg u < deg u + 1`, so strictness is preserved.

  Fully elementary and 0-axiom, like the sibling file.
-/
import Mathlib
import Proofs.Hilbert17UnivariatePSDSOS

namespace Hilbert17OQ01OQ01OQ02

open Polynomial Filter Topology
open Hilbert17UnivariatePSDSOS (IsPSD sq_dvd_of_psd_root nonneg_of_forall_gt)

/-- `WithBot ℕ` addition is strictly monotone on the right summand provided the
    larger left summand is not `⊥` (which would absorb).  Used to compare
    polynomial degrees through the inductive construction. -/
private lemma wb_add_lt {a b c d : WithBot ℕ} (h1 : a ≤ b) (h2 : c < d)
    (hb : b ≠ ⊥) : a + c < b + d := by
  lift b to ℕ using hb with bn
  lift d to ℕ using (by rintro rfl; exact not_lt_bot h2) with dn
  cases a with
  | bot =>
    rw [WithBot.bot_add]; exact bot_lt_iff_ne_bot.mpr (by simp [WithBot.add_eq_bot])
  | coe an =>
    cases c with
    | bot =>
      rw [WithBot.add_bot]; exact bot_lt_iff_ne_bot.mpr (by simp [WithBot.add_eq_bot])
    | coe cn =>
      have han : an ≤ bn := WithBot.coe_le_coe.mp h1
      have hcn : cn < dn := WithBot.coe_lt_coe.mp h2
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_lt_coe]; omega

/-- In `WithBot ℕ`, `a < b` upgrades to `1 + a ≤ b` (the successor bound). -/
private lemma wb_one_add_le {a b : WithBot ℕ} (h : a < b) : 1 + a ≤ b := by
  cases a with
  | bot => rw [WithBot.add_bot]; exact bot_le
  | coe an =>
    cases b with
    | bot => exact absurd h not_lt_bot
    | coe bn =>
      have : an < bn := WithBot.coe_lt_coe.mp h
      rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]; omega

/-- **Strict asymmetric strong-induction engine.**  Every *non-zero* PSD
    polynomial of degree `d` is a sum of two squares `u² + v²` with
    `2·deg u = deg p` (so `u²` carries the full degree) and `v.degree < u.degree`
    (the auxiliary square is strictly smaller). -/
theorem psd_asym_aux :
    ∀ (d : ℕ) (p : ℝ[X]), p.natDegree = d → p ≠ 0 → IsPSD p →
      ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 ∧
        2 * u.natDegree = p.natDegree ∧ v.degree < u.degree := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro p hpd hp0 hnn
    by_cases hdeg : p.natDegree = 0
    · -- constant non-zero polynomial `p = C c` with `c > 0`
      have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hc : 0 ≤ p.coeff 0 := by
        have := hnn 0; rwa [← coeff_zero_eq_eval_zero] at this
      have hcpos : 0 < p.coeff 0 := by
        rcases hc.lt_or_eq with h | h
        · exact h
        · exact absurd (by rw [hpc, ← h]; simp) hp0
      have hsqrt : Real.sqrt (p.coeff 0) ≠ 0 := (Real.sqrt_pos.mpr hcpos).ne'
      refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_, ?_, ?_⟩
      · conv_lhs => rw [hpc]
        rw [← C_pow, Real.sq_sqrt hc]; ring
      · rw [natDegree_C, hdeg]
      · rw [degree_zero, degree_C hsqrt]
        exact bot_lt_iff_ne_bot.mpr (by simp)
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
        have hpdeg : p.natDegree = q.natDegree + 2 := by
          rw [hq, natDegree_mul (pow_ne_zero 2 (X_sub_C_ne_zero r)) hq0, natDegree_pow,
            natDegree_X_sub_C]; omega
        have hlt : q.natDegree < d := by omega
        obtain ⟨u, v, huv, hud, hvd⟩ := ih q.natDegree hlt q rfl hq0 hqnn
        have hu0 : u ≠ 0 := by
          rintro rfl; rw [degree_zero] at hvd; exact not_lt_bot hvd
        refine ⟨(X - C r) * u, (X - C r) * v, by rw [hq, huv]; ring, ?_, ?_⟩
        · -- `2·deg((X-r)·u) = deg p`
          rw [natDegree_mul (X_sub_C_ne_zero r) hu0, natDegree_X_sub_C, hpdeg]
          omega
        · -- `deg((X-r)·v) < deg((X-r)·u)`
          rw [degree_mul, degree_mul, degree_X_sub_C]
          exact wb_add_lt le_rfl hvd (by simp)
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
        obtain ⟨u, v, huv, hud, hvd⟩ := ih q.natDegree hlt q rfl hq0 hqnn
        have hu0 : u ≠ 0 := by
          rintro rfl; rw [degree_zero] at hvd; exact not_lt_bot hvd
        have hudeg_ne : u.degree ≠ ⊥ := mt degree_eq_bot.mp hu0
        have hQpoly : Q = (X - C z.re) ^ 2 + (C z.im) ^ 2 := by
          rw [hQ_def]
          have hC : (C (‖z‖ ^ 2) : ℝ[X]) = C (z.re ^ 2 + z.im ^ 2) := by rw [hns]
          rw [hC]; simp only [C_add, C_pow, C_mul, map_ofNat]; ring
        set U := (X - C z.re) * u - (C z.im) * v with hU
        set V := (X - C z.re) * v + (C z.im) * u with hV
        -- degree of `(X - C re)·u` is `deg u + 1`
        have hXu : ((X - C z.re) * u).degree = u.degree + 1 := by
          rw [degree_mul, degree_X_sub_C, add_comm]
        -- the correction `(C im)·v` is strictly below `(X - C re)·u`
        have hle1 : u.degree ≤ u.degree + 1 := by
          cases hu : u.degree with
          | bot => simp
          | coe n => rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]; omega
        have hcorr_u : ((C z.im) * v).degree < ((X - C z.re) * u).degree := by
          rw [hXu, degree_mul, degree_C him, zero_add]
          exact lt_of_lt_of_le hvd hle1
        have hU_deg : U.degree = u.degree + 1 := by
          rw [hU, sub_eq_add_neg,
            degree_add_eq_left_of_degree_lt (by rw [degree_neg]; exact hcorr_u), hXu]
        have hU_nd : U.natDegree = u.natDegree + 1 := by
          have hsome : U.degree = (↑(u.natDegree + 1) : WithBot ℕ) := by
            rw [hU_deg, degree_eq_natDegree hu0]; norm_cast
          exact natDegree_eq_of_degree_eq_some hsome
        refine ⟨U, V, by rw [hq, huv, hQpoly, hU, hV]; ring, ?_, ?_⟩
        · -- `2·deg U = deg p`
          rw [hU_nd, hpdeg]; omega
        · -- `deg V < deg U = deg u + 1`
          rw [hU_deg]
          have h1 : ((X - C z.re) * v).degree ≤ u.degree := by
            rw [degree_mul, degree_X_sub_C]; exact wb_one_add_le hvd
          have h2 : ((C z.im) * u).degree ≤ u.degree :=
            le_of_eq (by rw [degree_mul, degree_C him, zero_add])
          have hV_le : V.degree ≤ u.degree :=
            le_trans (degree_add_le _ _) (max_le h1 h2)
          exact lt_of_le_of_lt hV_le (by
            cases hu : u.degree with
            | bot => exact absurd hu hudeg_ne
            | coe n =>
                rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_lt_coe]; omega)

/-- **Univariate Hilbert 17, strict asymmetric Fejér–Riesz normalization.**
    Every non-zero non-negative real univariate polynomial `p` is a sum of two
    squares `p = u² + v²` in which the *leading* square `u²` has degree exactly
    `deg p` (so `2·deg u = deg p`, and in particular `deg p` is even) while the
    auxiliary square `v²` has strictly smaller degree (`v.degree < u.degree`). -/
theorem univariate_psd_two_sos_asym (p : ℝ[X]) (hp : p ≠ 0) (h : IsPSD p) :
    ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 ∧
      2 * u.natDegree = p.natDegree ∧ v.degree < u.degree :=
  psd_asym_aux p.natDegree p rfl hp h

/-- The degree of a non-zero PSD univariate polynomial is **even** — the leading
    square `u²` from the asymmetric normalization has degree `2·deg u = deg p`. -/
theorem natDegree_even_of_psd (p : ℝ[X]) (hp : p ≠ 0) (h : IsPSD p) :
    Even p.natDegree := by
  obtain ⟨u, _, _, hud, _⟩ := univariate_psd_two_sos_asym p hp h
  exact ⟨u.natDegree, by omega⟩

/-- In the asymmetric normalization the *leading* square attains the full
    degree: `u²` has degree exactly `deg p`, while `v²` is strictly below. -/
theorem leading_square_full_degree (p : ℝ[X]) (hp : p ≠ 0) (h : IsPSD p) :
    ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 ∧
      (u ^ 2).natDegree = p.natDegree ∧ (v ^ 2).degree < (u ^ 2).degree := by
  obtain ⟨u, v, huv, hud, hvd⟩ := univariate_psd_two_sos_asym p hp h
  have hu0 : u ≠ 0 := by
    rintro rfl; rw [degree_zero] at hvd; exact not_lt_bot hvd
  refine ⟨u, v, huv, ?_, ?_⟩
  · rw [natDegree_pow]; omega
  · rw [pow_two, pow_two, degree_mul, degree_mul]
    exact wb_add_lt (le_of_lt hvd) hvd (mt degree_eq_bot.mp hu0)

/-- **Leading coefficient of a non-zero PSD polynomial is positive.**  In the
    asymmetric normal form the top coefficient comes entirely from the leading
    square `u²` (the auxiliary square `v²` has strictly smaller degree), so
    `leadingCoeff p = (leadingCoeff u)² > 0`.  This is the polynomial counterpart
    of the elementary fact that a non-negative real polynomial cannot tend to
    `−∞`; it is not implied by the symmetric Fejér–Riesz bound, which leaves the
    sign of the top coefficient undetermined. -/
theorem leadingCoeff_pos_of_psd (p : ℝ[X]) (hp : p ≠ 0) (h : IsPSD p) :
    0 < p.leadingCoeff := by
  obtain ⟨u, v, huv, hud, hvd⟩ := univariate_psd_two_sos_asym p hp h
  have hu0 : u ≠ 0 := by
    rintro rfl; rw [degree_zero] at hvd; exact not_lt_bot hvd
  have hdeg : (v ^ 2).degree < (u ^ 2).degree := by
    rw [pow_two, pow_two, degree_mul, degree_mul]
    exact wb_add_lt (le_of_lt hvd) hvd (mt degree_eq_bot.mp hu0)
  have hlc : p.leadingCoeff = (u ^ 2).leadingCoeff := by
    rw [huv, add_comm, leadingCoeff_add_of_degree_lt hdeg]
  rw [hlc, leadingCoeff_pow]
  exact pow_two_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hu0)

end Hilbert17OQ01OQ01OQ02
