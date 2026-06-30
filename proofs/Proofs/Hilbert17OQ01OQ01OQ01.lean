/-
  Hilbert's 17th problem, univariate case — SHARPNESS of the Fejér–Riesz degree
  bound.

  The parent file `Proofs/Hilbert17OQ01OQ01.lean` proves the degree-sharp
  *existence* statement (Fejér–Riesz):

      every PSD `p : ℝ[X]` is `u² + v²` with `2·deg u ≤ deg p` and
      `2·deg v ≤ deg p`.

  That is an UPPER bound on the certificate degree.  This file proves the
  matching SHARPNESS / converse: the bound is achieved exactly, in *every*
  sum-of-two-squares representation — not just the one the existence proof
  happens to produce.

  The crux is a leading-term non-cancellation fact special to the reals:

      `natDegree (u² + v²) = 2 · max (natDegree u) (natDegree v)`   (u, v not both 0).

  Two real squares can never cancel in top degree: when `deg u = deg v` the top
  coefficient of `u² + v²` is `(lc u)² + (lc v)²`, a sum of two real squares that
  vanishes only if both `u, v` vanish.  (Over ℂ this fails: `X² + (iX)² = 0`.)

  Consequences pinned down here:

    * `two_sos_max_degree_eq`  — in ANY `p = u² + v²` with `p ≠ 0`, the larger
      summand has degree *exactly* `½·deg p`.  So the Fejér–Riesz upper bound
      `2·deg u ≤ deg p` cannot be improved: equality holds for `max(u, v)`.
    * `natDegree_two_sos_even` — the degree of any nonzero sum of two real
      squares is even (an immediate structural corollary).
    * `univariate_psd_two_sos_degree_exact` — strengthens the parent existence
      theorem: the witnesses can be taken with `2·max(deg u, deg v) = deg p`.

  Fully elementary and 0-axiom, like the parent.
-/
import Mathlib
import Proofs.Hilbert17OQ01OQ01

namespace Hilbert17OQ01OQ01OQ01

open Polynomial
open Hilbert17UnivariatePSDSOS (IsPSD)

/-- **Leading-term non-cancellation for real sums of two squares.**

The degree of `u² + v²` is exactly twice the larger of `deg u`, `deg v`.  The
only nontrivial case is `deg u = deg v`, where the top coefficient is
`(lc u)² + (lc v)²`; over an ordered field this is `0` only when both leading
coefficients vanish, i.e. both polynomials are zero. -/
theorem natDegree_sq_add_sq {u v : ℝ[X]} (h : u ≠ 0 ∨ v ≠ 0) :
    (u ^ 2 + v ^ 2).natDegree = 2 * max u.natDegree v.natDegree := by
  rcases lt_trichotomy u.natDegree v.natDegree with hlt | heq | hgt
  · -- `deg u < deg v`: the `v²` term strictly dominates.
    have hd : (u ^ 2).natDegree < (v ^ 2).natDegree := by
      rw [natDegree_pow, natDegree_pow]; omega
    rw [natDegree_add_eq_right_of_natDegree_lt hd, natDegree_pow, max_eq_right hlt.le]
  · -- `deg u = deg v`: the top coefficients are `(lc u)²` and `(lc v)²`; no
    -- cancellation since `(lc u)² + (lc v)² = 0 → u = v = 0`.
    set a := u.natDegree with ha
    have hnu : (u ^ 2).natDegree = 2 * a := by rw [natDegree_pow]
    have hnv : (v ^ 2).natDegree = 2 * a := by rw [natDegree_pow, ← heq]
    -- upper bound on the degree of the sum
    have hub : (u ^ 2 + v ^ 2).natDegree ≤ 2 * a := by
      refine le_trans (natDegree_add_le _ _) ?_
      rw [hnu, hnv, max_self]
    -- the coefficient at degree `2a` is `(lc u)² + (lc v)²`
    have e1 : (u ^ 2).coeff (2 * a) = u.leadingCoeff ^ 2 := by
      have : (u ^ 2).coeff (2 * a) = (u ^ 2).leadingCoeff := by rw [← hnu]; rfl
      rw [this, leadingCoeff_pow]
    have e2 : (v ^ 2).coeff (2 * a) = v.leadingCoeff ^ 2 := by
      have : (v ^ 2).coeff (2 * a) = (v ^ 2).leadingCoeff := by rw [← hnv]; rfl
      rw [this, leadingCoeff_pow]
    have hne : (u ^ 2 + v ^ 2).coeff (2 * a) ≠ 0 := by
      rw [coeff_add, e1, e2]
      rcases h with hu | hv
      · have hpos := pow_two_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hu)
        nlinarith [sq_nonneg v.leadingCoeff]
      · have hpos := pow_two_pos_of_ne_zero (leadingCoeff_ne_zero.mpr hv)
        nlinarith [sq_nonneg u.leadingCoeff]
    have hlb : 2 * a ≤ (u ^ 2 + v ^ 2).natDegree := le_natDegree_of_ne_zero hne
    have hmax : max a v.natDegree = a := by rw [← heq, max_self]
    rw [hmax]; omega
  · -- `deg u > deg v`: symmetric to the first case.
    have hd : (v ^ 2).natDegree < (u ^ 2).natDegree := by
      rw [natDegree_pow, natDegree_pow]; omega
    rw [natDegree_add_eq_left_of_natDegree_lt hd, natDegree_pow, max_eq_left hgt.le]

/-- **Sharpness of the Fejér–Riesz degree bound.**

In *any* representation of a nonzero polynomial as a sum of two real squares, the
larger summand has degree *exactly* `½·deg p`.  Combined with the parent's upper
bound `2·deg u ≤ deg p`, this shows the bound is attained and cannot be lowered. -/
theorem two_sos_max_degree_eq {p u v : ℝ[X]} (hp : p ≠ 0) (huv : p = u ^ 2 + v ^ 2) :
    2 * max u.natDegree v.natDegree = p.natDegree := by
  have h : u ≠ 0 ∨ v ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hp (by rw [huv, hc.1, hc.2]; ring)
  rw [huv, natDegree_sq_add_sq h]

/-- The degree of any nonzero sum of two real squares is even.  (Structural
corollary of the exact-degree formula: `deg p = 2 · max(deg u, deg v)`.) -/
theorem natDegree_two_sos_even {p u v : ℝ[X]} (hp : p ≠ 0) (huv : p = u ^ 2 + v ^ 2) :
    Even p.natDegree :=
  ⟨max u.natDegree v.natDegree, by rw [← two_sos_max_degree_eq hp huv]; ring⟩

/-- **Degree-exact Fejér–Riesz.**  Strengthening the parent existence theorem:
every nonzero PSD univariate polynomial is a sum of two squares whose larger
summand has degree *exactly* `½·deg p` (so the certificate degree is forced, not
merely bounded above). -/
theorem univariate_psd_two_sos_degree_exact (p : ℝ[X]) (hp : p ≠ 0) (h : IsPSD p) :
    ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 ∧ 2 * max u.natDegree v.natDegree = p.natDegree := by
  obtain ⟨u, v, huv, _, _⟩ := Hilbert17OQ01OQ01.univariate_psd_is_two_sos_deg p h
  exact ⟨u, v, huv, two_sos_max_degree_eq hp huv⟩

end Hilbert17OQ01OQ01OQ01
