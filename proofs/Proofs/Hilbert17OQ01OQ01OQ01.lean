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

  Finally, the representation can be put into an **asymmetric normal form**.  The
  sharpness result only says the *larger* square hits `½·deg p`; it leaves open
  whether the *other* square can always be pushed strictly below.  It can:

    * `two_sos_rotate_normalize` — a constant orthogonal rotation
      `(u, v) ↦ (αu+βv, -βu+αv)` with `α²+β²=1` preserves `u²+v²` (it is the
      polynomial avatar of multiplying the Gaussian factor by a unit complex
      number).  Aligning the rotation with the top coefficients kills the leading
      term of the second component, giving `u'² + v'²` with `deg u' = n` and
      `deg v' < n` (`n = max(deg u, deg v)`).  No complex factorization is used —
      just a `2×2` rotation of the coefficient pair.
    * `univariate_psd_two_sos_normalized` — consequently every PSD `p` of degree
      `≥ 2` is `u² + v²` with `2·deg u = deg p` and `2·deg v < deg p`: one square
      of degree *exactly* `½·deg p`, the other *strictly* smaller.

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

/-- **Constant orthogonal rotation of a two-squares pair (asymmetric normal form).**

The pair `(u, v)` and the rotated pair `(αu+βv, -βu+αv)` produce the *same* sum of
two squares whenever `α² + β² = 1` — this is the polynomial avatar of multiplying
the complex factor `u + iv` by a unit `α - iβ`.  Choosing the rotation that aligns
with the top coefficients `(a, b) = (uₙ, vₙ)`, namely `α = a/s`, `β = b/s` with
`s = √(a²+b²)`, sends the leading coefficient of the second component to
`-βa + αb = 0` while that of the first becomes `αa + βb = s ≠ 0`.

Hence any two-squares pair whose larger degree `n = max(deg u, deg v)` is positive
can be normalized to `u'² + v'² = u² + v²` with `deg u' = n` and `deg v' < n`. -/
theorem two_sos_rotate_normalize (u v : ℝ[X])
    (hn : 1 ≤ max u.natDegree v.natDegree) :
    ∃ u' v' : ℝ[X], u' ^ 2 + v' ^ 2 = u ^ 2 + v ^ 2 ∧
      u'.natDegree = max u.natDegree v.natDegree ∧
      v'.natDegree < max u.natDegree v.natDegree := by
  set n := max u.natDegree v.natDegree with hn_def
  set a := u.coeff n with ha_def
  set b := v.coeff n with hb_def
  -- the top coefficient achieving the max is nonzero, so `a² + b² > 0`
  have habpos : 0 < a ^ 2 + b ^ 2 := by
    rcases max_choice u.natDegree v.natDegree with hmx | hmx
    · have hun : u.natDegree = n := by rw [hn_def, hmx]
      have hu0 : u ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hun; omega
      have ha0 : a ≠ 0 := by
        rw [ha_def, ← hun]; exact leadingCoeff_ne_zero.mpr hu0
      nlinarith [sq_nonneg b, pow_two_pos_of_ne_zero ha0]
    · have hvn : v.natDegree = n := by rw [hn_def, hmx]
      have hv0 : v ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hvn; omega
      have hb0 : b ≠ 0 := by
        rw [hb_def, ← hvn]; exact leadingCoeff_ne_zero.mpr hv0
      nlinarith [sq_nonneg a, pow_two_pos_of_ne_zero hb0]
  set s := Real.sqrt (a ^ 2 + b ^ 2) with hs_def
  have hspos : 0 < s := Real.sqrt_pos.mpr habpos
  have hs2 : s ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt habpos.le
  set α := a / s with hα_def
  set β := b / s with hβ_def
  have habs : α ^ 2 + β ^ 2 = 1 := by
    rw [hα_def, hβ_def, div_pow, div_pow, ← add_div, ← hs2,
      div_self (pow_ne_zero 2 hspos.ne')]
  refine ⟨C α * u + C β * v, C (-β) * u + C α * v, ?_, ?_, ?_⟩
  · -- rotation preserves the sum of two squares
    have key : (C α * u + C β * v) ^ 2 + (C (-β) * u + C α * v) ^ 2
        = ((C α) ^ 2 + (C β) ^ 2) * (u ^ 2 + v ^ 2) := by
      simp only [map_neg]; ring
    have hone : (C α) ^ 2 + (C β) ^ 2 = 1 := by
      rw [← C_pow, ← C_pow, ← C_add, habs, C_1]
    rw [key, hone, one_mul]
  · -- first component has degree exactly `n`: its `n`-th coefficient is `s ≠ 0`
    have hule : (C α * u + C β * v).natDegree ≤ n := by
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · exact le_trans (natDegree_C_mul_le α u) (le_max_left _ _)
      · exact le_trans (natDegree_C_mul_le β v) (le_max_right _ _)
    have hcoeff : (C α * u + C β * v).coeff n = s := by
      rw [coeff_add, coeff_C_mul, coeff_C_mul, ← ha_def, ← hb_def, hα_def, hβ_def]
      field_simp
      nlinarith [hs2]
    exact le_antisymm hule (le_natDegree_of_ne_zero (by rw [hcoeff]; exact hspos.ne'))
  · -- second component has degree `< n`: its `n`-th coefficient vanishes
    have hvle : (C (-β) * u + C α * v).natDegree ≤ n := by
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · exact le_trans (natDegree_C_mul_le (-β) u) (le_max_left _ _)
      · exact le_trans (natDegree_C_mul_le α v) (le_max_right _ _)
    have hcoeff : (C (-β) * u + C α * v).coeff n = 0 := by
      rw [coeff_add, coeff_C_mul, coeff_C_mul, ← ha_def, ← hb_def, hα_def, hβ_def]
      field_simp
      ring
    rcases eq_or_lt_of_le hvle with heq | hlt
    · exfalso
      have hlc : (C (-β) * u + C α * v).leadingCoeff = 0 := by
        rw [leadingCoeff, heq, hcoeff]
      rw [leadingCoeff_eq_zero.mp hlc, natDegree_zero] at heq
      omega
    · exact hlt

/-- **Asymmetric Fejér–Riesz normal form.**  Every PSD univariate polynomial of
degree at least `2` is a sum of two squares `u² + v²` in which one square has
degree *exactly* `½·deg p` and the other has degree *strictly* less.  (For the
larger square the bound is forced by `two_sos_max_degree_eq`; the strict gap on
the smaller square is achieved by the rotation `two_sos_rotate_normalize`.) -/
theorem univariate_psd_two_sos_normalized (p : ℝ[X]) (hp : 2 ≤ p.natDegree)
    (h : IsPSD p) :
    ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 ∧
      2 * u.natDegree = p.natDegree ∧ 2 * v.natDegree < p.natDegree := by
  have hp0 : p ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hp; omega
  obtain ⟨u, v, huv, _, _⟩ := Hilbert17OQ01OQ01.univariate_psd_is_two_sos_deg p h
  have hmax : 2 * max u.natDegree v.natDegree = p.natDegree := two_sos_max_degree_eq hp0 huv
  have hn : 1 ≤ max u.natDegree v.natDegree := by omega
  obtain ⟨u', v', hpres, hu'deg, hv'deg⟩ := two_sos_rotate_normalize u v hn
  refine ⟨u', v', ?_, ?_, ?_⟩
  · rw [huv, ← hpres]
  · rw [hu'deg]; exact hmax
  · omega

end Hilbert17OQ01OQ01OQ01
