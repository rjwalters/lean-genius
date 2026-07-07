/-
  Hilbert's 17th problem, univariate case — STRUCTURAL sharpening of the
  two-squares decomposition.

  The parent file `Proofs/Hilbert17OQ01OQ01.lean` proves the degree-sharp
  Fejér–Riesz statement: every nonnegative real univariate polynomial `p` is a
  sum of two squares `p = u² + v²` with `2·deg u ≤ deg p` and `2·deg v ≤ deg p`.
  That is an *upper* bound on the certificate size.

  This file pins down the certificate exactly, via one elementary structural
  fact that the parent never isolates:

      a sum of two polynomial squares has NO degree collapse —
      `deg (u² + v²) = 2 · max (deg u) (deg v)`.

  The leading coefficients of `u²` and `v²` are both squares, hence nonnegative,
  so they can never cancel.  Three consequences follow:

    * `IsPSD.natDegree_even`     — a nonzero PSD polynomial has EVEN degree.
    * `IsPSD.leadingCoeff_pos`   — its leading coefficient is strictly positive.
    * `univariate_psd_two_sos_degree_exact` — the precise Fejér–Riesz
        normalization (the parent file's own stated open question): for `p ≠ 0`
        there is a decomposition `p = u² + v²` with `deg v < deg u` and
        `2·deg u = deg p`, i.e. one square has degree exactly `½·deg p` and the
        other strictly less.  The construction is an explicit orthogonal rotation
        `(u,v) = (c·a + s·b, c·b − s·a)` (with `c² + s² = 1`) of any existing
        decomposition `p = a² + b²`, chosen to kill the top coefficient of `v`.

  Like the parent, this file is fully elementary and 0-axiom.
-/
import Mathlib
import Proofs.Hilbert17OQ01OQ01

namespace Hilbert17OQ01OQ01OQ01

open Polynomial
open Hilbert17UnivariatePSDSOS (IsPSD)

/-- **Coefficient of a square at twice a degree ceiling.**  If `deg w ≤ n`, then
the coefficient of `w²` at index `2n` is exactly `(w.coeff n)²` — it picks out the
diagonal term and nothing else.  (For `deg w < n` both sides are `0`; for
`deg w = n` it is the leading coefficient of `w²`.) -/
theorem coeff_sq_two (w : ℝ[X]) (n : ℕ) (hw : w.natDegree ≤ n) :
    (w ^ 2).coeff (2 * n) = (w.coeff n) ^ 2 := by
  rcases lt_or_eq_of_le hw with hlt | heq
  · -- deg w < n : both sides vanish
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt natDegree_pow_le (by omega)),
      coeff_eq_zero_of_natDegree_lt hlt]
    ring
  · -- deg w = n : leading coefficient
    rcases eq_or_ne w 0 with rfl | hw0
    · simp
    · have hnd2 : (w ^ 2).natDegree = 2 * n := by
        rw [pow_two, natDegree_mul hw0 hw0, heq]; ring
      rw [← hnd2, pow_two w,
        show (w * w).coeff (w * w).natDegree = (w * w).leadingCoeff from rfl,
        leadingCoeff_mul, show w.leadingCoeff = w.coeff w.natDegree from rfl, heq, pow_two]

/-- **No degree collapse for a sum of two squares.**  Over `ℝ`,
`deg (u² + v²) = 2 · max (deg u) (deg v)`: the leading coefficients of the two
squares are nonnegative and cannot cancel. -/
theorem natDegree_sq_add_sq (u v : ℝ[X]) :
    (u ^ 2 + v ^ 2).natDegree = 2 * max u.natDegree v.natDegree := by
  -- A symmetric helper handling the case where `u` carries the maximal degree.
  have key : ∀ (p q : ℝ[X]), p ≠ 0 → q ≠ 0 → q.natDegree ≤ p.natDegree →
      (p ^ 2 + q ^ 2).natDegree = 2 * p.natDegree := by
    intro p q hp hq hqp
    have hdp : (p ^ 2).natDegree = 2 * p.natDegree := by
      rw [pow_two, natDegree_mul hp hp]; ring
    have hdq : (q ^ 2).natDegree = 2 * q.natDegree := by
      rw [pow_two, natDegree_mul hq hq]; ring
    refine le_antisymm ?_ ?_
    · calc (p ^ 2 + q ^ 2).natDegree
          ≤ max (p ^ 2).natDegree (q ^ 2).natDegree := natDegree_add_le _ _
        _ = 2 * p.natDegree := by rw [hdp, hdq, max_eq_left (by omega)]
    · apply le_natDegree_of_ne_zero
      have hcp : (p ^ 2).coeff (2 * p.natDegree) = (p.coeff p.natDegree) ^ 2 :=
        coeff_sq_two p p.natDegree le_rfl
      have hcq : 0 ≤ (q ^ 2).coeff (2 * p.natDegree) := by
        rw [coeff_sq_two q p.natDegree hqp]; positivity
      have hlc : p.coeff p.natDegree ≠ 0 := by
        rw [show p.coeff p.natDegree = p.leadingCoeff from rfl]
        exact leadingCoeff_ne_zero.mpr hp
      have hpos : 0 < (p ^ 2 + q ^ 2).coeff (2 * p.natDegree) := by
        rw [coeff_add, hcp]
        have : 0 < (p.coeff p.natDegree) ^ 2 := by positivity
        linarith
      exact hpos.ne'
  rcases eq_or_ne u 0 with rfl | hu
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    · rw [zero_pow (two_ne_zero), zero_add, natDegree_zero, max_eq_right (Nat.zero_le _),
        pow_two, natDegree_mul hv hv]; ring
  rcases eq_or_ne v 0 with rfl | hv
  · rw [zero_pow (two_ne_zero), add_zero, natDegree_zero, max_eq_left (Nat.zero_le _),
      pow_two, natDegree_mul hu hu]; ring
  rcases le_total v.natDegree u.natDegree with h | h
  · rw [max_eq_left h]; exact key u v hu hv h
  · rw [max_eq_right h, add_comm (u ^ 2) (v ^ 2)]; exact key v u hv hu h

/-- **A nonzero PSD univariate polynomial has even degree.**  Immediate from the
two-squares decomposition and the no-collapse lemma. -/
theorem IsPSD.natDegree_even {p : ℝ[X]} (h : IsPSD p) : Even p.natDegree := by
  obtain ⟨u, v, huv⟩ := Hilbert17OQ01OQ01.univariate_psd_is_two_sos p h
  rw [huv, natDegree_sq_add_sq]
  exact ⟨max u.natDegree v.natDegree, by ring⟩

/-- **A nonzero PSD univariate polynomial has positive leading coefficient.**
Writing `p = u² + v²`, the leading coefficient equals `(u.coeff n)² + (v.coeff n)²`
at `n = ½·deg p`, which is nonnegative and nonzero because `p ≠ 0`. -/
theorem IsPSD.leadingCoeff_pos {p : ℝ[X]} (hp : p ≠ 0) (h : IsPSD p) :
    0 < p.leadingCoeff := by
  obtain ⟨u, v, huv⟩ := Hilbert17OQ01OQ01.univariate_psd_is_two_sos p h
  set n := max u.natDegree v.natDegree with hn
  have hdeg : p.natDegree = 2 * n := by rw [huv, natDegree_sq_add_sq]
  have hlc : p.leadingCoeff = (u.coeff n) ^ 2 + (v.coeff n) ^ 2 := by
    rw [show p.leadingCoeff = p.coeff p.natDegree from rfl, hdeg, huv, coeff_add,
      coeff_sq_two u n (le_max_left _ _), coeff_sq_two v n (le_max_right _ _)]
  have hne : (u.coeff n) ^ 2 + (v.coeff n) ^ 2 ≠ 0 := by
    rw [← hlc]; exact leadingCoeff_ne_zero.mpr hp
  rw [hlc]
  exact lt_of_le_of_ne (by positivity) (Ne.symm hne)

/-- **Precise Fejér–Riesz normalization** — the parent file's own stated open
question.  For a nonzero PSD polynomial `p` there is a two-squares decomposition
`p = u² + v²` in which one square has degree exactly `½·deg p` and the other
strictly less: `deg v < deg u` and `2·deg u = deg p`.

The decomposition is an explicit orthogonal rotation `(u, v) = (c·a + s·b,
c·b − s·a)` (with `c² + s² = 1`) of any existing decomposition `p = a² + b²`,
with the angle chosen so that the top coefficient of the second square `v`
vanishes while that of the first square `u` becomes `r = √(la² + lb²) > 0`. -/
theorem univariate_psd_two_sos_degree_exact {p : ℝ[X]} (hp : p ≠ 0) (h : IsPSD p) :
    ∃ u v : ℝ[X], p = u ^ 2 + v ^ 2 ∧ v.degree < u.degree ∧
      2 * u.natDegree = p.natDegree := by
  obtain ⟨a, b, hab⟩ := Hilbert17OQ01OQ01.univariate_psd_is_two_sos p h
  set n := max a.natDegree b.natDegree with hn
  have hpdeg : p.natDegree = 2 * n := by rw [hab, natDegree_sq_add_sq]
  set la := a.coeff n with hla
  set lb := b.coeff n with hlb
  -- `la² + lb²` is the (positive) leading coefficient of `p`.
  have hsum_pos : 0 < la ^ 2 + lb ^ 2 := by
    have hlc : p.leadingCoeff = la ^ 2 + lb ^ 2 := by
      rw [show p.leadingCoeff = p.coeff p.natDegree from rfl, hpdeg, hab, coeff_add,
        coeff_sq_two a n (le_max_left _ _), coeff_sq_two b n (le_max_right _ _)]
    have hpos := IsPSD.leadingCoeff_pos hp h
    rwa [hlc] at hpos
  -- rotation data
  set r := Real.sqrt (la ^ 2 + lb ^ 2) with hr
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hsum_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hr_sq : r ^ 2 = la ^ 2 + lb ^ 2 := Real.sq_sqrt (le_of_lt hsum_pos)
  set c := la / r with hc
  set s := lb / r with hs
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, div_pow, div_pow, ← add_div, ← hr_sq, div_self (pow_ne_zero 2 hr_ne)]
  -- coefficient at `n` of the rotated polynomials
  have hu_coeff : (C c * a + C s * b).coeff n = r := by
    have hval : c * la + s * lb = r := by
      rw [hc, hs, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
        show la * la + lb * lb = r ^ 2 by rw [hr_sq]; ring, sq, mul_div_assoc,
        div_self hr_ne, mul_one]
    rw [coeff_add, coeff_C_mul, coeff_C_mul]; exact hval
  have hv_coeff : (C c * b - C s * a).coeff n = 0 := by
    have hval : c * lb - s * la = 0 := by
      rw [hc, hs, div_mul_eq_mul_div, div_mul_eq_mul_div, div_sub_div_same,
        show la * lb - lb * la = 0 by ring, zero_div]
    rw [coeff_sub, coeff_C_mul, coeff_C_mul]; exact hval
  -- degree bounds
  have hu_le : (C c * a + C s * b).natDegree ≤ n :=
    le_trans (natDegree_add_le _ _)
      (max_le (le_trans (natDegree_C_mul_le _ _) (le_max_left _ _))
        (le_trans (natDegree_C_mul_le _ _) (le_max_right _ _)))
  have hv_le : (C c * b - C s * a).natDegree ≤ n :=
    le_trans (natDegree_sub_le _ _)
      (max_le (le_trans (natDegree_C_mul_le _ _) (le_max_right _ _))
        (le_trans (natDegree_C_mul_le _ _) (le_max_left _ _)))
  have hu_ne : C c * a + C s * b ≠ 0 := fun hz =>
    hr_ne (by rw [← hu_coeff, hz, coeff_zero])
  have hu_deg : (C c * a + C s * b).natDegree = n :=
    le_antisymm hu_le (le_natDegree_of_ne_zero (by rw [hu_coeff]; exact hr_ne))
  -- the rotation preserves the sum of squares
  have hsum : p = (C c * a + C s * b) ^ 2 + (C c * b - C s * a) ^ 2 := by
    have hCcs : (C c) ^ 2 + (C s) ^ 2 = 1 := by
      rw [← C_pow, ← C_pow, ← C_add, hcs, map_one]
    rw [hab]; linear_combination (-(a ^ 2 + b ^ 2)) * hCcs
  -- the second square has strictly smaller degree
  have hv_deg : (C c * b - C s * a).degree < (C c * a + C s * b).degree := by
    rw [degree_eq_natDegree hu_ne, hu_deg]
    rcases eq_or_ne (C c * b - C s * a) 0 with hz | hz
    · rw [hz, degree_zero]; exact bot_lt_iff_ne_bot.mpr (by simp)
    · rw [degree_eq_natDegree hz]
      have hvne : (C c * b - C s * a).natDegree ≠ n := by
        intro hcontra
        have h0 : (C c * b - C s * a).leadingCoeff = 0 := by
          rw [show (C c * b - C s * a).leadingCoeff
              = (C c * b - C s * a).coeff (C c * b - C s * a).natDegree from rfl,
            hcontra, hv_coeff]
        rw [leadingCoeff_eq_zero] at h0; exact hz h0
      exact_mod_cast lt_of_le_of_ne hv_le hvne
  exact ⟨C c * a + C s * b, C c * b - C s * a, hsum, hv_deg, by rw [hu_deg, hpdeg]⟩

/-
  SHARPNESS in *every* representation (recovered from PR #31649).

  `univariate_psd_two_sos_degree_exact` above pins down the degree of *one*
  well-chosen decomposition.  The results below pin down what happens in ANY
  sum-of-two-squares representation, plus a standalone reusable form of the
  orthogonal-rotation normalization.
-/

/-- **Sharpness of the Fejér–Riesz degree bound.**

In *any* representation of a nonzero polynomial as a sum of two real squares, the
larger summand has degree *exactly* `½·deg p`.  Combined with the parent's upper
bound `2·deg u ≤ deg p`, this shows the bound is attained and cannot be lowered. -/
theorem two_sos_max_degree_eq {p u v : ℝ[X]} (_hp : p ≠ 0) (huv : p = u ^ 2 + v ^ 2) :
    2 * max u.natDegree v.natDegree = p.natDegree := by
  rw [huv, natDegree_sq_add_sq]

/-- The degree of any nonzero sum of two real squares is even.  (Structural
corollary of the exact-degree formula: `deg p = 2 · max(deg u, deg v)`.) -/
theorem natDegree_two_sos_even {p u v : ℝ[X]} (hp : p ≠ 0) (huv : p = u ^ 2 + v ^ 2) :
    Even p.natDegree :=
  ⟨max u.natDegree v.natDegree, by rw [← two_sos_max_degree_eq hp huv]; ring⟩

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

/-- **Asymmetric Fejér–Riesz normal form** (natDegree version).  Every PSD
univariate polynomial of degree at least `2` is a sum of two squares `u² + v²` in
which one square has degree *exactly* `½·deg p` and the other has `2·deg v`
*strictly* below `deg p`.  (For the larger square the bound is forced by
`two_sos_max_degree_eq`; the strict gap on the smaller square is achieved by the
rotation `two_sos_rotate_normalize`.) -/
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

-- Axiom audit (recovered declarations): should report only the foundational trio
-- (propext, Classical.choice, Quot.sound) — no sorryAx, no Lean.ofReduceBool.
#print axioms Hilbert17OQ01OQ01OQ01.two_sos_max_degree_eq
#print axioms Hilbert17OQ01OQ01OQ01.natDegree_two_sos_even
#print axioms Hilbert17OQ01OQ01OQ01.two_sos_rotate_normalize
#print axioms Hilbert17OQ01OQ01OQ01.univariate_psd_two_sos_normalized
