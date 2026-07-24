/-
# Erdős #1215 (cyclotomic sub-question, OQ02) — small-C DISCONNECTION of the
# QUARTIC cyclotomic lemniscates: the `φ(n) = 4` layer opens (n = 8, 12)

  Slug: erdos-1215-oq-02
  Prior work (this OQ family):
    * OQ02OQ01–07 — sharp two-sided radius/area sandwich, origin interiority (C > 1).
    * OQ02OQ08/OQ10 — radial/directional exit paths, sharp first-crossing bounds.
    * OQ02OQ11 — QUADRATIC disconnection (n = 3, 4, 6, the full `φ(n) = 2` case):
      two-focal-ball Cassini cover, disjoint when `4C < |a−b|²`.
    * OQ02OQ12 — exact TWO path components sub-threshold (per-petal star-shapedness).

  ## This file — the general finite-root disconnection engine, and `φ(n) = 4`

  OQ11's engine is hard-wired to two foci.  This file proves the DEGREE-GENERIC
  criterion and uses it to open the quartic layer:

  > **General engine** (`not_isPreconnected_lemniscate`).  Let `S` be a finite
  > set of roots, `a, b ∈ S` distinct, `C ≤ r^|S|`, and suppose every other
  > root of `S` is at distance `> 2r` from `a`.  Then
  > `{z : ‖∏_{μ∈S} (z − μ)‖ < C}` is NOT preconnected: it is covered by the
  > open balls `B(μ, r)`, the ball at `a` is disjoint from all the others,
  > and both sides of that split contain a root.
  >
  > (Covering: a point at distance `≥ r` from every root has product `≥ r^|S|
  > ≥ C`.  This subsumes OQ11's quadratic criterion — take `S = {a, b}`,
  > `r = √C` — and pre-builds the sextic layer `φ(n) = 6`: n = 7, 9, 14, 18.)

  > **Quartic corollary** (`not_isPreconnected_quartic_lemniscate`): for four
  > distinct roots `a, b, c, d` with `C ≤ r⁴` and `2r < dist a {b, c, d}`,
  > the set `{z : ‖(z−a)(z−b)(z−c)(z−d)‖ < C}` is not preconnected.

  > **Cyclotomic specializations.**  `n = 5, 8, 10, 12` are exactly the indices
  > with `φ(n) = 4`.  Here the two with quadratic-surd roots are delivered:
  > * `{|Φ₈| < C}` is DISCONNECTED for `0 < C < 1/4`
  >   (roots `(±√2 ± √2·i)/2`, minimal root gap `√2`, `2·C^{1/4} < √2`);
  > * `{|Φ₁₂| < C}` is DISCONNECTED for `0 < C < 1/16`
  >   (roots `(±√3 ± i)/2`, minimal root gap `1`).
  > Byproducts: `cyclotomic 8 ℂ = X⁴ + 1` and `cyclotomic 12 ℂ = X⁴ − X² + 1`,
  > both absent from Mathlib, via `cyclotomic_expand_eq_cyclotomic` from
  > `Φ₄ = X² + 1` (OQ11) and `Φ₆ = X² − X + 1`.

  The remaining quartic indices `n = 5, 10` have roots with NESTED radicals
  (`sin 72°`); their disconnection thresholds are recorded as a follow-up.
  Exact component counts (four petals) need the OQ12 star-shaped template at
  four foci — also a follow-up, not attempted here.

  Result status: 0 sorries, 0 axioms, no `native_decide` — axiom-free relative
  to Mathlib.  The deep `maclane_labyrinth` axiom of the parent is untouched.
-/
import Mathlib
import Proofs.Erdos1215Problem
import Proofs.CyclotomicPolynomialsOQ02OQ11

open Complex Polynomial Metric

namespace CyclotomicPolynomialsOQ02OQ13

/-! ## The general finite-root disconnection engine -/

/-- **Covering lemma**: every point of the lemniscate `{‖∏_{μ∈S}(z−μ)‖ < C}` with
`C ≤ r^|S|` lies within `r` of some root — otherwise every factor is `≥ r` and
the product is `≥ r^|S| ≥ C`. -/
theorem lemniscate_subset_biUnion (S : Finset ℂ) {C r : ℝ} (hr : 0 ≤ r)
    (hCr : C ≤ r ^ S.card) :
    {z : ℂ | ‖∏ μ ∈ S, (z - μ)‖ < C} ⊆ ⋃ μ ∈ S, Metric.ball μ r := by
  intro z hz
  rw [Set.mem_setOf_eq, norm_prod] at hz
  by_contra hcon
  simp only [Set.mem_iUnion, Metric.mem_ball, not_exists] at hcon
  have hall : ∀ μ ∈ S, r ≤ ‖z - μ‖ := by
    intro μ hμ
    have h := hcon μ hμ
    rw [not_lt, dist_eq_norm] at h
    exact h
  have hprod : r ^ S.card ≤ ∏ μ ∈ S, ‖z - μ‖ := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => hr) hall
  linarith

/-- **General disconnection criterion**: if `a, b ∈ S` are distinct roots,
`0 < C ≤ r^|S|`, and every root of `S` other than `a` is at distance `> 2r`
from `a`, then the lemniscate `{z : ‖∏_{μ∈S}(z−μ)‖ < C}` is not preconnected.
The split: the ball `B(a, r)` versus the union of the balls at the other roots. -/
theorem not_isPreconnected_lemniscate {S : Finset ℂ} {a b : ℂ} {C r : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : b ≠ a) (hC : 0 < C) (hr : 0 ≤ r)
    (hCr : C ≤ r ^ S.card)
    (hsep : ∀ μ ∈ S, μ ≠ a → 2 * r < dist a μ) :
    ¬ IsPreconnected {z : ℂ | ‖∏ μ ∈ S, (z - μ)‖ < C} := by
  intro hpre
  have hrpos : 0 < r := by
    rcases lt_or_eq_of_le hr with h | h
    · exact h
    · exfalso
      have hcard : S.card ≠ 0 := Finset.card_ne_zero.mpr ⟨a, ha⟩
      rw [← h, zero_pow hcard] at hCr
      linarith
  have hmema : a ∈ {z : ℂ | ‖∏ μ ∈ S, (z - μ)‖ < C} := by
    rw [Set.mem_setOf_eq, Finset.prod_eq_zero ha (by rw [sub_self]), norm_zero]
    exact hC
  have hmemb : b ∈ {z : ℂ | ‖∏ μ ∈ S, (z - μ)‖ < C} := by
    rw [Set.mem_setOf_eq, Finset.prod_eq_zero hb (by rw [sub_self]), norm_zero]
    exact hC
  have hcover : {z : ℂ | ‖∏ μ ∈ S, (z - μ)‖ < C} ⊆
      Metric.ball a r ∪ ⋃ μ ∈ S.erase a, Metric.ball μ r := by
    have h := lemniscate_subset_biUnion S hr hCr
    intro z hz
    have hz' := h hz
    rw [Set.mem_iUnion₂] at hz'
    obtain ⟨μ, hμS, hμz⟩ := hz'
    by_cases hμa : μ = a
    · exact Or.inl (hμa ▸ hμz)
    · exact Or.inr (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hμa, hμS⟩) hμz)
  have hdisj : Metric.ball a r ∩ (⋃ μ ∈ S.erase a, Metric.ball μ r) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Metric.mem_ball,
      Set.mem_empty_iff_false, iff_false, not_and, not_exists]
    intro hza μ hμ hzμ
    obtain ⟨hμa, hμS⟩ := Finset.mem_erase.mp hμ
    have htri : dist a μ ≤ dist a z + dist z μ := dist_triangle a z μ
    rw [dist_comm a z] at htri
    have := hsep μ hμS hμa
    linarith
  obtain ⟨z, _, hz⟩ := hpre (Metric.ball a r) (⋃ μ ∈ S.erase a, Metric.ball μ r)
    Metric.isOpen_ball (isOpen_biUnion fun _ _ => Metric.isOpen_ball) hcover
    ⟨a, hmema, Metric.mem_ball_self hrpos⟩
    ⟨b, hmemb, Set.mem_biUnion (Finset.mem_erase.mpr ⟨hab, hb⟩)
      (Metric.mem_ball_self hrpos)⟩
  rw [hdisj] at hz
  exact Set.notMem_empty z hz

/-! ## The quartic corollary -/

/-- **Quartic disconnection**: for pairwise distinct roots `a, b, c, d` with
`0 < C ≤ r⁴` and `2r < dist a μ` for `μ ∈ {b, c, d}`, the quartic lemniscate
`{z : ‖(z−a)(z−b)(z−c)(z−d)‖ < C}` is not preconnected. -/
theorem not_isPreconnected_quartic_lemniscate {a b c d : ℂ} {C r : ℝ}
    (hC : 0 < C) (hr : 0 ≤ r) (hCr : C ≤ r ^ 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsb : 2 * r < dist a b) (hsc : 2 * r < dist a c) (hsd : 2 * r < dist a d) :
    ¬ IsPreconnected {z : ℂ | ‖(z - a) * (z - b) * (z - c) * (z - d)‖ < C} := by
  have hnb : a ∉ ({b, c, d} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hab, hac, had⟩
  have hnc : b ∉ ({c, d} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨hbc, hbd⟩
  have hnd : c ∉ ({d} : Finset ℂ) := Finset.notMem_singleton.mpr hcd
  have hprod : ∀ z : ℂ, ∏ μ ∈ ({a, b, c, d} : Finset ℂ), (z - μ) =
      (z - a) * (z - b) * (z - c) * (z - d) := by
    intro z
    rw [show ({a, b, c, d} : Finset ℂ) = insert a (insert b (insert c {d})) from rfl,
      Finset.prod_insert hnb, Finset.prod_insert hnc, Finset.prod_insert hnd,
      Finset.prod_singleton]
    ring
  have hset : {z : ℂ | ‖(z - a) * (z - b) * (z - c) * (z - d)‖ < C} =
      {z : ℂ | ‖∏ μ ∈ ({a, b, c, d} : Finset ℂ), (z - μ)‖ < C} := by
    ext z
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hprod]
  have hcard : ({a, b, c, d} : Finset ℂ).card = 4 := by
    rw [show ({a, b, c, d} : Finset ℂ) = insert a (insert b (insert c {d})) from rfl,
      Finset.card_insert_of_notMem hnb, Finset.card_insert_of_notMem hnc,
      Finset.card_insert_of_notMem hnd, Finset.card_singleton]
  rw [hset]
  refine not_isPreconnected_lemniscate (a := a) (b := b)
    (by simp) (by simp) hab.symm hC hr (by rw [hcard]; exact hCr) ?_
  intro μ hμ hμa
  simp only [Finset.mem_insert, Finset.mem_singleton] at hμ
  rcases hμ with rfl | rfl | rfl | rfl
  · exact absurd rfl hμa
  · exact hsb
  · exact hsc
  · exact hsd

/-- Quartic lemniscates are not connected in the separated regime. -/
theorem not_isConnected_quartic_lemniscate {a b c d : ℂ} {C r : ℝ}
    (hC : 0 < C) (hr : 0 ≤ r) (hCr : C ≤ r ^ 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsb : 2 * r < dist a b) (hsc : 2 * r < dist a c) (hsd : 2 * r < dist a d) :
    ¬ IsConnected {z : ℂ | ‖(z - a) * (z - b) * (z - c) * (z - d)‖ < C} :=
  fun h => not_isPreconnected_quartic_lemniscate hC hr hCr hab hac had hbc hbd hcd
    hsb hsc hsd h.isPreconnected

/-- Quartic lemniscates are not path-connected in the separated regime. -/
theorem not_isPathConnected_quartic_lemniscate {a b c d : ℂ} {C r : ℝ}
    (hC : 0 < C) (hr : 0 ≤ r) (hCr : C ≤ r ^ 4)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsb : 2 * r < dist a b) (hsc : 2 * r < dist a c) (hsd : 2 * r < dist a d) :
    ¬ IsPathConnected {z : ℂ | ‖(z - a) * (z - b) * (z - c) * (z - d)‖ < C} :=
  fun h => not_isConnected_quartic_lemniscate hC hr hCr hab hac had hbc hbd hcd
    hsb hsc hsd h.isConnected

/-! ## Shared surd facts and the `C^{1/4}` radius -/

/-- `(√2 : ℂ)² = 2`, the complexified square identity for the `n = 8` roots. -/
private lemma ofReal_sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-- `(√3 : ℂ)² = 3`, the complexified square identity for the `n = 12` roots. -/
private lemma ofReal_sqrt_three_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-- The fourth-root radius `r = C^{1/4}` (as `√√C`) satisfies `r⁴ = C`. -/
private lemma sqrt_sqrt_pow_four {C : ℝ} (hC : 0 ≤ C) :
    Real.sqrt (Real.sqrt C) ^ 4 = C := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    Real.sq_sqrt (Real.sqrt_nonneg C), Real.sq_sqrt hC]

/-- From `16C < (t²)²` (with `0 ≤ t`) the fourth-root radius satisfies
`2·√√C < t` — the separation input for a minimal root gap `t`. -/
private lemma two_sqrt_sqrt_lt {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (h : 16 * C < (t ^ 2) ^ 2) :
    2 * Real.sqrt (Real.sqrt C) < t := by
  set r := Real.sqrt (Real.sqrt C) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr4 : r ^ 4 = C := sqrt_sqrt_pow_four hC
  have h4 : (2 * r) ^ 4 < t ^ 4 := by
    have e1 : (2 * r) ^ 4 = 16 * r ^ 4 := by ring
    have e2 : (t ^ 2) ^ 2 = t ^ 4 := by ring
    rw [e1, hr4]
    rw [e2] at h
    exact h
  by_contra hcon
  push Not at hcon
  exact absurd h4 (not_lt.mpr (pow_le_pow_left₀ ht hcon 4))

/-! ## `n = 8`: `Φ₈ = X⁴ + 1`, roots `(±√2 ± √2·i)/2`, minimal gap `√2`

Disconnection for `C < 1/4` (`2·C^{1/4} < √2 ⟺ 16C < 4`). -/

/-- `Φ₈ = X⁴ + 1` (absent from Mathlib): from `expand ℂ 2 Φ₄ = Φ₈` and
OQ11's `Φ₄ = X² + 1`. -/
theorem cyclotomic_eight : cyclotomic 8 ℂ = X ^ 4 + 1 := by
  have h : Polynomial.expand ℂ 2 (X ^ 2 + 1) = cyclotomic 8 ℂ := by
    have h0 := cyclotomic_expand_eq_cyclotomic Nat.prime_two
      (show 2 ∣ 4 by norm_num) ℂ
    rwa [CyclotomicPolynomialsOQ02OQ11.cyclotomic_four] at h0
  rw [← h]
  simp only [map_add, map_pow, Polynomial.expand_X, map_one]
  ring

/-- The primitive eighth root of unity `e^{iπ/4} = (√2 + √2·i)/2`. -/
noncomputable def w8a : ℂ := (Real.sqrt 2 : ℂ) / 2 * (1 + Complex.I)

/-- The primitive eighth root `e^{-iπ/4} = (√2 − √2·i)/2`. -/
noncomputable def w8b : ℂ := (Real.sqrt 2 : ℂ) / 2 * (1 - Complex.I)

/-- The primitive eighth root `e^{3iπ/4} = (−√2 + √2·i)/2`. -/
noncomputable def w8c : ℂ := (Real.sqrt 2 : ℂ) / 2 * (-1 + Complex.I)

/-- The primitive eighth root `e^{5iπ/4} = (−√2 − √2·i)/2`. -/
noncomputable def w8d : ℂ := (Real.sqrt 2 : ℂ) / 2 * (-1 - Complex.I)

/-- `Φ₈` factors over its four roots. -/
theorem cyclotomic_eight_eval_factor (z : ℂ) :
    (cyclotomic 8 ℂ).eval z = (z - w8a) * (z - w8b) * (z - w8c) * (z - w8d) := by
  rw [cyclotomic_eight]
  simp only [eval_add, eval_pow, eval_X, eval_one, w8a, w8b, w8c, w8d]
  linear_combination (-((Real.sqrt 2 : ℂ) ^ 2 + 2) / 4) * ofReal_sqrt_two_sq
    + (z ^ 2 * (Real.sqrt 2 : ℂ) ^ 2 / 2 + (Real.sqrt 2 : ℂ) ^ 4 / 4
      - (Real.sqrt 2 : ℂ) ^ 4 * (Complex.I ^ 2 + 1) / 16) * Complex.I_sq

/-- The `Φ₈` sublevel set in factored form. -/
theorem levelSet_cyclotomic_eight_eq (C : ℝ) :
    Erdos1215.levelSet (cyclotomic 8 ℂ) C =
      {z : ℂ | ‖(z - w8a) * (z - w8b) * (z - w8c) * (z - w8d)‖ < C} := by
  ext z
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq, cyclotomic_eight_eval_factor]

private lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-- `w8a − w8b = √2·i`: the vertical gap. -/
private lemma w8_sub_ab : w8a - w8b = (Real.sqrt 2 : ℂ) * Complex.I := by
  simp only [w8a, w8b]; ring

/-- `w8a − w8c = √2`: the horizontal gap. -/
private lemma w8_sub_ac : w8a - w8c = (Real.sqrt 2 : ℂ) := by
  simp only [w8a, w8c]; ring

/-- `w8a − w8d = √2·(1 + i)`: the diagonal gap. -/
private lemma w8_sub_ad : w8a - w8d = (Real.sqrt 2 : ℂ) * (1 + Complex.I) := by
  simp only [w8a, w8d]; ring

private lemma norm_w8_sub_ab : ‖w8a - w8b‖ = Real.sqrt 2 := by
  rw [w8_sub_ab, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]

private lemma norm_w8_sub_ac : ‖w8a - w8c‖ = Real.sqrt 2 := by
  rw [w8_sub_ac, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- The diagonal gap is at least `√2` (its real part). -/
private lemma norm_w8_sub_ad : Real.sqrt 2 ≤ ‖w8a - w8d‖ := by
  have hre : (w8a - w8d).re = Real.sqrt 2 := by
    rw [w8_sub_ad]
    simp [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  calc Real.sqrt 2 = (w8a - w8d).re := hre.symm
    _ ≤ |(w8a - w8d).re| := le_abs_self _
    _ ≤ ‖w8a - w8d‖ := Complex.abs_re_le_norm _

private lemma w8_ab_ne : w8a ≠ w8b := by
  intro h
  have h0 := w8_sub_ab
  rw [h, sub_self] at h0
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt sqrt_two_pos))
    Complex.I_ne_zero h0.symm

private lemma w8_ac_ne : w8a ≠ w8c := by
  intro h
  have h0 := w8_sub_ac
  rw [h, sub_self] at h0
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt sqrt_two_pos) h0.symm

private lemma w8_ad_ne : w8a ≠ w8d := by
  intro h
  have h0 := w8_sub_ad
  rw [h, sub_self] at h0
  have : (1 + Complex.I) ≠ 0 := by
    intro h1
    have := congrArg Complex.re h1
    simp at this
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt sqrt_two_pos)) this h0.symm

private lemma w8_bc_ne : w8b ≠ w8c := by
  intro h
  have h0 : w8b - w8c = (Real.sqrt 2 : ℂ) * (1 - Complex.I) := by
    simp only [w8b, w8c]; ring
  rw [h, sub_self] at h0
  have : (1 - Complex.I) ≠ 0 := by
    intro h1
    have := congrArg Complex.re h1
    simp at this
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt sqrt_two_pos)) this h0.symm

private lemma w8_bd_ne : w8b ≠ w8d := by
  intro h
  have h0 : w8b - w8d = (Real.sqrt 2 : ℂ) := by
    simp only [w8b, w8d]; ring
  rw [h, sub_self] at h0
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt sqrt_two_pos) h0.symm

private lemma w8_cd_ne : w8c ≠ w8d := by
  intro h
  have h0 : w8c - w8d = (Real.sqrt 2 : ℂ) * Complex.I := by
    simp only [w8c, w8d]; ring
  rw [h, sub_self] at h0
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt sqrt_two_pos))
    Complex.I_ne_zero h0.symm

/-- **`{|Φ₈| < C}` is DISCONNECTED for `0 < C < 1/4`** — the first quartic
component-topology result in the family. -/
theorem not_isPreconnected_levelSet_eight {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 4) :
    ¬ IsPreconnected (Erdos1215.levelSet (cyclotomic 8 ℂ) C) := by
  rw [levelSet_cyclotomic_eight_eq]
  set r := Real.sqrt (Real.sqrt C) with hrdef
  have hsep : 2 * r < Real.sqrt 2 := by
    apply two_sqrt_sqrt_lt hC.le (Real.sqrt_nonneg 2)
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [hC']
  refine not_isPreconnected_quartic_lemniscate hC (Real.sqrt_nonneg _)
    (le_of_eq (sqrt_sqrt_pow_four hC.le).symm)
    w8_ab_ne w8_ac_ne w8_ad_ne w8_bc_ne w8_bd_ne w8_cd_ne ?_ ?_ ?_
  · rw [dist_eq_norm, norm_w8_sub_ab]; exact hsep
  · rw [dist_eq_norm, norm_w8_sub_ac]; exact hsep
  · rw [dist_eq_norm]; exact lt_of_lt_of_le hsep norm_w8_sub_ad

/-- `{|Φ₈| < C}` is not path-connected for `0 < C < 1/4`. -/
theorem not_isPathConnected_levelSet_eight {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 4) :
    ¬ IsPathConnected (Erdos1215.levelSet (cyclotomic 8 ℂ) C) :=
  fun h => not_isPreconnected_levelSet_eight hC hC'
    h.isConnected.isPreconnected

/-! ## `n = 12`: `Φ₁₂ = X⁴ − X² + 1`, roots `(±√3 ± i)/2`, minimal gap `1`

Disconnection for `C < 1/16` (`2·C^{1/4} < 1 ⟺ 16C < 1`). -/

/-- `Φ₁₂ = X⁴ − X² + 1` (absent from Mathlib): from `expand ℂ 2 Φ₆ = Φ₁₂` and
`Φ₆ = X² − X + 1`. -/
theorem cyclotomic_twelve : cyclotomic 12 ℂ = X ^ 4 - X ^ 2 + 1 := by
  have h : Polynomial.expand ℂ 2 (X ^ 2 - X + 1) = cyclotomic 12 ℂ := by
    have h0 := cyclotomic_expand_eq_cyclotomic Nat.prime_two
      (show 2 ∣ 6 by norm_num) ℂ
    rwa [cyclotomic_six] at h0
  rw [← h]
  simp only [map_add, map_sub, map_pow, Polynomial.expand_X, map_one]
  ring

/-- The primitive twelfth root of unity `e^{iπ/6} = (√3 + i)/2`. -/
noncomputable def w12a : ℂ := ((Real.sqrt 3 : ℂ) + Complex.I) / 2

/-- The primitive twelfth root `e^{-iπ/6} = (√3 − i)/2`. -/
noncomputable def w12b : ℂ := ((Real.sqrt 3 : ℂ) - Complex.I) / 2

/-- The primitive twelfth root `e^{5iπ/6} = (−√3 + i)/2`. -/
noncomputable def w12c : ℂ := (-(Real.sqrt 3 : ℂ) + Complex.I) / 2

/-- The primitive twelfth root `e^{7iπ/6} = (−√3 − i)/2`. -/
noncomputable def w12d : ℂ := (-(Real.sqrt 3 : ℂ) - Complex.I) / 2

/-- `Φ₁₂` factors over its four roots. -/
theorem cyclotomic_twelve_eval_factor (z : ℂ) :
    (cyclotomic 12 ℂ).eval z =
      (z - w12a) * (z - w12b) * (z - w12c) * (z - w12d) := by
  rw [cyclotomic_twelve]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one, w12a, w12b, w12c, w12d]
  linear_combination ((z ^ 2 : ℂ) / 2 - ((Real.sqrt 3 : ℂ) ^ 2 - 3) / 16
    + (Complex.I ^ 2 + 1) / 8 - 1 / 2) * ofReal_sqrt_three_sq
    + ((z ^ 2 : ℂ) / 2 + 1 / 2 - (Complex.I ^ 2 + 1) / 16) * Complex.I_sq

/-- The `Φ₁₂` sublevel set in factored form. -/
theorem levelSet_cyclotomic_twelve_eq (C : ℝ) :
    Erdos1215.levelSet (cyclotomic 12 ℂ) C =
      {z : ℂ | ‖(z - w12a) * (z - w12b) * (z - w12c) * (z - w12d)‖ < C} := by
  ext z
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq, cyclotomic_twelve_eval_factor]

private lemma sqrt_three_pos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

/-- `w12a − w12b = i`: the vertical gap (the MINIMAL gap, length `1`). -/
private lemma w12_sub_ab : w12a - w12b = Complex.I := by
  simp only [w12a, w12b]; ring

/-- `w12a − w12c = √3`: the horizontal gap. -/
private lemma w12_sub_ac : w12a - w12c = (Real.sqrt 3 : ℂ) := by
  simp only [w12a, w12c]; ring

/-- `w12a − w12d = √3 + i`: the diagonal gap. -/
private lemma w12_sub_ad : w12a - w12d = (Real.sqrt 3 : ℂ) + Complex.I := by
  simp only [w12a, w12d]; ring

private lemma norm_w12_sub_ab : ‖w12a - w12b‖ = 1 := by
  rw [w12_sub_ab, Complex.norm_I]

private lemma norm_w12_sub_ac : ‖w12a - w12c‖ = Real.sqrt 3 := by
  rw [w12_sub_ac, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 3)]

/-- The diagonal gap is at least `√3` (its real part). -/
private lemma norm_w12_sub_ad : Real.sqrt 3 ≤ ‖w12a - w12d‖ := by
  have hre : (w12a - w12d).re = Real.sqrt 3 := by
    rw [w12_sub_ad]
    simp [Complex.add_re, Complex.I_re, Complex.ofReal_re]
  calc Real.sqrt 3 = (w12a - w12d).re := hre.symm
    _ ≤ |(w12a - w12d).re| := le_abs_self _
    _ ≤ ‖w12a - w12d‖ := Complex.abs_re_le_norm _

private lemma w12_ab_ne : w12a ≠ w12b := by
  intro h
  have h0 := w12_sub_ab
  rw [h, sub_self] at h0
  exact Complex.I_ne_zero h0.symm

private lemma w12_ac_ne : w12a ≠ w12c := by
  intro h
  have h0 := w12_sub_ac
  rw [h, sub_self] at h0
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt sqrt_three_pos) h0.symm

private lemma w12_ad_ne : w12a ≠ w12d := by
  intro h
  have h0 := w12_sub_ad
  rw [h, sub_self] at h0
  have := congrArg Complex.im h0.symm
  simp at this

private lemma w12_bc_ne : w12b ≠ w12c := by
  intro h
  have h0 : w12b - w12c = (Real.sqrt 3 : ℂ) - Complex.I := by
    simp only [w12b, w12c]; ring
  rw [h, sub_self] at h0
  have := congrArg Complex.im h0.symm
  simp at this

private lemma w12_bd_ne : w12b ≠ w12d := by
  intro h
  have h0 : w12b - w12d = (Real.sqrt 3 : ℂ) := by
    simp only [w12b, w12d]; ring
  rw [h, sub_self] at h0
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt sqrt_three_pos) h0.symm

private lemma w12_cd_ne : w12c ≠ w12d := by
  intro h
  have h0 : w12c - w12d = Complex.I := by
    simp only [w12c, w12d]; ring
  rw [h, sub_self] at h0
  exact Complex.I_ne_zero h0.symm

/-- **`{|Φ₁₂| < C}` is DISCONNECTED for `0 < C < 1/16`.**  The minimal root gap
of `Φ₁₂` is `1` (vertical neighbours `(√3 ± i)/2`), so the four `C^{1/4}`-balls
separate exactly when `16C < 1`. -/
theorem not_isPreconnected_levelSet_twelve {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 16) :
    ¬ IsPreconnected (Erdos1215.levelSet (cyclotomic 12 ℂ) C) := by
  rw [levelSet_cyclotomic_twelve_eq]
  set r := Real.sqrt (Real.sqrt C) with hrdef
  have hsep1 : 2 * r < 1 := by
    apply two_sqrt_sqrt_lt hC.le zero_le_one
    nlinarith [hC']
  have hsep3 : 2 * r < Real.sqrt 3 := by
    have h13 : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  refine not_isPreconnected_quartic_lemniscate hC (Real.sqrt_nonneg _)
    (le_of_eq (sqrt_sqrt_pow_four hC.le).symm)
    w12_ab_ne w12_ac_ne w12_ad_ne w12_bc_ne w12_bd_ne w12_cd_ne ?_ ?_ ?_
  · rw [dist_eq_norm, norm_w12_sub_ab]; exact hsep1
  · rw [dist_eq_norm, norm_w12_sub_ac]; exact hsep3
  · rw [dist_eq_norm]; exact lt_of_lt_of_le hsep3 norm_w12_sub_ad

/-- `{|Φ₁₂| < C}` is not path-connected for `0 < C < 1/16`. -/
theorem not_isPathConnected_levelSet_twelve {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 16) :
    ¬ IsPathConnected (Erdos1215.levelSet (cyclotomic 12 ℂ) C) :=
  fun h => not_isPreconnected_levelSet_twelve hC hC'
    h.isConnected.isPreconnected

#check @lemniscate_subset_biUnion
#check @not_isPreconnected_lemniscate
#check @not_isPreconnected_quartic_lemniscate
#check @cyclotomic_eight
#check @cyclotomic_twelve
#check @not_isPreconnected_levelSet_eight
#check @not_isPreconnected_levelSet_twelve

end CyclotomicPolynomialsOQ02OQ13
