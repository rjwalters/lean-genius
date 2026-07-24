/-
# Erdős #1215 (cyclotomic sub-question, OQ02) — small-C DISCONNECTION of the
# QUARTIC cyclotomic lemniscates: the `φ(n) = 4` layer CLOSES (n = 5, 8, 10, 12)

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
  > with `φ(n) = 4`, and ALL FOUR are delivered:
  > * `{|Φ₈| < C}` DISCONNECTED for `0 < C < 1/4`
  >   (roots `(±√2 ± √2·i)/2`, minimal root gap `√2`);
  > * `{|Φ₁₂| < C}` DISCONNECTED for `0 < C < 1/16`
  >   (roots `(±√3 ± i)/2`, minimal root gap `1`);
  > * `{|Φ₅| < C}` and `{|Φ₁₀| < C}` DISCONNECTED for `0 < C < 1/16`
  >   (nested-radical roots; the gap bounds need only real parts, clean in
  >   `√5`, plus `2·sin 72° ≥ 1` from its square — no unnesting);
  > * uniformly: `not_isPreconnected_levelSet_quartic` — every `φ(n) = 4`
  >   lemniscate is disconnected for `0 < C < 1/16`.
  > Byproducts: `cyclotomic 5/8/10/12 ℂ` in explicit polynomial form (8, 10,
  > 12 absent from Mathlib), via `cyclotomic_prime`,
  > `cyclotomic_expand_eq_cyclotomic(_mul)` from `Φ₄ = X² + 1` (OQ11) and `Φ₆`.

  Exact component counts (four petals) need the OQ12 star-shaped template at
  four foci — a follow-up, not attempted here. Sextic layer `φ(n) = 6` is
  engine-ready.

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

/-! ## `n = 5, 10`: the nested-radical quartics — the `φ(n) = 4` layer CLOSES

`Φ₅ = X⁴+X³+X²+X+1` has roots `cos(2πk/5) ± i·sin(2πk/5)` (`k = 1, 2`), with
`cos 72° = (√5−1)/4`, `cos 144° = −(√5+1)/4` and the NESTED radicals
`sin 72° = √(10+2√5)/4`, `sin 36° = √(10−2√5)/4`. The key observation that
keeps this session-sized: the root-GAP lower bounds need only the *real
parts* of the differences (clean in `√5`) and the conjugate-pair gap
`2·sin 72° ≥ 1` (from its square `(10+2√5)/4 ≥ 1`) — the nested radicals
never need to be unnested. `Φ₁₀(X) = Φ₅(−X)`, so its roots are the negatives
and every bound mirrors. Uniform regime: `0 < C < 1/16` disconnects BOTH
(gaps `≥ 1 > 2·C^{1/4}`), matching the `Φ₁₂` threshold. -/

/-- `(√5 : ℂ)² = 5`. -/
private lemma ofReal_sqrt_five_sq : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private lemma sqrt_five_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

private lemma sqrt_five_lt_five : Real.sqrt 5 < 5 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

private lemma two_le_sqrt_five : (2 : ℝ) ≤ Real.sqrt 5 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

/-- `4·sin 72°` as a real surd. -/
noncomputable def sin72x4 : ℝ := Real.sqrt (10 + 2 * Real.sqrt 5)

/-- `4·sin 36°` as a real surd. -/
noncomputable def sin36x4 : ℝ := Real.sqrt (10 - 2 * Real.sqrt 5)

private lemma sin72x4_sq : sin72x4 ^ 2 = 10 + 2 * Real.sqrt 5 :=
  Real.sq_sqrt (by positivity)

private lemma sin36x4_sq : sin36x4 ^ 2 = 10 - 2 * Real.sqrt 5 :=
  Real.sq_sqrt (by nlinarith [sqrt_five_lt_five])

private lemma sin72x4_pos : 0 < sin72x4 :=
  Real.sqrt_pos.mpr (by positivity)

private lemma sin36x4_pos : 0 < sin36x4 :=
  Real.sqrt_pos.mpr (by nlinarith [sqrt_five_lt_five])

/-- The conjugate-pair gap of `Φ₅` is at least `2`: `(4·sin 72°)² ≥ 10 > 4`. -/
private lemma two_le_sin72x4 : (2 : ℝ) ≤ sin72x4 := by
  nlinarith [sin72x4_sq, sin72x4_pos.le, Real.sqrt_nonneg 5]

/-- Complexified square identity for `4·sin 72°`. -/
private lemma ofReal_sin72x4_sq :
    (sin72x4 : ℂ) ^ 2 = 10 + 2 * (Real.sqrt 5 : ℂ) := by
  rw [show ((sin72x4 : ℝ) : ℂ) ^ 2 = ((sin72x4 ^ 2 : ℝ) : ℂ) by push_cast; ring,
    sin72x4_sq]
  push_cast
  ring

/-- Complexified square identity for `4·sin 36°`. -/
private lemma ofReal_sin36x4_sq :
    (sin36x4 : ℂ) ^ 2 = 10 - 2 * (Real.sqrt 5 : ℂ) := by
  rw [show ((sin36x4 : ℝ) : ℂ) ^ 2 = ((sin36x4 ^ 2 : ℝ) : ℂ) by push_cast; ring,
    sin36x4_sq]
  push_cast
  ring

/-- The primitive fifth root of unity `e^{2πi/5} = (√5−1)/4 + i·sin 72°`. -/
noncomputable def w5a : ℂ := ((Real.sqrt 5 : ℂ) - 1) / 4 + (sin72x4 : ℂ) / 4 * Complex.I

/-- The primitive fifth root `e^{-2πi/5}`. -/
noncomputable def w5b : ℂ := ((Real.sqrt 5 : ℂ) - 1) / 4 - (sin72x4 : ℂ) / 4 * Complex.I

/-- The primitive fifth root `e^{4πi/5} = −(√5+1)/4 + i·sin 36°`. -/
noncomputable def w5c : ℂ := -((Real.sqrt 5 : ℂ) + 1) / 4 + (sin36x4 : ℂ) / 4 * Complex.I

/-- The primitive fifth root `e^{-4πi/5}`. -/
noncomputable def w5d : ℂ := -((Real.sqrt 5 : ℂ) + 1) / 4 - (sin36x4 : ℂ) / 4 * Complex.I

/-- `Φ₅ = X⁴+X³+X²+X+1` in explicit form (`cyclotomic_prime` for `p = 5`). -/
theorem cyclotomic_five : cyclotomic 5 ℂ = X ^ 4 + X ^ 3 + X ^ 2 + X + 1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Polynomial.cyclotomic_prime]
  simp [Finset.sum_range_succ]
  ring

/-- The outer conjugate pair of `Φ₅` multiplies to `z² − ((√5−1)/2)z + 1`. -/
private lemma pair5_outer (z : ℂ) :
    (z - w5a) * (z - w5b) =
      z ^ 2 - ((Real.sqrt 5 : ℂ) - 1) / 2 * z + 1 := by
  simp only [w5a, w5b]
  linear_combination (1 / 16 : ℂ) * ofReal_sqrt_five_sq
    + (1 / 16 : ℂ) * ofReal_sin72x4_sq
    - ((sin72x4 : ℂ) / 4) ^ 2 * Complex.I_sq

/-- The inner conjugate pair of `Φ₅` multiplies to `z² + ((√5+1)/2)z + 1`. -/
private lemma pair5_inner (z : ℂ) :
    (z - w5c) * (z - w5d) =
      z ^ 2 + ((Real.sqrt 5 : ℂ) + 1) / 2 * z + 1 := by
  simp only [w5c, w5d]
  linear_combination (1 / 16 : ℂ) * ofReal_sqrt_five_sq
    + (1 / 16 : ℂ) * ofReal_sin36x4_sq
    - ((sin36x4 : ℂ) / 4) ^ 2 * Complex.I_sq

/-- The two quadratic factors multiply to `Φ₅`. -/
private lemma quad5 (z : ℂ) :
    (z ^ 2 - ((Real.sqrt 5 : ℂ) - 1) / 2 * z + 1) *
      (z ^ 2 + ((Real.sqrt 5 : ℂ) + 1) / 2 * z + 1) =
      z ^ 4 + z ^ 3 + z ^ 2 + z + 1 := by
  linear_combination (-(z ^ 2) / 4) * ofReal_sqrt_five_sq

/-- `Φ₅` factors over its four roots. -/
theorem cyclotomic_five_eval_factor (z : ℂ) :
    (cyclotomic 5 ℂ).eval z = (z - w5a) * (z - w5b) * (z - w5c) * (z - w5d) := by
  rw [cyclotomic_five]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  linear_combination (-1 : ℂ) * quad5 z
    - ((z - w5c) * (z - w5d)) * pair5_outer z
    - (z ^ 2 - ((Real.sqrt 5 : ℂ) - 1) / 2 * z + 1) * pair5_inner z

/-- The `Φ₅` sublevel set in factored form. -/
theorem levelSet_cyclotomic_five_eq (C : ℝ) :
    Erdos1215.levelSet (cyclotomic 5 ℂ) C =
      {z : ℂ | ‖(z - w5a) * (z - w5b) * (z - w5c) * (z - w5d)‖ < C} := by
  ext z
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq, cyclotomic_five_eval_factor]

/-! Gap lemmas for `Φ₅`: the three gaps from `w5a` are the vertical conjugate
gap `2·sin 72° ≥ 2·C^{1/4}⁻¹-free bound `≥ 1`` and the two cross-pair gaps
with real part `√5/2 ≥ 1`. -/

private lemma w5_sub_ab :
    w5a - w5b = ((sin72x4 / 2 : ℝ) : ℂ) * Complex.I := by
  simp only [w5a, w5b]
  push_cast
  ring

private lemma w5_sub_ac :
    w5a - w5c = ((Real.sqrt 5 / 2 : ℝ) : ℂ) +
      (((sin72x4 - sin36x4) / 4 : ℝ) : ℂ) * Complex.I := by
  simp only [w5a, w5c]
  push_cast
  ring

private lemma w5_sub_ad :
    w5a - w5d = ((Real.sqrt 5 / 2 : ℝ) : ℂ) +
      (((sin72x4 + sin36x4) / 4 : ℝ) : ℂ) * Complex.I := by
  simp only [w5a, w5d]
  push_cast
  ring

private lemma norm_w5_sub_ab : ‖w5a - w5b‖ = sin72x4 / 2 := by
  rw [w5_sub_ab, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by linarith [sin72x4_pos] : (0:ℝ) ≤ sin72x4 / 2)]

/-- Real part of a `(a : ℂ) + (b : ℂ)·I` combination. -/
private lemma re_ofReal_add_ofReal_mul_I (a b : ℝ) :
    (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I).re = a := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]

private lemma norm_w5_sub_ac : Real.sqrt 5 / 2 ≤ ‖w5a - w5c‖ := by
  calc Real.sqrt 5 / 2
      = (w5a - w5c).re := by rw [w5_sub_ac, re_ofReal_add_ofReal_mul_I]
    _ ≤ |(w5a - w5c).re| := le_abs_self _
    _ ≤ ‖w5a - w5c‖ := Complex.abs_re_le_norm _

private lemma norm_w5_sub_ad : Real.sqrt 5 / 2 ≤ ‖w5a - w5d‖ := by
  calc Real.sqrt 5 / 2
      = (w5a - w5d).re := by rw [w5_sub_ad, re_ofReal_add_ofReal_mul_I]
    _ ≤ |(w5a - w5d).re| := le_abs_self _
    _ ≤ ‖w5a - w5d‖ := Complex.abs_re_le_norm _

/-- Distinctness of the four `Φ₅` roots, via imaginary or real parts. -/
private lemma w5_ab_ne : w5a ≠ w5b := by
  intro h
  have h0 := w5_sub_ab
  rw [h, sub_self] at h0
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (div_pos sin72x4_pos (by norm_num)).ne')
    Complex.I_ne_zero h0.symm

private lemma re_ne_of_sub {u v : ℂ} (a b : ℝ) (ha : 0 < a)
    (h0 : u - v = ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I) : u ≠ v := by
  intro h
  rw [h, sub_self] at h0
  have hre := congrArg Complex.re h0.symm
  rw [re_ofReal_add_ofReal_mul_I, Complex.zero_re] at hre
  exact absurd hre (ne_of_gt ha)

private lemma w5_ac_ne : w5a ≠ w5c :=
  re_ne_of_sub _ _ (by positivity) w5_sub_ac

private lemma w5_ad_ne : w5a ≠ w5d :=
  re_ne_of_sub _ _ (by positivity) w5_sub_ad

private lemma w5_bc_ne : w5b ≠ w5c := by
  refine re_ne_of_sub (Real.sqrt 5 / 2) (-(sin72x4 + sin36x4) / 4)
    (by positivity) ?_
  simp only [w5b, w5c]
  push_cast
  ring

private lemma w5_bd_ne : w5b ≠ w5d := by
  refine re_ne_of_sub (Real.sqrt 5 / 2) (-(sin72x4 - sin36x4) / 4)
    (by positivity) ?_
  simp only [w5b, w5d]
  push_cast
  ring

private lemma w5_cd_ne : w5c ≠ w5d := by
  intro h
  have h0 : w5c - w5d = ((sin36x4 / 2 : ℝ) : ℂ) * Complex.I := by
    simp only [w5c, w5d]
    push_cast
    ring
  rw [h, sub_self] at h0
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (div_pos sin36x4_pos (by norm_num)).ne')
    Complex.I_ne_zero h0.symm

/-- **`{|Φ₅| < C}` is DISCONNECTED for `0 < C < 1/16`** — the first
nested-radical quartic. All three gaps from `e^{2πi/5}` are `≥ 1`:
the conjugate gap is `2·sin 72° ≥ 1` and the cross-pair gaps have real part
`√5/2 ≥ 1`. -/
theorem not_isPreconnected_levelSet_five {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 16) :
    ¬ IsPreconnected (Erdos1215.levelSet (cyclotomic 5 ℂ) C) := by
  rw [levelSet_cyclotomic_five_eq]
  set r := Real.sqrt (Real.sqrt C) with hrdef
  have hsep1 : 2 * r < 1 := by
    apply two_sqrt_sqrt_lt hC.le zero_le_one
    nlinarith [hC']
  have hgap_ab : (1 : ℝ) ≤ sin72x4 / 2 := by
    nlinarith [two_le_sin72x4]
  have hgap_cross : (1 : ℝ) ≤ Real.sqrt 5 / 2 := by
    nlinarith [two_le_sqrt_five]
  refine not_isPreconnected_quartic_lemniscate hC (Real.sqrt_nonneg _)
    (le_of_eq (sqrt_sqrt_pow_four hC.le).symm)
    w5_ab_ne w5_ac_ne w5_ad_ne w5_bc_ne w5_bd_ne w5_cd_ne ?_ ?_ ?_
  · rw [dist_eq_norm, norm_w5_sub_ab]
    linarith
  · rw [dist_eq_norm]
    have := norm_w5_sub_ac
    linarith
  · rw [dist_eq_norm]
    have := norm_w5_sub_ad
    linarith

/-- `{|Φ₅| < C}` is not path-connected for `0 < C < 1/16`. -/
theorem not_isPathConnected_levelSet_five {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 16) :
    ¬ IsPathConnected (Erdos1215.levelSet (cyclotomic 5 ℂ) C) :=
  fun h => not_isPreconnected_levelSet_five hC hC' h.isConnected.isPreconnected

/-! ### `n = 10`: `Φ₁₀(X) = Φ₅(−X)`, roots the negatives of the `Φ₅` roots -/

/-- `Φ₁₀ = X⁴−X³+X²−X+1`: from `expand ℂ 2 Φ₅ = Φ₁₀·Φ₅` (`2 ∤ 5`) by
cancelling the (nonzero) factor `Φ₅`. -/
theorem cyclotomic_ten : cyclotomic 10 ℂ = X ^ 4 - X ^ 3 + X ^ 2 - X + 1 := by
  have key := cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two
    (show ¬ (2 ∣ 5) by norm_num) ℂ (n := 5)
  have h5ne : cyclotomic 5 ℂ ≠ 0 := cyclotomic_ne_zero 5 ℂ
  apply mul_right_cancel₀ h5ne
  rw [← key, cyclotomic_five]
  simp only [map_add, map_pow, Polynomial.expand_X, map_one]
  ring

/-- The primitive tenth root `−e^{2πi/5} = e^{7πi/5}`… the four roots of
`Φ₁₀` are exactly the negatives of the `Φ₅` roots. -/
noncomputable def w10a : ℂ := -w5a

/-- Negated `Φ₅` root. -/
noncomputable def w10b : ℂ := -w5b

/-- Negated `Φ₅` root. -/
noncomputable def w10c : ℂ := -w5c

/-- Negated `Φ₅` root. -/
noncomputable def w10d : ℂ := -w5d

/-- `Φ₁₀` factors over the negated `Φ₅` roots: `Φ₁₀(z) = Φ₅(−z)`. -/
theorem cyclotomic_ten_eval_factor (z : ℂ) :
    (cyclotomic 10 ℂ).eval z =
      (z - w10a) * (z - w10b) * (z - w10c) * (z - w10d) := by
  rw [cyclotomic_ten]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one,
    w10a, w10b, w10c, w10d]
  have h := cyclotomic_five_eval_factor (-z)
  rw [cyclotomic_five] at h
  simp only [eval_add, eval_pow, eval_X, eval_one] at h
  linear_combination h

/-- The `Φ₁₀` sublevel set in factored form. -/
theorem levelSet_cyclotomic_ten_eq (C : ℝ) :
    Erdos1215.levelSet (cyclotomic 10 ℂ) C =
      {z : ℂ | ‖(z - w10a) * (z - w10b) * (z - w10c) * (z - w10d)‖ < C} := by
  ext z
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq, cyclotomic_ten_eval_factor]

/-- Negation is an isometry: all `Φ₁₀` gap bounds mirror the `Φ₅` ones. -/
private lemma norm_neg_sub_neg (u v : ℂ) : ‖-u - -v‖ = ‖u - v‖ := by
  rw [show -u - -v = -(u - v) by ring, norm_neg]

/-- **`{|Φ₁₀| < C}` is DISCONNECTED for `0 < C < 1/16`** — with this the
quartic layer `φ(n) = 4` (`n = 5, 8, 10, 12`) is complete. -/
theorem not_isPreconnected_levelSet_ten {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 16) :
    ¬ IsPreconnected (Erdos1215.levelSet (cyclotomic 10 ℂ) C) := by
  rw [levelSet_cyclotomic_ten_eq]
  set r := Real.sqrt (Real.sqrt C) with hrdef
  have hsep1 : 2 * r < 1 := by
    apply two_sqrt_sqrt_lt hC.le zero_le_one
    nlinarith [hC']
  have hgap_ab : (1 : ℝ) ≤ sin72x4 / 2 := by
    nlinarith [two_le_sin72x4]
  have hgap_cross : (1 : ℝ) ≤ Real.sqrt 5 / 2 := by
    nlinarith [two_le_sqrt_five]
  have hnorm_ab : ‖w10a - w10b‖ = sin72x4 / 2 := by
    rw [w10a, w10b, norm_neg_sub_neg, norm_w5_sub_ab]
  have hnorm_ac : Real.sqrt 5 / 2 ≤ ‖w10a - w10c‖ := by
    rw [w10a, w10c, norm_neg_sub_neg]
    exact norm_w5_sub_ac
  have hnorm_ad : Real.sqrt 5 / 2 ≤ ‖w10a - w10d‖ := by
    rw [w10a, w10d, norm_neg_sub_neg]
    exact norm_w5_sub_ad
  refine not_isPreconnected_quartic_lemniscate hC (Real.sqrt_nonneg _)
    (le_of_eq (sqrt_sqrt_pow_four hC.le).symm)
    (fun h => w5_ab_ne (neg_injective h))
    (fun h => w5_ac_ne (neg_injective h))
    (fun h => w5_ad_ne (neg_injective h))
    (fun h => w5_bc_ne (neg_injective h))
    (fun h => w5_bd_ne (neg_injective h))
    (fun h => w5_cd_ne (neg_injective h)) ?_ ?_ ?_
  · rw [dist_eq_norm, hnorm_ab]
    linarith
  · rw [dist_eq_norm]
    linarith
  · rw [dist_eq_norm]
    linarith

/-- `{|Φ₁₀| < C}` is not path-connected for `0 < C < 1/16`. -/
theorem not_isPathConnected_levelSet_ten {C : ℝ} (hC : 0 < C) (hC' : C < 1 / 16) :
    ¬ IsPathConnected (Erdos1215.levelSet (cyclotomic 10 ℂ) C) :=
  fun h => not_isPreconnected_levelSet_ten hC hC' h.isConnected.isPreconnected

/-! ### The uniform quartic statement -/

/-- **The quartic layer, uniformly**: for every `n` with `φ(n) = 4` — that is
`n ∈ {5, 8, 10, 12}` — the cyclotomic lemniscate `{|Φₙ| < C}` is disconnected
for all `0 < C < 1/16`. (For `n = 8` the individual threshold `1/4` is wider;
`1/16` is the uniform one, tight at `n = 12`, whose minimal root gap `1` is
the smallest in the layer.) -/
theorem not_isPreconnected_levelSet_quartic {C : ℝ} (hC : 0 < C)
    (hC' : C < 1 / 16) :
    ∀ n ∈ ({5, 8, 10, 12} : Finset ℕ),
      ¬ IsPreconnected (Erdos1215.levelSet (cyclotomic n ℂ) C) := by
  intro n hn
  fin_cases hn
  · exact not_isPreconnected_levelSet_five hC hC'
  · exact not_isPreconnected_levelSet_eight hC (by linarith)
  · exact not_isPreconnected_levelSet_ten hC hC'
  · exact not_isPreconnected_levelSet_twelve hC hC'

#check @lemniscate_subset_biUnion
#check @not_isPreconnected_lemniscate
#check @not_isPreconnected_quartic_lemniscate
#check @cyclotomic_eight
#check @cyclotomic_twelve
#check @not_isPreconnected_levelSet_eight
#check @not_isPreconnected_levelSet_twelve
#check @cyclotomic_five
#check @cyclotomic_ten
#check @not_isPreconnected_levelSet_five
#check @not_isPreconnected_levelSet_ten
#check @not_isPreconnected_levelSet_quartic

end CyclotomicPolynomialsOQ02OQ13
