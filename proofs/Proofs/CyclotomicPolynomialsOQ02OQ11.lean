/-
# Erdős #1215 (cyclotomic sub-question, OQ02) — small-C DISCONNECTION of the
# quadratic cyclotomic lemniscates (n = 3, 4, 6)

  Slug: erdos-1215-oq-02
  Prior work (this OQ family):
    * OQ02OQ01  — boundedness/openness of `{|Φ_n| < C}`; exact open disks for n = 1, 2.
    * OQ02OQ02–07 — sharp two-sided radius/area sandwich, origin interiority (C > 1).
    * OQ02OQ08  — radial exit path; OQ02OQ09 — path-connected far field;
    * OQ02OQ10  — first-crossing exit in EVERY direction, sharp two-sided bound.

  ## This file — the FIRST component-topology result for the family

  All previous OQ02 layers pinned the *shape* of the sublevel set
  `{z : |Φ_n(z)| < C}` (radius/area sandwich) or produced *positive* path results
  (every ray exits quickly).  The recorded blocked driver — every-boundary-point
  reachability — needs the *component structure* of the cyclotomic lemniscate,
  and the recorded tractable layer is explicit small-`n` geometry.  This file
  delivers that layer for the complete QUADRATIC case: `n = 3, 4, 6` are exactly
  the indices with `φ(n) = 2` (`Φ₃ = X²+X+1`, `Φ₄ = X²+1`, `Φ₆ = X²−X+1`), whose
  lemniscates are Cassini ovals with foci at the two primitive roots `a, b`.

  > **Main result.**  For `4C < |a − b|²` the sublevel set `{|Φ_n| < C}` is
  > NOT preconnected (hence not connected, hence not path-connected): it splits
  > into two nonempty "petals" inside the disjoint balls `B(a, √C)`, `B(b, √C)`.
  > Concretely: `{|Φ₃| < C}` and `{|Φ₆| < C}` are disconnected for `0 < C < 3/4`
  > (foci `√3` apart), and `{|Φ₄| < C}` is disconnected for `0 < C < 1`
  > (foci `2` apart).

  The engine is a single general Cassini-oval criterion
  (`not_isPreconnected_quadratic_lemniscate`): if every point of
  `{|z−a||z−b| < C}` were at distance `≥ √C` from both foci the product would be
  `≥ C`, so the set is covered by the two open balls `B(a, √C) ∪ B(b, √C)`; when
  `2√C < |a−b|` these balls are disjoint, each contains a focus (a root of the
  polynomial), and `IsPreconnected` applied to this open cover yields a point of
  the empty intersection — contradiction.

  ## Perspective within the family

  * For `n = 1, 2` (`φ(n) = 1`) the sublevel sets are exact open disks
    (`OQ02OQ01.sublevel_one/two`) — always connected.  Disconnection therefore
    first appears exactly at degree `φ(n) = 2`, and this file pins the regime.
  * The disconnection regime `C < 3/4` (resp. `< 1`) and the origin-interior
    regime `C > 1` (OQ02OQ07: `|Φ_n(0)| = 1`, so `0 ∈ {|Φ_n| < C}` iff `C > 1`)
    are disjoint — consistent with the classical Cassini picture, where the oval
    with foci `a, b` is a single connected curve iff `C ≥ (|a−b|/2)²`.
  * Sharpness (the sets ARE connected for `C ≥ (|a−b|/2)²`) and the exact
    component count (each petal is connected, so exactly two) are the natural
    follow-ups; both need per-petal connectivity arguments not attempted here.

  Byproduct: `cyclotomic 4 ℂ = X² + 1` is absent from Mathlib (which has
  `cyclotomic_one/_two/_three/_six`); proved here via
  `cyclotomic_expand_eq_cyclotomic` from `Φ₂ = X + 1` (`cyclotomic_four`).

  Result status: 0 sorries, 0 axioms, no `native_decide` — axiom-free relative
  to Mathlib.  The deep `maclane_labyrinth` axiom of the parent is untouched.
-/
import Mathlib
import Proofs.Erdos1215Problem

open Complex Polynomial Metric

namespace CyclotomicPolynomialsOQ02OQ11

/-! ## The general Cassini-oval disconnection engine

For `a b : ℂ` and threshold `C`, the quadratic lemniscate `{z : ‖(z−a)(z−b)‖ < C}`
is covered by the two balls of radius `√C` around the foci; when `4C < ‖a−b‖²`
those balls are disjoint and each contains a focus, so the set is disconnected. -/

/-- **Covering lemma**: every point of the quadratic lemniscate is within `√C`
of one of the two foci — otherwise both factors are `≥ √C` and the product is `≥ C`. -/
theorem quadratic_lemniscate_subset_union (a b : ℂ) {C : ℝ} (hC : 0 ≤ C) :
    {z : ℂ | ‖(z - a) * (z - b)‖ < C} ⊆
      Metric.ball a (Real.sqrt C) ∪ Metric.ball b (Real.sqrt C) := by
  intro z hz
  rw [Set.mem_setOf_eq, norm_mul] at hz
  by_contra hcon
  simp only [Set.mem_union, Metric.mem_ball, dist_eq_norm] at hcon
  push Not at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hmul : Real.sqrt C * Real.sqrt C ≤ ‖z - a‖ * ‖z - b‖ :=
    mul_le_mul ha hb (Real.sqrt_nonneg C) (norm_nonneg _)
  rw [Real.mul_self_sqrt hC] at hmul
  linarith

/-- **Separation lemma**: when `4C < ‖a − b‖²` the two focal balls of radius `√C`
are disjoint (triangle inequality + squaring). -/
theorem sqrt_balls_disjoint {a b : ℂ} {C : ℝ} (hC : 0 < C)
    (hsep : 4 * C < ‖a - b‖ ^ 2) :
    Metric.ball a (Real.sqrt C) ∩ Metric.ball b (Real.sqrt C) = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Metric.mem_ball, dist_eq_norm, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro hza hzb
  have htri : ‖a - b‖ ≤ ‖z - a‖ + ‖z - b‖ := by
    have h := dist_triangle a z b
    rw [dist_comm a z] at h
    simpa [dist_eq_norm] using h
  have h1 : ‖a - b‖ < 2 * Real.sqrt C := by linarith
  have h2 : ‖a - b‖ * ‖a - b‖ < (2 * Real.sqrt C) * (2 * Real.sqrt C) :=
    mul_self_lt_mul_self (norm_nonneg _) h1
  have h3 : (2 * Real.sqrt C) * (2 * Real.sqrt C) = 4 * C := by
    have := Real.mul_self_sqrt hC.le
    nlinarith [this]
  nlinarith [h2, h3, hsep]

/-- **Cassini disconnection criterion**: for `0 < C` with `4C < ‖a − b‖²`, the
quadratic lemniscate `{z : ‖(z−a)(z−b)‖ < C}` is not preconnected — the two
focal balls form an open cover by disjoint sets each meeting the lemniscate
(at its focus, a root of the polynomial). -/
theorem not_isPreconnected_quadratic_lemniscate {a b : ℂ} {C : ℝ} (hC : 0 < C)
    (hsep : 4 * C < ‖a - b‖ ^ 2) :
    ¬ IsPreconnected {z : ℂ | ‖(z - a) * (z - b)‖ < C} := by
  intro hpre
  have hmema : a ∈ {z : ℂ | ‖(z - a) * (z - b)‖ < C} := by
    simp only [Set.mem_setOf_eq, sub_self, zero_mul, norm_zero]
    exact hC
  have hmemb : b ∈ {z : ℂ | ‖(z - a) * (z - b)‖ < C} := by
    simp only [Set.mem_setOf_eq, sub_self, mul_zero, norm_zero]
    exact hC
  have hballa : a ∈ Metric.ball a (Real.sqrt C) :=
    Metric.mem_ball_self (Real.sqrt_pos.mpr hC)
  have hballb : b ∈ Metric.ball b (Real.sqrt C) :=
    Metric.mem_ball_self (Real.sqrt_pos.mpr hC)
  obtain ⟨z, _, hz⟩ := hpre (Metric.ball a (Real.sqrt C)) (Metric.ball b (Real.sqrt C))
    Metric.isOpen_ball Metric.isOpen_ball
    (quadratic_lemniscate_subset_union a b hC.le)
    ⟨a, hmema, hballa⟩ ⟨b, hmemb, hballb⟩
  have hdisj := sqrt_balls_disjoint hC hsep
  rw [Set.eq_empty_iff_forall_not_mem] at hdisj
  exact hdisj z hz

/-- The quadratic lemniscate is not connected in the separated regime. -/
theorem not_isConnected_quadratic_lemniscate {a b : ℂ} {C : ℝ} (hC : 0 < C)
    (hsep : 4 * C < ‖a - b‖ ^ 2) :
    ¬ IsConnected {z : ℂ | ‖(z - a) * (z - b)‖ < C} :=
  fun h => not_isPreconnected_quadratic_lemniscate hC hsep h.isPreconnected

/-- The quadratic lemniscate is not path-connected in the separated regime. -/
theorem not_isPathConnected_quadratic_lemniscate {a b : ℂ} {C : ℝ} (hC : 0 < C)
    (hsep : 4 * C < ‖a - b‖ ^ 2) :
    ¬ IsPathConnected {z : ℂ | ‖(z - a) * (z - b)‖ < C} :=
  fun h => not_isConnected_quadratic_lemniscate hC hsep h.isConnected

/-! ## Shared surd fact -/

/-- `(√3 : ℂ)² = 3`, the complexified square identity used for the `n = 3, 6` foci. -/
private lemma ofReal_sqrt_three_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-! ## `n = 3`: `Φ₃ = X² + X + 1`, foci at the primitive cube roots of unity

`ω = (−1 + √3·i)/2` and its conjugate, `√3` apart: disconnection for `C < 3/4`. -/

/-- The primitive cube root of unity `ω = (−1 + √3·i)/2`. -/
noncomputable def omega3 : ℂ := (-1 + Real.sqrt 3 * Complex.I) / 2

/-- The conjugate primitive cube root of unity `ω̄ = (−1 − √3·i)/2`. -/
noncomputable def omega3' : ℂ := (-1 - Real.sqrt 3 * Complex.I) / 2

private lemma omega3_add : omega3 + omega3' = -1 := by
  simp only [omega3, omega3']; ring

private lemma omega3_mul : omega3 * omega3' = 1 := by
  simp only [omega3, omega3']
  linear_combination (-(Complex.I ^ 2) / 4) * ofReal_sqrt_three_sq
    - (3 / 4 : ℂ) * Complex.I_sq

/-- `Φ₃` factors over its two roots: `Φ₃(z) = (z − ω)(z − ω̄)`. -/
theorem cyclotomic_three_eval_factor (z : ℂ) :
    (cyclotomic 3 ℂ).eval z = (z - omega3) * (z - omega3') := by
  rw [cyclotomic_three]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  linear_combination z * omega3_add - omega3_mul

/-- The foci of `Φ₃` are `√3` apart: `‖ω − ω̄‖² = 3`. -/
theorem norm_omega3_sub_sq : ‖omega3 - omega3'‖ ^ 2 = 3 := by
  have h : omega3 - omega3' = (Real.sqrt 3 : ℂ) * Complex.I := by
    simp only [omega3, omega3']; ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3)]
  exact Real.sq_sqrt (by norm_num)

/-- The `Φ₃` sublevel set in factored (Cassini) form. -/
theorem levelSet_cyclotomic_three_eq (C : ℝ) :
    Erdos1215.levelSet (cyclotomic 3 ℂ) C =
      {z : ℂ | ‖(z - omega3) * (z - omega3')‖ < C} := by
  ext z
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq, cyclotomic_three_eval_factor]

/-- **`{|Φ₃| < C}` is DISCONNECTED for `0 < C < 3/4`** — the first
component-topology result for a cyclotomic lemniscate in this family. -/
theorem not_isPreconnected_levelSet_three {C : ℝ} (hC : 0 < C) (hC' : C < 3 / 4) :
    ¬ IsPreconnected (Erdos1215.levelSet (cyclotomic 3 ℂ) C) := by
  rw [levelSet_cyclotomic_three_eq]
  exact not_isPreconnected_quadratic_lemniscate hC
    (by rw [norm_omega3_sub_sq]; linarith)

/-- `{|Φ₃| < C}` is not path-connected for `0 < C < 3/4`. -/
theorem not_isPathConnected_levelSet_three {C : ℝ} (hC : 0 < C) (hC' : C < 3 / 4) :
    ¬ IsPathConnected (Erdos1215.levelSet (cyclotomic 3 ℂ) C) := by
  rw [levelSet_cyclotomic_three_eq]
  exact not_isPathConnected_quadratic_lemniscate hC
    (by rw [norm_omega3_sub_sq]; linarith)

/-! ## `n = 4`: `Φ₄ = X² + 1`, foci at `± i`, `2` apart: disconnection for `C < 1`

`cyclotomic 4` has no explicit form in Mathlib — proved here by expanding
`Φ₂ = X + 1` along the prime `2` (`Φ₄(X) = Φ₂(X²)`). -/

/-- `Φ₄ = X² + 1` (absent from Mathlib, which stops at `cyclotomic_three` /
`cyclotomic_six`): from `expand ℂ 2 Φ₂ = Φ₄`. -/
theorem cyclotomic_four : cyclotomic 4 ℂ = X ^ 2 + 1 := by
  have h := cyclotomic_expand_eq_cyclotomic Nat.prime_two (dvd_refl 2) ℂ
  norm_num at h
  rw [← h, cyclotomic_two, map_add, expand_X, map_one]

/-- `Φ₄` factors over its two roots: `Φ₄(z) = (z − i)(z + i)`. -/
theorem cyclotomic_four_eval_factor (z : ℂ) :
    (cyclotomic 4 ℂ).eval z = (z - Complex.I) * (z - -Complex.I) := by
  rw [cyclotomic_four]
  simp only [eval_add, eval_pow, eval_X, eval_one]
  linear_combination Complex.I_sq

/-- The foci of `Φ₄` are `2` apart: `‖i − (−i)‖² = 4`. -/
theorem norm_I_sub_neg_I_sq : ‖Complex.I - -Complex.I‖ ^ 2 = 4 := by
  have h : Complex.I - -Complex.I = (2 : ℂ) * Complex.I := by ring
  rw [h, norm_mul, Complex.norm_I, mul_one]
  norm_num

/-- The `Φ₄` sublevel set in factored (Cassini) form. -/
theorem levelSet_cyclotomic_four_eq (C : ℝ) :
    Erdos1215.levelSet (cyclotomic 4 ℂ) C =
      {z : ℂ | ‖(z - Complex.I) * (z - -Complex.I)‖ < C} := by
  ext z
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq, cyclotomic_four_eval_factor]

/-- **`{|Φ₄| < C}` is DISCONNECTED for `0 < C < 1`** — the widest disconnection
regime among the quadratic cyclotomics (foci `2` apart vs `√3`). -/
theorem not_isPreconnected_levelSet_four {C : ℝ} (hC : 0 < C) (hC' : C < 1) :
    ¬ IsPreconnected (Erdos1215.levelSet (cyclotomic 4 ℂ) C) := by
  rw [levelSet_cyclotomic_four_eq]
  exact not_isPreconnected_quadratic_lemniscate hC
    (by rw [norm_I_sub_neg_I_sq]; linarith)

/-- `{|Φ₄| < C}` is not path-connected for `0 < C < 1`. -/
theorem not_isPathConnected_levelSet_four {C : ℝ} (hC : 0 < C) (hC' : C < 1) :
    ¬ IsPathConnected (Erdos1215.levelSet (cyclotomic 4 ℂ) C) := by
  rw [levelSet_cyclotomic_four_eq]
  exact not_isPathConnected_quadratic_lemniscate hC
    (by rw [norm_I_sub_neg_I_sq]; linarith)

/-! ## `n = 6`: `Φ₆ = X² − X + 1`, foci at the primitive sixth roots of unity

`ζ = (1 + √3·i)/2` and its conjugate, again `√3` apart: disconnection for `C < 3/4`. -/

/-- The primitive sixth root of unity `ζ = (1 + √3·i)/2`. -/
noncomputable def zeta6 : ℂ := (1 + Real.sqrt 3 * Complex.I) / 2

/-- The conjugate primitive sixth root of unity `ζ̄ = (1 − √3·i)/2`. -/
noncomputable def zeta6' : ℂ := (1 - Real.sqrt 3 * Complex.I) / 2

private lemma zeta6_add : zeta6 + zeta6' = 1 := by
  simp only [zeta6, zeta6']; ring

private lemma zeta6_mul : zeta6 * zeta6' = 1 := by
  simp only [zeta6, zeta6']
  linear_combination (-(Complex.I ^ 2) / 4) * ofReal_sqrt_three_sq
    - (3 / 4 : ℂ) * Complex.I_sq

/-- `Φ₆` factors over its two roots: `Φ₆(z) = (z − ζ)(z − ζ̄)`. -/
theorem cyclotomic_six_eval_factor (z : ℂ) :
    (cyclotomic 6 ℂ).eval z = (z - zeta6) * (z - zeta6') := by
  rw [cyclotomic_six]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_one]
  linear_combination z * zeta6_add - zeta6_mul

/-- The foci of `Φ₆` are `√3` apart: `‖ζ − ζ̄‖² = 3`. -/
theorem norm_zeta6_sub_sq : ‖zeta6 - zeta6'‖ ^ 2 = 3 := by
  have h : zeta6 - zeta6' = (Real.sqrt 3 : ℂ) * Complex.I := by
    simp only [zeta6, zeta6']; ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3)]
  exact Real.sq_sqrt (by norm_num)

/-- The `Φ₆` sublevel set in factored (Cassini) form. -/
theorem levelSet_cyclotomic_six_eq (C : ℝ) :
    Erdos1215.levelSet (cyclotomic 6 ℂ) C =
      {z : ℂ | ‖(z - zeta6) * (z - zeta6')‖ < C} := by
  ext z
  simp only [Erdos1215.levelSet, Set.mem_setOf_eq, cyclotomic_six_eval_factor]

/-- **`{|Φ₆| < C}` is DISCONNECTED for `0 < C < 3/4`.** -/
theorem not_isPreconnected_levelSet_six {C : ℝ} (hC : 0 < C) (hC' : C < 3 / 4) :
    ¬ IsPreconnected (Erdos1215.levelSet (cyclotomic 6 ℂ) C) := by
  rw [levelSet_cyclotomic_six_eq]
  exact not_isPreconnected_quadratic_lemniscate hC
    (by rw [norm_zeta6_sub_sq]; linarith)

/-- `{|Φ₆| < C}` is not path-connected for `0 < C < 3/4`. -/
theorem not_isPathConnected_levelSet_six {C : ℝ} (hC : 0 < C) (hC' : C < 3 / 4) :
    ¬ IsPathConnected (Erdos1215.levelSet (cyclotomic 6 ℂ) C) := by
  rw [levelSet_cyclotomic_six_eq]
  exact not_isPathConnected_quadratic_lemniscate hC
    (by rw [norm_zeta6_sub_sq]; linarith)

end CyclotomicPolynomialsOQ02OQ11
