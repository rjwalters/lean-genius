/-
# The Nine-Point Circle in an Abstract Inner Product Space

## The Open Question (Feuerbach Defs OQ-04 → OQ-03)

The gallery's nine-point circle results (`FeuerbachsTheoremDefs.lean`,
`FeuerbachsTheoremDefsOQ04.lean`) are tied to a fixed coordinate model:
`Point = ℝ × ℝ`, with circumcenter, orthocenter, etc. given by explicit
two-dimensional coordinate formulas. The natural next step toward a *Mathlib
contribution* is to discard coordinates entirely and prove the theorem for an
arbitrary triangle in any real inner product space.

This file does exactly that. Working in a general `InnerProductSpace ℝ V`, it
proves: for any three points `A B C` with a common circumcenter `O`
(`dist O A = dist O B = dist O C =: R`), the nine classical points
- the three side midpoints,
- the three midpoints of vertex-to-orthocenter segments,
- the three feet of the altitudes,
all lie on the single sphere of radius `R/2` centred at the nine-point centre
`N = (A + B + C - O)/2` (the midpoint of `O` and the orthocenter
`H = A + B + C - 2•O`).

## Why this is genuinely more general than the gallery

* **No coordinates.** `V` is *any* real inner product space — `EuclideanSpace ℝ
  (Fin 2)`, `ℝ³`, an abstract Hilbert space — not `ℝ × ℝ`.
* **No nondegeneracy hypothesis for six of the nine points.** The side
  midpoints and the vertex-orthocenter midpoints lie on the circle for *any*
  `A B C` on a common sphere about `O`, even collinear ones. Only the altitude
  feet require the corresponding side to be a genuine line (`B ≠ C`, etc.).
* **Free choice of circumcenter.** `O` is an arbitrary point; the statement is
  manifestly translation-covariant.

Mathlib has **no** nine-point circle / Feuerbach circle result, so this is new
infrastructure. The headline is `ninePoints_mem_sphere`.

## Proof strategy

After subtracting the circumcenter `O`, everything reduces to vector identities
about `a = A - O`, `b = B - O`, `c = C - O` with `‖a‖ = ‖b‖ = ‖c‖ = R`:

* **Six midpoint points (clean).** Each difference `N - P` equals `±(1/2)•x`
  for `x ∈ {a, b, c}`, so `dist N P = ‖x‖/2 = R/2`.
* **Three altitude feet (the crux).** The foot of the perpendicular from `A`
  onto line `BC` is `F = B + t•(C-B)`, `t = ⟪A-B, C-B⟫ / ⟪C-B, C-B⟫`. A direct
  inner-product expansion gives `‖N - F‖² = R²/4`, discharged by `field_simp; ring`
  after the three radius identities `⟪x,x⟫ = R²` are substituted.

Status: 0 axioms, 0 sorries — fully verified, fully general.
-/

import Mathlib

open scoped InnerProductSpace

set_option linter.unusedVariables false

namespace NinePointCircle

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## Constructions (coordinate-free) -/

/-- The orthocenter of triangle `A B C` with circumcenter `O`: `H = A + B + C - 2•O`. -/
def orthocenter (A B C O : V) : V := A + B + C - (2 : ℝ) • O

/-- The nine-point centre: the midpoint of circumcenter `O` and orthocenter,
equal to `(A + B + C - O)/2`. -/
def ninePointCenter (A B C O : V) : V := (2 : ℝ)⁻¹ • (A + B + C - O)

/-- The nine-point radius: half the circumradius `dist O A`. -/
def ninePointRadius (A B C O : V) : ℝ := dist O A / 2

/-- The foot of the perpendicular from `P` onto the line through `Q` and `S`. -/
def foot (P Q S : V) : V :=
  Q + (⟪P - Q, S - Q⟫_ℝ / ⟪S - Q, S - Q⟫_ℝ) • (S - Q)

/-- The nine-point centre is symmetric in the three vertices. -/
theorem ninePointCenter_rotate (A B C O : V) :
    ninePointCenter B C A O = ninePointCenter A B C O := by
  simp only [ninePointCenter]; module

/-! ## Core lemma: altitude foot with circumcenter at the origin -/

/-- **Foot of altitude, circumcenter at origin.** With `‖a‖ = ‖b‖ = ‖c‖ = R`
and `b ≠ c`, the foot of the perpendicular from `a` onto line `bc` lies at
distance `R/2` from `N = (a+b+c)/2`. This is the analytic heart of the theorem. -/
theorem foot_core (a b c : V) (R : ℝ)
    (ha : ‖a‖ = R) (hb : ‖b‖ = R) (hc : ‖c‖ = R) (hbc : b ≠ c) :
    dist ((2 : ℝ)⁻¹ • (a + b + c))
      (b + (⟪a - b, c - b⟫_ℝ / ⟪c - b, c - b⟫_ℝ) • (c - b)) = R / 2 := by
  have e_aa : ⟪a, a⟫_ℝ = R ^ 2 := by rw [real_inner_self_eq_norm_sq, ha]
  have e_bb : ⟪b, b⟫_ℝ = R ^ 2 := by rw [real_inner_self_eq_norm_sq, hb]
  have e_cc : ⟪c, c⟫_ℝ = R ^ 2 := by rw [real_inner_self_eq_norm_sq, hc]
  have hR : 0 ≤ R := ha ▸ norm_nonneg a
  have hw : c - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbc)
  have hs_ne : ⟪c - b, c - b⟫_ℝ ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]; positivity
  have hs_val : ⟪c - b, c - b⟫_ℝ = 2 * R ^ 2 - 2 * ⟪b, c⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm b c, e_bb, e_cc]; ring
  have hden : (2 * R ^ 2 - 2 * ⟪b, c⟫_ℝ) ≠ 0 := hs_val ▸ hs_ne
  have hden2 : (R ^ 2 - ⟪b, c⟫_ℝ) ≠ 0 := by intro h; apply hden; linarith
  have hd : (2 : ℝ)⁻¹ • (a + b + c)
      - (b + (⟪a - b, c - b⟫_ℝ / ⟪c - b, c - b⟫_ℝ) • (c - b))
      = (2 : ℝ)⁻¹ • (a - b + c)
      - (⟪a - b, c - b⟫_ℝ / ⟪c - b, c - b⟫_ℝ) • (c - b) := by module
  rw [dist_eq_norm, hd]
  rw [show R / 2 = Real.sqrt ((R / 2) ^ 2) from (Real.sqrt_sq (by positivity)).symm,
      ← Real.sqrt_sq (norm_nonneg _)]
  congr 1
  rw [← real_inner_self_eq_norm_sq, hs_val]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_comm a b, real_inner_comm a c, real_inner_comm b c,
    e_aa, e_bb, e_cc]
  field_simp [hden2]
  ring

/-! ## Helper for the six "midpoint-type" points -/

/-- If `N - P = (1/2)•Y` with `‖Y‖ = dist O A`, then `P` lies on the nine-point
sphere. All six midpoint-type points are of this shape. -/
private theorem dist_eq_of_diff (A B C O P Y : V)
    (hY : ‖Y‖ = dist O A)
    (hPid : ninePointCenter A B C O - P = (2 : ℝ)⁻¹ • Y) :
    dist (ninePointCenter A B C O) P = ninePointRadius A B C O := by
  rw [dist_eq_norm, hPid, ninePointRadius, norm_smul, hY]
  simp; ring

/-! ## The six midpoint-type memberships

Side midpoint of `BC` and the midpoint of `AH` need no hypothesis; the other four
need the relevant circumradius equality. -/

theorem dist_midpoint_BC (A B C O : V) :
    dist (ninePointCenter A B C O) ((2 : ℝ)⁻¹ • (B + C)) = ninePointRadius A B C O :=
  dist_eq_of_diff A B C O _ (A - O) (by rw [dist_eq_norm, norm_sub_rev])
    (by simp only [ninePointCenter]; module)

theorem dist_midpoint_CA (A B C O : V) (hAB : dist O A = dist O B) :
    dist (ninePointCenter A B C O) ((2 : ℝ)⁻¹ • (C + A)) = ninePointRadius A B C O :=
  dist_eq_of_diff A B C O _ (B - O) (by rw [hAB, dist_eq_norm, norm_sub_rev])
    (by simp only [ninePointCenter]; module)

theorem dist_midpoint_AB (A B C O : V) (hAC : dist O A = dist O C) :
    dist (ninePointCenter A B C O) ((2 : ℝ)⁻¹ • (A + B)) = ninePointRadius A B C O :=
  dist_eq_of_diff A B C O _ (C - O) (by rw [hAC, dist_eq_norm, norm_sub_rev])
    (by simp only [ninePointCenter]; module)

theorem dist_midpoint_AH (A B C O : V) :
    dist (ninePointCenter A B C O) ((2 : ℝ)⁻¹ • (A + orthocenter A B C O))
      = ninePointRadius A B C O :=
  dist_eq_of_diff A B C O _ (O - A) (by rw [dist_eq_norm])
    (by simp only [ninePointCenter, orthocenter]; module)

theorem dist_midpoint_BH (A B C O : V) (hAB : dist O A = dist O B) :
    dist (ninePointCenter A B C O) ((2 : ℝ)⁻¹ • (B + orthocenter A B C O))
      = ninePointRadius A B C O :=
  dist_eq_of_diff A B C O _ (O - B) (by rw [hAB, dist_eq_norm])
    (by simp only [ninePointCenter, orthocenter]; module)

theorem dist_midpoint_CH (A B C O : V) (hAC : dist O A = dist O C) :
    dist (ninePointCenter A B C O) ((2 : ℝ)⁻¹ • (C + orthocenter A B C O))
      = ninePointRadius A B C O :=
  dist_eq_of_diff A B C O _ (O - C) (by rw [hAC, dist_eq_norm])
    (by simp only [ninePointCenter, orthocenter]; module)

/-! ## The three altitude feet (via the core lemma + translation) -/

/-- General altitude-foot membership: `foot A B C` lies on the nine-point sphere.
Obtained from `foot_core` by subtracting the circumcenter `O`. -/
theorem dist_foot (A B C O : V) (R : ℝ)
    (ha : dist O A = R) (hb : dist O B = R) (hc : dist O C = R) (hbc : B ≠ C) :
    dist (ninePointCenter A B C O) (foot A B C) = R / 2 := by
  have hna : ‖A - O‖ = R := by rw [norm_sub_rev, ← dist_eq_norm]; exact ha
  have hnb : ‖B - O‖ = R := by rw [norm_sub_rev, ← dist_eq_norm]; exact hb
  have hnc : ‖C - O‖ = R := by rw [norm_sub_rev, ← dist_eq_norm]; exact hc
  have hbc' : B - O ≠ C - O := fun h => hbc (by
    have h2 := congrArg (· + O) h; simpa using h2)
  have hcore := foot_core (A - O) (B - O) (C - O) R hna hnb hnc hbc'
  simp only [sub_sub_sub_cancel_right] at hcore
  have e1 : (2 : ℝ)⁻¹ • (A - O + (B - O) + (C - O)) = ninePointCenter A B C O - O := by
    simp only [ninePointCenter]; module
  have e2 : B - O + (⟪A - B, C - B⟫_ℝ / ⟪C - B, C - B⟫_ℝ) • (C - B)
      = foot A B C - O := by simp only [foot]; module
  rw [e1, e2, dist_sub_right] at hcore
  exact hcore

theorem dist_foot_A (A B C O : V) (R : ℝ)
    (ha : dist O A = R) (hb : dist O B = R) (hc : dist O C = R) (hbc : B ≠ C) :
    dist (ninePointCenter A B C O) (foot A B C) = R / 2 :=
  dist_foot A B C O R ha hb hc hbc

theorem dist_foot_B (A B C O : V) (R : ℝ)
    (ha : dist O A = R) (hb : dist O B = R) (hc : dist O C = R) (hca : C ≠ A) :
    dist (ninePointCenter A B C O) (foot B C A) = R / 2 := by
  rw [← ninePointCenter_rotate A B C O]
  exact dist_foot B C A O R hb hc ha hca

theorem dist_foot_C (A B C O : V) (R : ℝ)
    (ha : dist O A = R) (hb : dist O B = R) (hc : dist O C = R) (hab : A ≠ B) :
    dist (ninePointCenter A B C O) (foot C A B) = R / 2 := by
  rw [← ninePointCenter_rotate A B C O, ← ninePointCenter_rotate B C A O]
  exact dist_foot C A B O R hc ha hb hab

/-! ## Headline: all nine points lie on one sphere -/

/-- **The nine-point circle theorem (coordinate-free).** Given any triangle
`A B C` in a real inner product space with common circumcenter `O`
(`dist O A = dist O B = dist O C = R`) and distinct vertices, all nine special
points lie on the single sphere of radius `R/2` about the nine-point centre. -/
theorem ninePoints_mem_sphere (A B C O : V) (R : ℝ)
    (ha : dist O A = R) (hb : dist O B = R) (hc : dist O C = R)
    (hAB : A ≠ B) (hBC : B ≠ C) (hCA : C ≠ A) :
    ((2 : ℝ)⁻¹ • (B + C)) ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) ∧
    ((2 : ℝ)⁻¹ • (C + A)) ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) ∧
    ((2 : ℝ)⁻¹ • (A + B)) ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) ∧
    ((2 : ℝ)⁻¹ • (A + orthocenter A B C O)) ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) ∧
    ((2 : ℝ)⁻¹ • (B + orthocenter A B C O)) ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) ∧
    ((2 : ℝ)⁻¹ • (C + orthocenter A B C O)) ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) ∧
    foot A B C ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) ∧
    foot B C A ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) ∧
    foot C A B ∈ Metric.sphere (ninePointCenter A B C O) (R / 2) := by
  have hAB' : dist O A = dist O B := by rw [ha, hb]
  have hAC' : dist O A = dist O C := by rw [ha, hc]
  have hr : ninePointRadius A B C O = R / 2 := by simp only [ninePointRadius]; rw [ha]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [Metric.mem_sphere, dist_comm]
  · rw [← hr]; exact dist_midpoint_BC A B C O
  · rw [← hr]; exact dist_midpoint_CA A B C O hAB'
  · rw [← hr]; exact dist_midpoint_AB A B C O hAC'
  · rw [← hr]; exact dist_midpoint_AH A B C O
  · rw [← hr]; exact dist_midpoint_BH A B C O hAB'
  · rw [← hr]; exact dist_midpoint_CH A B C O hAC'
  · exact dist_foot_A A B C O R ha hb hc hBC
  · exact dist_foot_B A B C O R ha hb hc hCA
  · exact dist_foot_C A B C O R ha hb hc hAB

end

end NinePointCircle
