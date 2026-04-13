/-
  Feuerbach's Theorem DefsOQ03: Uniqueness of the Feuerbach Point

  ## The Open Question

  The Feuerbach point is the tangency point of the nine-point circle and incircle.
  But is it the UNIQUE common point of these two circles?

  ## What This File Proves

  ### Definition of the Feuerbach Point

  The Feuerbach point F is the unique point on the ray from nine-point center N
  through incenter I, at distance R₂ (ninePointRadius) from N:

    F = N + (R₂ / d) * (I - N)    where d = R₂ - r = |NI| (from Feuerbach's theorem)

  Valid for non-equilateral triangles (inradius < ninePointRadius).

  ### F Lies on Both Circles (membership theorems)

  feuerbachPoint_on_ninePointCircle: dist2 N F = R₂
  feuerbachPoint_on_incircle:        dist2 I F = r

  ### Uniqueness of the Feuerbach Point (Main Result)

  If P lies on both the nine-point circle and the incircle of a non-equilateral
  triangle, then P = F.

  Proof strategy (sum of squares): Define v₁ = e₁d - R₂Δ₁, v₂ = e₂d - R₂Δ₂,
  where e = P - N, Δ = I - N. The three constraints (two circles + Feuerbach
  distance theorem) force v₁² + v₂² = 0, hence v₁ = v₂ = 0 and P = F.

  ### Explicit Feuerbach Point for 3-4-5 Triangle

  For the 3-4-5 right triangle: F = (2, 1).

  Status: 7 theorems, 0 sorries, 0 axioms
-/

import Proofs.FeuerbachsTheorem

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremDefsOQ03

open FeuerbachsTheorem FeuerbachsTheoremOQ01 Real

-- ============================================================
-- Part I: Helper Lemmas
-- ============================================================

/-- Convert dist2 equality to squared form: dist2 P Q = r → (Q.1-P.1)²+(Q.2-P.2)² = r². -/
private lemma dist2_to_sq (P Q : Point) (r : ℝ) (h : dist2 P Q = r) :
    (Q.1 - P.1)^2 + (Q.2 - P.2)^2 = r ^ 2 := by
  have hnn : 0 ≤ (Q.1 - P.1)^2 + (Q.2 - P.2)^2 := by positivity
  have h1 : dist2 P Q ^ 2 = (Q.1 - P.1)^2 + (Q.2 - P.2)^2 := by
    unfold dist2; exact Real.sq_sqrt hnn
  linarith [h ▸ h1]

/-- The NI distance in raw sqrt form.
    From Feuerbach: dist2 N I = |R₂ - r| = R₂ - r (since r < R₂). -/
private lemma feuerbach_NI_sqrt (T : Triangle) (h : T.inradius < T.ninePointRadius) :
    Real.sqrt ((T.incenter.1 - T.ninePointCenter.1)^2 +
               (T.incenter.2 - T.ninePointCenter.2)^2) =
    T.ninePointRadius - T.inradius := by
  have hd : 0 < T.ninePointRadius - T.inradius := by linarith
  have hNI := feuerbach_incircle_distance T
  rw [abs_of_pos hd] at hNI
  unfold dist2 at hNI
  exact hNI

-- ============================================================
-- Part II: The Feuerbach Point
-- ============================================================

/-- **The Feuerbach Point**: the tangency point of the nine-point circle and incircle.

    Defined as the point on the ray from nine-point center N through incenter I
    at distance R₂ (ninePointRadius) from N.

    Requires inradius < ninePointRadius (non-equilateral triangle). -/
def feuerbachPoint (T : Triangle) (h : T.inradius < T.ninePointRadius) : Point :=
  let d := T.ninePointRadius - T.inradius
  (T.ninePointCenter.1 + (T.ninePointRadius / d) * (T.incenter.1 - T.ninePointCenter.1),
   T.ninePointCenter.2 + (T.ninePointRadius / d) * (T.incenter.2 - T.ninePointCenter.2))

/-- **F lies on the nine-point circle**: dist2(N, F) = R₂. -/
theorem feuerbachPoint_on_ninePointCircle (T : Triangle) (h : T.inradius < T.ninePointRadius) :
    dist2 T.ninePointCenter (feuerbachPoint T h) = T.ninePointRadius := by
  have hd : 0 < T.ninePointRadius - T.inradius := by linarith
  have hd_ne : T.ninePointRadius - T.inradius ≠ 0 := ne_of_gt hd
  unfold dist2 feuerbachPoint
  rw [show (T.ninePointCenter.1 + T.ninePointRadius / (T.ninePointRadius - T.inradius) *
           (T.incenter.1 - T.ninePointCenter.1) - T.ninePointCenter.1)^2 +
          (T.ninePointCenter.2 + T.ninePointRadius / (T.ninePointRadius - T.inradius) *
           (T.incenter.2 - T.ninePointCenter.2) - T.ninePointCenter.2)^2 =
      (T.ninePointRadius / (T.ninePointRadius - T.inradius))^2 *
      ((T.incenter.1 - T.ninePointCenter.1)^2 +
       (T.incenter.2 - T.ninePointCenter.2)^2) by field_simp; ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg (ninePointRadius_nonneg T) (le_of_lt hd))]
  rw [feuerbach_NI_sqrt T h]
  field_simp

/-- **F lies on the incircle**: dist2(I, F) = r. -/
theorem feuerbachPoint_on_incircle (T : Triangle) (h : T.inradius < T.ninePointRadius) :
    dist2 T.incenter (feuerbachPoint T h) = T.inradius := by
  have hd : 0 < T.ninePointRadius - T.inradius := by linarith
  have hd_ne : T.ninePointRadius - T.inradius ≠ 0 := ne_of_gt hd
  unfold dist2 feuerbachPoint
  rw [show (T.ninePointCenter.1 + T.ninePointRadius / (T.ninePointRadius - T.inradius) *
           (T.incenter.1 - T.ninePointCenter.1) - T.incenter.1)^2 +
          (T.ninePointCenter.2 + T.ninePointRadius / (T.ninePointRadius - T.inradius) *
           (T.incenter.2 - T.ninePointCenter.2) - T.incenter.2)^2 =
      (T.inradius / (T.ninePointRadius - T.inradius))^2 *
      ((T.incenter.1 - T.ninePointCenter.1)^2 +
       (T.incenter.2 - T.ninePointCenter.2)^2) by field_simp; ring]
  rw [Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (div_nonneg (le_of_lt (inradius_pos T)) (le_of_lt hd))]
  rw [feuerbach_NI_sqrt T h]
  field_simp

-- ============================================================
-- Part III: Uniqueness of the Feuerbach Point (Main Result)
-- ============================================================

set_option maxHeartbeats 800000 in
/-- **Uniqueness of the Feuerbach Point**

    The Feuerbach point is the unique point lying on both the nine-point circle
    and the incircle of a non-equilateral triangle.

    Proof (sum of squares): Let e1=P.1-N.1, e2=P.2-N.2, D1=I.1-N.1, D2=I.2-N.2.
    From the two circle conditions and Feuerbach's distance theorem:
    (1) e1^2+e2^2 = R2^2, (2) (e1-D1)^2+(e2-D2)^2 = r^2, (3) D1^2+D2^2 = d^2

    linear_combination (1)-(2)+(3) gives: 2(e1*D1+e2*D2) = 2*R2*d.

    Set v1 = e1*d-R2*D1, v2 = e2*d-R2*D2. Then:
    v1^2+v2^2 = d^2*(1) - 2*R2*d*dot + R2^2*(3) = 0.

    Hence v1=v2=0, giving P = F by definition. -/
theorem feuerbachPoint_unique (T : Triangle) (h : T.inradius < T.ninePointRadius)
    (P : Point)
    (hPN : dist2 T.ninePointCenter P = T.ninePointRadius)
    (hPI : dist2 T.incenter P = T.inradius) :
    P = feuerbachPoint T h := by
  have hd_pos : 0 < T.ninePointRadius - T.inradius := by linarith
  have hd_ne : T.ninePointRadius - T.inradius ≠ 0 := ne_of_gt hd_pos
  -- Step 1: Squared distance forms
  have hPN_sq : (P.1 - T.ninePointCenter.1)^2 + (P.2 - T.ninePointCenter.2)^2 =
                T.ninePointRadius ^ 2 :=
    dist2_to_sq T.ninePointCenter P T.ninePointRadius hPN
  have hPI_sq : (P.1 - T.incenter.1)^2 + (P.2 - T.incenter.2)^2 =
                T.inradius ^ 2 :=
    dist2_to_sq T.incenter P T.inradius hPI
  -- Step 2: |NI|² = d² from Feuerbach's theorem
  have hNI : dist2 T.ninePointCenter T.incenter = T.ninePointRadius - T.inradius := by
    rw [feuerbach_incircle_distance T, abs_of_pos hd_pos]
  have hNI_sq : (T.incenter.1 - T.ninePointCenter.1)^2 + (T.incenter.2 - T.ninePointCenter.2)^2 =
                (T.ninePointRadius - T.inradius) ^ 2 :=
    dist2_to_sq T.ninePointCenter T.incenter (T.ninePointRadius - T.inradius) hNI
  -- Step 3: Dot product identity — 2(e₁Δ₁ + e₂Δ₂) = 2R₂d
  have hdot : 2 * ((P.1 - T.ninePointCenter.1) * (T.incenter.1 - T.ninePointCenter.1) +
                   (P.2 - T.ninePointCenter.2) * (T.incenter.2 - T.ninePointCenter.2)) =
              2 * T.ninePointRadius * (T.ninePointRadius - T.inradius) := by
    linear_combination hPN_sq - hPI_sq + hNI_sq
  -- Step 4: Sum of squares vanishes
  have hsum :
      ((P.1 - T.ninePointCenter.1) * (T.ninePointRadius - T.inradius) -
       T.ninePointRadius * (T.incenter.1 - T.ninePointCenter.1))^2 +
      ((P.2 - T.ninePointCenter.2) * (T.ninePointRadius - T.inradius) -
       T.ninePointRadius * (T.incenter.2 - T.ninePointCenter.2))^2 = 0 := by
    linear_combination
      (T.ninePointRadius - T.inradius)^2 * hPN_sq +
      T.ninePointRadius^2 * hNI_sq +
      (- T.ninePointRadius * (T.ninePointRadius - T.inradius)) * hdot
  -- Step 5: Extract v₁ = 0 and v₂ = 0 from v₁²+v₂²=0
  have hv1_sq : ((P.1 - T.ninePointCenter.1) * (T.ninePointRadius - T.inradius) -
                  T.ninePointRadius * (T.incenter.1 - T.ninePointCenter.1))^2 = 0 := by
    nlinarith [sq_nonneg ((P.1 - T.ninePointCenter.1) * (T.ninePointRadius - T.inradius) -
                           T.ninePointRadius * (T.incenter.1 - T.ninePointCenter.1)),
               sq_nonneg ((P.2 - T.ninePointCenter.2) * (T.ninePointRadius - T.inradius) -
                           T.ninePointRadius * (T.incenter.2 - T.ninePointCenter.2))]
  have hv2_sq : ((P.2 - T.ninePointCenter.2) * (T.ninePointRadius - T.inradius) -
                  T.ninePointRadius * (T.incenter.2 - T.ninePointCenter.2))^2 = 0 := by
    nlinarith [sq_nonneg ((P.1 - T.ninePointCenter.1) * (T.ninePointRadius - T.inradius) -
                           T.ninePointRadius * (T.incenter.1 - T.ninePointCenter.1)),
               sq_nonneg ((P.2 - T.ninePointCenter.2) * (T.ninePointRadius - T.inradius) -
                           T.ninePointRadius * (T.incenter.2 - T.ninePointCenter.2))]
  have hv1 : (P.1 - T.ninePointCenter.1) * (T.ninePointRadius - T.inradius) =
              T.ninePointRadius * (T.incenter.1 - T.ninePointCenter.1) := by
    have := sq_eq_zero_iff.mp hv1_sq; linarith
  have hv2 : (P.2 - T.ninePointCenter.2) * (T.ninePointRadius - T.inradius) =
              T.ninePointRadius * (T.incenter.2 - T.ninePointCenter.2) := by
    have := sq_eq_zero_iff.mp hv2_sq; linarith
  -- Step 6: P = feuerbachPoint T h
  unfold feuerbachPoint
  apply Prod.ext
  · field_simp [hd_ne]; linarith
  · field_simp [hd_ne]; linarith

-- ============================================================
-- Part IV: Concrete Example — 3-4-5 Right Triangle
-- ============================================================

/-- The 3-4-5 right triangle is non-equilateral: inradius (1) < ninePointRadius (5/4). -/
theorem triangle_345_not_equilateral : triangle_345.inradius < triangle_345.ninePointRadius := by
  rw [triangle_345_inradius, triangle_345_ninePointRadius]
  norm_num

/-- **The Feuerbach point of the 3-4-5 triangle is (2, 1)**.
    Computed from N=(3/4,1), I=(1,1), R₂=5/4, r=1, d=1/4:
    F = (3/4 + 5*(1/4), 1 + 0) = (2, 1). -/
theorem triangle_345_feuerbachPoint :
    feuerbachPoint triangle_345 triangle_345_not_equilateral = (2, 1) := by
  unfold feuerbachPoint
  rw [triangle_345_inradius, triangle_345_ninePointRadius,
      triangle_345_ninePointCenter, triangle_345_incenter]
  norm_num

/-- The Feuerbach point (2, 1) lies on the nine-point circle. -/
theorem triangle_345_feuerbachPoint_on_ninePointCircle :
    dist2 triangle_345.ninePointCenter
      (feuerbachPoint triangle_345 triangle_345_not_equilateral) =
    triangle_345.ninePointRadius :=
  feuerbachPoint_on_ninePointCircle triangle_345 triangle_345_not_equilateral

/-- The Feuerbach point (2, 1) lies on the incircle. -/
theorem triangle_345_feuerbachPoint_on_incircle :
    dist2 triangle_345.incenter
      (feuerbachPoint triangle_345 triangle_345_not_equilateral) =
    triangle_345.inradius :=
  feuerbachPoint_on_incircle triangle_345 triangle_345_not_equilateral

/-
## Summary

7 theorems (plus 2 private lemmas), 0 sorries, 0 axioms.

Main result: feuerbachPoint_unique — the Feuerbach point is the unique common
point of the nine-point circle and incircle. Proof uses a sum-of-squares
argument: v₁²+v₂²=0 forces v₁=v₂=0, uniquely determining P.
-/

end FeuerbachsTheoremDefsOQ03

end
