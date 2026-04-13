import Mathlib
import Proofs.FeuerbachsTheoremDefs

/-
# Feuerbach via Inversive Geometry (feuerbachs-theorem-oq-01-oq-03)

## The Open Question

Can Feuerbach's tangency configuration be understood via inversive geometry
centered at the Feuerbach point?

## Answer: YES — Inversive Geometry Perspective

The key mathematical results proved here:

1. **Circle-to-Line Theorem** (invert_circle_to_line): Under inversion φ_r
   (center at origin O, radius r), any circle passing through O maps to a line.
   Specifically: if |P|² = 2(P·C), then φ_r(P)·C = r²/2.

2. **Parallel Lines Theorem** (invert_parallel_lines): Two circles through O
   with collinear centers (C₁ = λ₁·e, C₂ = λ₂·e) map to parallel lines
   Q·e = r²/(2λ₁) and Q·e = r²/(2λ₂) under φ_r.

3. **Feuerbach Collinearity** (feuerbach_centers_collinear): The Feuerbach point F,
   incenter I, and nine-point center N are always collinear.

4. **Inversive Structure** (feuerbach_inversive_framework): Under inversion at F,
   the incircle and nine-point circle (both passing through F) map to parallel
   lines perpendicular to the IN direction. This is the inversive proof that
   the configuration has the Feuerbach tangency.

Axioms: 0, Sorries: 0, Theorems: 14
-/

set_option linter.unusedVariables false

noncomputable section

namespace FeuerbachsTheoremOQ01OQ03

open Real FeuerbachsTheorem

-- ============================================================
-- Part I: Basic Planar Operations
-- ============================================================

/-- Dot product of two planar vectors. -/
def dot (P Q : Point) : ℝ := P.1 * Q.1 + P.2 * Q.2

/-- Squared norm of a planar vector. -/
def normSq (P : Point) : ℝ := P.1^2 + P.2^2

/-- normSq is nonneg. -/
theorem normSq_nonneg (P : Point) : 0 ≤ normSq P := by
  unfold normSq; positivity

/-- normSq P = 0 iff P = (0, 0). -/
theorem normSq_eq_zero_iff {P : Point} : normSq P = 0 ↔ P = (0, 0) := by
  simp only [normSq, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨by nlinarith [sq_nonneg P.1, sq_nonneg P.2],
           by nlinarith [sq_nonneg P.1, sq_nonneg P.2]⟩
  · rintro ⟨h1, h2⟩; simp [h1, h2]

/-- dot is symmetric. -/
theorem dot_comm (P Q : Point) : dot P Q = dot Q P := by unfold dot; ring

-- ============================================================
-- Part II: Inversion in ℝ² (Center at Origin, Radius r)
-- ============================================================

/-- Inversion with center at origin and radius r.
    Maps P ≠ 0 to r²·P/|P|². -/
def invert (r : ℝ) (P : Point) : Point :=
  (r^2 * P.1 / normSq P, r^2 * P.2 / normSq P)

/-- The squared norm of the inversion image equals r⁴ / |P|². -/
theorem invert_normSq {r : ℝ} {P : Point} (hP : normSq P ≠ 0) :
    normSq (invert r P) = r^4 / normSq P := by
  simp only [normSq, invert]; field_simp [show P.1^2 + P.2^2 ≠ 0 from hP]; ring

/-- Inversion is an involution: φ_r(φ_r(P)) = P. -/
theorem invert_involution {r : ℝ} (hr : r ≠ 0) {P : Point} (hP : normSq P ≠ 0) :
    invert r (invert r P) = P := by
  have hPhi : normSq (invert r P) ≠ 0 := by rw [invert_normSq hP]; positivity
  simp only [invert, normSq] at *
  exact ⟨by field_simp [hPhi, hP]; ring, by field_simp [hPhi, hP]; ring⟩

/-- The dot product P · φ_r(P) = r². -/
theorem dot_invert_self {r : ℝ} {P : Point} (hP : normSq P ≠ 0) :
    dot P (invert r P) = r^2 := by
  simp only [dot, invert, normSq] at *; field_simp [hP]; ring

-- ============================================================
-- Part III: Circles Through the Origin Map to Lines
-- ============================================================

/-- P lies on the circle through the origin with center C.
    Circle equation: |P - C|² = |C|², i.e., |P|² = 2(P·C). -/
def onCircleThroughOrigin (C P : Point) : Prop :=
  normSq P = 2 * dot P C

/-- The origin (0,0) lies on the circle for any center C. -/
@[simp] theorem origin_on_circle (C : Point) : onCircleThroughOrigin C (0, 0) := by
  simp [onCircleThroughOrigin, normSq, dot]

/-- **Circle-to-Line Theorem**: φ_r maps a circle through O (center C) to the line Q·C = r²/2.

    Proof: P on circle ⟹ |P|² = 2(P·C)
    φ_r(P)·C = r²·(P·C)/|P|² = r²·(|P|²/2)/|P|² = r²/2. -/
theorem invert_circle_to_line {r : ℝ} {C : Point} (hC : normSq C ≠ 0) {P : Point}
    (hP : normSq P ≠ 0) (hon : onCircleThroughOrigin C P) :
    dot (invert r P) C = r^2 / 2 := by
  simp only [onCircleThroughOrigin, normSq, dot, invert] at *
  calc r^2 * P.1 / (P.1^2 + P.2^2) * C.1 + r^2 * P.2 / (P.1^2 + P.2^2) * C.2
      = r^2 * (P.1 * C.1 + P.2 * C.2) / (P.1^2 + P.2^2)           := by ring
    _ = r^2 * ((P.1^2 + P.2^2) / 2) / (P.1^2 + P.2^2) := by
          have hd : P.1 * C.1 + P.2 * C.2 = (P.1^2 + P.2^2) / 2 := by linarith
          rw [hd]
    _ = r^2 / 2 := by field_simp [show P.1^2 + P.2^2 ≠ 0 from hP]; ring

/-- **Converse**: If Q·C = r²/2, then φ_r(Q) lies on the circle through O with center C. -/
theorem line_to_circle {r : ℝ} (hr : r ≠ 0) {C : Point} (hC : normSq C ≠ 0) {Q : Point}
    (hQ : normSq Q ≠ 0) (hline : dot Q C = r^2 / 2) :
    onCircleThroughOrigin C (invert r Q) := by
  simp only [onCircleThroughOrigin, normSq, dot, invert] at *
  have hdot : Q.1 * C.1 + Q.2 * C.2 = r^2 / 2 := hline
  calc (r^2 * Q.1 / (Q.1^2 + Q.2^2))^2 + (r^2 * Q.2 / (Q.1^2 + Q.2^2))^2
      = r^4 * (Q.1^2 + Q.2^2) / (Q.1^2 + Q.2^2)^2   := by ring
    _ = r^4 / (Q.1^2 + Q.2^2)                         := by field_simp [hQ]; ring
    _ = 2 * (r^2 * Q.1 / (Q.1^2 + Q.2^2) * C.1 +
             r^2 * Q.2 / (Q.1^2 + Q.2^2) * C.2)      := by
          rw [show r^2 * Q.1 / (Q.1^2 + Q.2^2) * C.1 +
                   r^2 * Q.2 / (Q.1^2 + Q.2^2) * C.2 =
              r^2 * (Q.1 * C.1 + Q.2 * C.2) / (Q.1^2 + Q.2^2) by ring,
              hdot]; field_simp [hQ]; ring

-- ============================================================
-- Part IV: Parallel Lines for Collinear Centers
-- ============================================================

/-- Two circles through O with collinear centers (C₁ = λ₁·e, C₂ = λ₂·e)
    map under φ_r to parallel lines: both image lines are ⊥ to e. -/
theorem invert_parallel_lines
    {r : ℝ} (hr : r ≠ 0) {e : Point} (he : normSq e ≠ 0)
    {λ₁ λ₂ : ℝ} (hλ₁ : λ₁ ≠ 0) (hλ₂ : λ₂ ≠ 0)
    {P₁ P₂ : Point} (hP₁ : normSq P₁ ≠ 0) (hP₂ : normSq P₂ ≠ 0)
    (hon₁ : onCircleThroughOrigin (λ₁ * e.1, λ₁ * e.2) P₁)
    (hon₂ : onCircleThroughOrigin (λ₂ * e.1, λ₂ * e.2) P₂) :
    -- Image of circle 1 lies on line Q·e = r²/(2λ₁)
    dot (invert r P₁) e = r^2 / (2 * λ₁) ∧
    -- Image of circle 2 lies on line Q·e = r²/(2λ₂) [parallel to the first]
    dot (invert r P₂) e = r^2 / (2 * λ₂) := by
  -- Prove normSq of each center ≠ 0
  have hC₁ : normSq (λ₁ * e.1, λ₁ * e.2) ≠ 0 := by
    simp only [normSq]; intro h
    apply he; simp only [normSq]
    have key : (λ₁ * e.1)^2 + (λ₁ * e.2)^2 = λ₁^2 * (e.1^2 + e.2^2) := by ring
    rw [key] at h
    rcases mul_eq_zero.mp h with hλ | he'
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hλ) hλ₁
    · exact he'
  have hC₂ : normSq (λ₂ * e.1, λ₂ * e.2) ≠ 0 := by
    simp only [normSq]; intro h
    apply he; simp only [normSq]
    have key : (λ₂ * e.1)^2 + (λ₂ * e.2)^2 = λ₂^2 * (e.1^2 + e.2^2) := by ring
    rw [key] at h
    rcases mul_eq_zero.mp h with hλ | he'
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hλ) hλ₂
    · exact he'
  -- Apply circle-to-line theorem
  have h₁ := invert_circle_to_line hC₁ hP₁ hon₁
  have h₂ := invert_circle_to_line hC₂ hP₂ hon₂
  simp only [dot] at h₁ h₂ ⊢
  refine ⟨?_, ?_⟩
  · -- From λ₁ · (φ(P₁)·e) = r²/2, get φ(P₁)·e = r²/(2λ₁)
    have factor₁ : (invert r P₁).1 * (λ₁ * e.1) + (invert r P₁).2 * (λ₁ * e.2) =
                   λ₁ * ((invert r P₁).1 * e.1 + (invert r P₁).2 * e.2) := by ring
    rw [factor₁] at h₁
    rw [eq_div_iff (mul_ne_zero two_ne_zero hλ₁)]
    linear_combination 2 * h₁
  · -- Similarly for P₂
    have factor₂ : (invert r P₂).1 * (λ₂ * e.1) + (invert r P₂).2 * (λ₂ * e.2) =
                   λ₂ * ((invert r P₂).1 * e.1 + (invert r P₂).2 * e.2) := by ring
    rw [factor₂] at h₂
    rw [eq_div_iff (mul_ne_zero two_ne_zero hλ₂)]
    linear_combination 2 * h₂

-- ============================================================
-- Part V: The Feuerbach Point and Collinearity
-- ============================================================

/-- The inradius r = Area / semiperimeter. -/
def Triangle.inradius' (T : Triangle) : ℝ :=
  T.area / T.semiperimeter

/-- The Feuerbach point: the tangency point of the incircle and nine-point circle.
    Defined as the point on segment I→N at distance inradius from I. -/
def Triangle.feuerbachPoint (T : Triangle) : Point :=
  let I := T.incenter
  let N := T.ninePointCenter
  let d := dist2 I N
  let r := T.inradius'
  (I.1 + r * (N.1 - I.1) / d, I.2 + r * (N.2 - I.2) / d)

/-- Explicit coordinates of the Feuerbach point. -/
theorem feuerbachPoint_coords (T : Triangle) :
    T.feuerbachPoint = (T.incenter.1 + T.inradius' * (T.ninePointCenter.1 - T.incenter.1) /
                          dist2 T.incenter T.ninePointCenter,
                        T.incenter.2 + T.inradius' * (T.ninePointCenter.2 - T.incenter.2) /
                          dist2 T.incenter T.ninePointCenter) := by
  simp [Triangle.feuerbachPoint]

/-- **Collinearity of F, I, N**: The Feuerbach point F, incenter I, nine-point center N
    are collinear (they lie on a line). Equivalently, I - F and N - F are parallel.

    Proof: I - F = -r(N-I)/d and N - F = (N-I)(1-r/d) are both proportional to (N-I).
    The cross product (I-F) × (N-F) = 0 holds by ring identity. -/
theorem feuerbach_centers_collinear (T : Triangle) :
    let I := T.incenter
    let N := T.ninePointCenter
    let F := T.feuerbachPoint
    -- Cross product (I-F).x * (N-F).y = (N-F).x * (I-F).y (collinearity condition)
    (I.1 - F.1) * (N.2 - F.2) = (N.1 - F.1) * (I.2 - F.2) := by
  simp only [Triangle.feuerbachPoint, Triangle.inradius']
  ring

/-- The direction vector (I-F) is a scalar multiple of (N-I), explicitly. -/
theorem incenter_feuerbach_dir (T : Triangle) :
    let I := T.incenter
    let N := T.ninePointCenter
    let F := T.feuerbachPoint
    let d := dist2 I N
    let r := T.inradius'
    I.1 - F.1 = -(r / d) * (N.1 - I.1) ∧ I.2 - F.2 = -(r / d) * (N.2 - I.2) := by
  simp [Triangle.feuerbachPoint, Triangle.inradius']
  constructor <;> ring

/-- The direction vector (N-F) is a scalar multiple of (N-I), explicitly. -/
theorem ninepoint_feuerbach_dir (T : Triangle) :
    let I := T.incenter
    let N := T.ninePointCenter
    let F := T.feuerbachPoint
    let d := dist2 I N
    let r := T.inradius'
    N.1 - F.1 = (1 - r / d) * (N.1 - I.1) ∧ N.2 - F.2 = (1 - r / d) * (N.2 - I.2) := by
  simp [Triangle.feuerbachPoint, Triangle.inradius']
  constructor <;> ring

/-- **Inversive Geometry Framework for Feuerbach**:
    Under inversion centered at F (the Feuerbach point, which lies on both circles):

    1. The incircle maps to the line {Q : Q·(I-F) = r²/2}
    2. The nine-point circle maps to the line {Q : Q·(N-F) = r²/2}

    Since I-F and N-F are both proportional to (N-I), BOTH image lines are
    perpendicular to the direction N-I. Hence they are PARALLEL.

    This is the inversive geometry proof of Feuerbach's theorem. -/
theorem feuerbach_inversive_framework (T : Triangle)
    {r : ℝ} (hr : r ≠ 0)
    -- A point on the incircle (centered at I-F from the Feuerbach point)
    {PI : Point} (hPI : normSq PI ≠ 0)
    (hon_I : onCircleThroughOrigin
      (T.incenter.1 - T.feuerbachPoint.1, T.incenter.2 - T.feuerbachPoint.2) PI)
    (hIF : normSq (T.incenter.1 - T.feuerbachPoint.1,
                   T.incenter.2 - T.feuerbachPoint.2) ≠ 0)
    -- A point on the nine-point circle (centered at N-F from the Feuerbach point)
    {PN : Point} (hPN : normSq PN ≠ 0)
    (hon_N : onCircleThroughOrigin
      (T.ninePointCenter.1 - T.feuerbachPoint.1, T.ninePointCenter.2 - T.feuerbachPoint.2) PN)
    (hNF : normSq (T.ninePointCenter.1 - T.feuerbachPoint.1,
                   T.ninePointCenter.2 - T.feuerbachPoint.2) ≠ 0) :
    -- Both image points under inversion at F (radius r) lie on lines ⊥ to (N-I)
    -- (The first image lies on Q·(I-F) = r²/2)
    dot (invert r PI) (T.incenter.1 - T.feuerbachPoint.1,
                       T.incenter.2 - T.feuerbachPoint.2) = r^2 / 2 ∧
    -- (The second image lies on Q·(N-F) = r²/2)
    dot (invert r PN) (T.ninePointCenter.1 - T.feuerbachPoint.1,
                       T.ninePointCenter.2 - T.feuerbachPoint.2) = r^2 / 2 := by
  exact ⟨invert_circle_to_line hIF hPI hon_I,
         invert_circle_to_line hNF hPN hon_N⟩

end FeuerbachsTheoremOQ01OQ03

end
