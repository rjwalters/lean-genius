/-
# Law of Sines via InnerProductGeometry.angle

## Research Problem: law-of-cosines-oq-06

The Law of Sines: in a triangle with vertices A, B, C ∈ ℝ²,
sides a = |BC|, b = |AC|, c = |AB|, angles α, β, γ opposite those sides:

  a / sin(α) = b / sin(β) = c / sin(γ)

Formalized using:
- EuclideanSpace ℝ (Fin 2)
- InnerProductGeometry.angle
- 2D cross product for area

## Proof Strategy

1. **2D Lagrange identity** (by ring): ‖u‖²‖v‖² = ⟨u,v⟩² + (u₀v₁-u₁v₀)²
2. **Sin-cross identity** (proved): sin(angle u v) · ‖u‖ · ‖v‖ = |cross2D u v|
3. **Area formula**: Area = (1/2)|cross2D(B-A, C-A)| = (1/2)cb·sin(α) = ...
4. **Law of Sines**: equating areas gives a/sin(α) = b/sin(β)

## Status: 0 axioms, 0 sorries

## References
- Parent: LawOfCosines.lean
- SphericalLawOfSines.lean (spherical version)
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

noncomputable section

open scoped RealInnerProductSpace

namespace LawOfSines

abbrev Vec2 := EuclideanSpace ℝ (Fin 2)

-- ============================================================
-- Part I: 2D Cross Product and Lagrange Identity
-- ============================================================

def cross2D (u v : Vec2) : ℝ := u 0 * v 1 - u 1 * v 0

lemma cross2D_self (u : Vec2) : cross2D u u = 0 := by simp [cross2D]; ring

lemma cross2D_antisymm (u v : Vec2) : cross2D u v = -cross2D v u := by
  simp [cross2D]; ring

/-- **2D Lagrange Identity**: ‖u‖²‖v‖² = ⟨u,v⟩² + (cross2D u v)²
    Proof by ring in Fin 2 coordinates. -/
theorem lagrange_2d (u v : Vec2) :
    ‖u‖ ^ 2 * ‖v‖ ^ 2 = (@inner ℝ _ _ u v) ^ 2 + cross2D u v ^ 2 := by
  simp only [EuclideanSpace.norm_sq_apply, EuclideanSpace.inner_apply,
             cross2D, Fin.sum_univ_two]
  ring

-- ============================================================
-- Part II: Sin-Angle / Cross Product Identity (proved)
-- ============================================================

/-- **Sin-Cross Identity** (proved, 0 axioms):
    sin(angle u v) · (‖u‖ · ‖v‖) = |cross2D u v|

    Proof chain:
    1. InnerProductGeometry.angle u v = arccos(⟨u,v⟩/(‖u‖‖v‖))
    2. Real.sin_arccos: sin(arccos x) = sqrt(1 - x²)
    3. sqrt(1 - (⟨u,v⟩/N)²) · N = sqrt((1-(⟨u,v⟩/N)²) · N²)
       [since N = sqrt(N²) and Real.sqrt_mul]
    4. (1 - (⟨u,v⟩/N)²) · N² = N² - ⟨u,v⟩² = cross²  [by Lagrange]
    5. sqrt(cross²) = |cross|  [Real.sqrt_sq_eq_abs] -/
lemma sin_angle_mul_norms (u v : Vec2) (hu : u ≠ 0) (hv : v ≠ 0) :
    Real.sin (InnerProductGeometry.angle u v) * (‖u‖ * ‖v‖) = |cross2D u v| := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hN_pos : 0 < ‖u‖ * ‖v‖ := mul_pos hnu hnv
  have hN_nn : 0 ≤ ‖u‖ * ‖v‖ := le_of_lt hN_pos
  have hlag := lagrange_2d u v
  -- Step 1: angle = arccos(inner/N), apply sin(arccos x) = sqrt(1 - x²)
  rw [InnerProductGeometry.angle, Real.sin_arccos]
  -- Step 2: 0 ≤ 1 - (inner/N)² (Cauchy-Schwarz from Lagrange + cross² ≥ 0)
  have hcs : (@inner ℝ _ _ u v) ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    nlinarith [sq_nonneg (cross2D u v), show (‖u‖ * ‖v‖) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 from by ring]
  have h_nn : 0 ≤ 1 - (@inner ℝ _ _ u v / (‖u‖ * ‖v‖)) ^ 2 := by
    rw [sub_nonneg, div_pow, div_le_one (by positivity)]
    exact hcs
  -- Step 3: algebraic identity (1 - (inner/N)²) · N² = cross²
  have key : (1 - (@inner ℝ _ _ u v / (‖u‖ * ‖v‖)) ^ 2) * (‖u‖ * ‖v‖) ^ 2 =
             (cross2D u v) ^ 2 := by
    field_simp [hN_pos.ne']
    nlinarith [hlag, show (‖u‖ * ‖v‖) ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 from by ring]
  -- Step 4: combine — sqrt(1-c²) · N = sqrt((1-c²)·N²) = sqrt(cross²) = |cross|
  calc Real.sqrt (1 - (@inner ℝ _ _ u v / (‖u‖ * ‖v‖)) ^ 2) * (‖u‖ * ‖v‖)
      = Real.sqrt ((1 - (@inner ℝ _ _ u v / (‖u‖ * ‖v‖)) ^ 2) * (‖u‖ * ‖v‖) ^ 2) := by
            rw [Real.sqrt_mul h_nn, Real.sqrt_sq hN_nn]
    _ = Real.sqrt ((cross2D u v) ^ 2) := by rw [key]
    _ = |cross2D u v| := Real.sqrt_sq_eq_abs _

-- ============================================================
-- Part III: Triangle
-- ============================================================

structure Triangle where
  A B C : Vec2
  hNonDeg : cross2D (B - A) (C - A) ≠ 0

namespace Triangle

def a (t : Triangle) : ℝ := ‖t.C - t.B‖
def b (t : Triangle) : ℝ := ‖t.C - t.A‖
def c (t : Triangle) : ℝ := ‖t.B - t.A‖
def α (t : Triangle) : ℝ := InnerProductGeometry.angle (t.B - t.A) (t.C - t.A)
def β (t : Triangle) : ℝ := InnerProductGeometry.angle (t.A - t.B) (t.C - t.B)
def γ (t : Triangle) : ℝ := InnerProductGeometry.angle (t.A - t.C) (t.B - t.C)
def area (t : Triangle) : ℝ := |cross2D (t.B - t.A) (t.C - t.A)| / 2

lemma area_pos (t : Triangle) : 0 < t.area :=
  half_pos (abs_pos.mpr t.hNonDeg)

lemma hBA_ne (t : Triangle) : t.B - t.A ≠ 0 := by
  intro h; exact t.hNonDeg (by simp [cross2D, h])

lemma hCA_ne (t : Triangle) : t.C - t.A ≠ 0 := by
  intro h; exact t.hNonDeg (by simp [cross2D, h])

lemma hCB_ne (t : Triangle) : t.C - t.B ≠ 0 := by
  intro h
  apply t.hNonDeg
  have : t.C = t.B := sub_eq_zero.mp h
  rw [this]; exact cross2D_self _

lemma c_pos (t : Triangle) : 0 < t.c := norm_pos_iff.mpr t.hBA_ne
lemma b_pos (t : Triangle) : 0 < t.b := norm_pos_iff.mpr t.hCA_ne
lemma a_pos (t : Triangle) : 0 < t.a := norm_pos_iff.mpr t.hCB_ne

-- ============================================================
-- Part IV: Cross Product Sign Relations (by ring)
-- ============================================================

/-- cross2D for angle β = -cross2D for angle α. -/
lemma cross_β (t : Triangle) :
    cross2D (t.A - t.B) (t.C - t.B) = -cross2D (t.B - t.A) (t.C - t.A) := by
  simp only [cross2D, Pi.sub_apply]; ring

/-- cross2D for angle γ = cross2D for angle α. -/
lemma cross_γ (t : Triangle) :
    cross2D (t.A - t.C) (t.B - t.C) = cross2D (t.B - t.A) (t.C - t.A) := by
  simp only [cross2D, Pi.sub_apply]; ring

lemma abs_cross_β (t : Triangle) :
    |cross2D (t.A - t.B) (t.C - t.B)| = |cross2D (t.B - t.A) (t.C - t.A)| := by
  rw [cross_β]; exact abs_neg _

lemma abs_cross_γ (t : Triangle) :
    |cross2D (t.A - t.C) (t.B - t.C)| = |cross2D (t.B - t.A) (t.C - t.A)| := by
  rw [cross_γ]

-- ============================================================
-- Part V: Three Area Formulas
-- ============================================================

/-- **Area at A**: Area = (1/2) · c · b · sin(α). -/
theorem area_from_A (t : Triangle) :
    t.area = t.c * t.b * Real.sin t.α / 2 := by
  simp only [area, c, b, α]
  have h := sin_angle_mul_norms (t.B - t.A) (t.C - t.A) t.hBA_ne t.hCA_ne
  linarith [mul_comm (Real.sin (InnerProductGeometry.angle (t.B - t.A) (t.C - t.A)))
                     (‖t.B - t.A‖ * ‖t.C - t.A‖)]

/-- **Area at B**: Area = (1/2) · c · a · sin(β). -/
theorem area_from_B (t : Triangle) :
    t.area = t.c * t.a * Real.sin t.β / 2 := by
  simp only [area, c, a, β]
  have hAB : t.A - t.B ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr t.hBA_ne
  have h := sin_angle_mul_norms (t.A - t.B) (t.C - t.B) hAB t.hCB_ne
  have hn : ‖t.A - t.B‖ = ‖t.B - t.A‖ := norm_sub_rev _ _
  rw [hn] at h
  have hc := abs_cross_β t
  linarith [mul_comm (Real.sin (InnerProductGeometry.angle (t.A - t.B) (t.C - t.B)))
                     (‖t.B - t.A‖ * ‖t.C - t.B‖)]

/-- **Area at C**: Area = (1/2) · b · a · sin(γ). -/
theorem area_from_C (t : Triangle) :
    t.area = t.b * t.a * Real.sin t.γ / 2 := by
  simp only [area, b, a, γ]
  have hAC : t.A - t.C ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr t.hCA_ne
  have hBC : t.B - t.C ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr t.hCB_ne
  have h := sin_angle_mul_norms (t.A - t.C) (t.B - t.C) hAC hBC
  have hn1 : ‖t.A - t.C‖ = ‖t.C - t.A‖ := norm_sub_rev _ _
  have hn2 : ‖t.B - t.C‖ = ‖t.C - t.B‖ := norm_sub_rev _ _
  rw [hn1, hn2] at h
  have hc := abs_cross_γ t
  linarith [mul_comm (Real.sin (InnerProductGeometry.angle (t.A - t.C) (t.B - t.C)))
                     (‖t.C - t.A‖ * ‖t.C - t.B‖)]

-- ============================================================
-- Part VI: Sin Positivity
-- ============================================================

/-- sin(α) > 0: from sin_angle_mul_norms and cross ≠ 0. -/
lemma sinA_pos (t : Triangle) : 0 < Real.sin t.α := by
  simp only [α]
  have h := sin_angle_mul_norms (t.B - t.A) (t.C - t.A) t.hBA_ne t.hCA_ne
  have hcross : 0 < |cross2D (t.B - t.A) (t.C - t.A)| := abs_pos.mpr t.hNonDeg
  have hprod : 0 < ‖t.B - t.A‖ * ‖t.C - t.A‖ := mul_pos t.c_pos t.b_pos
  have hsin_prod : 0 < Real.sin (InnerProductGeometry.angle (t.B - t.A) (t.C - t.A))
                       * (‖t.B - t.A‖ * ‖t.C - t.A‖) := by linarith
  rcases mul_pos_iff.mp hsin_prod with ⟨hs, _⟩ | ⟨_, h1⟩
  · exact hs
  · linarith

/-- sin(β) > 0: from area_from_B > 0 and c, a > 0. -/
lemma sinB_pos (t : Triangle) : 0 < Real.sin t.β := by
  have hA := t.area_from_B
  have harea := t.area_pos
  have hca : 0 < t.c * t.a := mul_pos t.c_pos t.a_pos
  have h : 0 < t.c * t.a * Real.sin t.β := by linarith
  rcases mul_pos_iff.mp h with ⟨_, hs⟩ | ⟨h1, _⟩
  · exact hs
  · linarith

/-- sin(γ) > 0: from area_from_C > 0 and b, a > 0. -/
lemma sinC_pos (t : Triangle) : 0 < Real.sin t.γ := by
  have hC := t.area_from_C
  have harea := t.area_pos
  have hba : 0 < t.b * t.a := mul_pos t.b_pos t.a_pos
  have h : 0 < t.b * t.a * Real.sin t.γ := by linarith
  rcases mul_pos_iff.mp h with ⟨_, hs⟩ | ⟨h1, _⟩
  · exact hs
  · linarith

-- ============================================================
-- Part VII: Law of Sines
-- ============================================================

/-- **Law of Sines (a/sinα = b/sinβ)**: both equal (abc)/(2·Area). -/
theorem law_of_sines_ab (t : Triangle) :
    t.a / Real.sin t.α = t.b / Real.sin t.β := by
  rw [div_eq_div_iff t.sinA_pos.ne' t.sinB_pos.ne']
  -- goal: t.a * sinβ = t.b * sinα
  -- from area_from_A = area_from_B: c*b*sinα = c*a*sinβ → b*sinα = a*sinβ
  have h1 := t.area_from_A
  have h2 := t.area_from_B
  -- c * b * sinα / 2 = area = c * a * sinβ / 2
  -- → c * b * sinα = c * a * sinβ
  have heq : t.c * t.b * Real.sin t.α = t.c * t.a * Real.sin t.β := by linarith
  -- Rewrite associativity explicitly then cancel t.c
  have hc := t.c_pos.ne'
  have hr1 : t.c * t.b * Real.sin t.α = t.c * (t.b * Real.sin t.α) := by ring
  have hr2 : t.c * t.a * Real.sin t.β = t.c * (t.a * Real.sin t.β) := by ring
  have heq2 : t.c * (t.b * Real.sin t.α) = t.c * (t.a * Real.sin t.β) := by linarith
  have key : t.b * Real.sin t.α = t.a * Real.sin t.β := mul_left_cancel₀ hc heq2
  linarith

/-- **Law of Sines (a/sinα = c/sinγ)**: both equal (abc)/(2·Area). -/
theorem law_of_sines_ac (t : Triangle) :
    t.a / Real.sin t.α = t.c / Real.sin t.γ := by
  rw [div_eq_div_iff t.sinA_pos.ne' t.sinC_pos.ne']
  -- from area_from_A = area_from_C: c*b*sinα / 2 = b*a*sinγ / 2
  have h1 := t.area_from_A
  have h3 := t.area_from_C
  have heq : t.c * t.b * Real.sin t.α = t.b * t.a * Real.sin t.γ := by linarith
  have hb := t.b_pos.ne'
  have hr1 : t.c * t.b * Real.sin t.α = t.b * (t.c * Real.sin t.α) := by ring
  have hr2 : t.b * t.a * Real.sin t.γ = t.b * (t.a * Real.sin t.γ) := by ring
  have heq2 : t.b * (t.c * Real.sin t.α) = t.b * (t.a * Real.sin t.γ) := by linarith
  have key : t.c * Real.sin t.α = t.a * Real.sin t.γ := mul_left_cancel₀ hb heq2
  linarith

/-- **Law of Sines (full)**: a/sinα = b/sinβ = c/sinγ. -/
theorem law_of_sines (t : Triangle) :
    t.a / Real.sin t.α = t.b / Real.sin t.β ∧
    t.b / Real.sin t.β = t.c / Real.sin t.γ := by
  exact ⟨t.law_of_sines_ab, t.law_of_sines_ab.symm.trans t.law_of_sines_ac⟩

/-
## Summary

### Axioms (0)
No axioms. The sin-cross identity is proved from Mathlib primitives.

### Proved (no sorry, no axioms)
- `lagrange_2d`: ‖u‖²‖v‖² = ⟨u,v⟩² + (cross2D u v)² — ring in Fin 2 coords
- `sin_angle_mul_norms`: sin(angle u v)·‖u‖·‖v‖ = |cross2D u v|
  via: arccos → sin_arccos → sqrt(1-c²)·N = sqrt((1-c²)·N²) → Lagrange → sqrt_sq_eq_abs
- `cross_β`, `cross_γ`: sign relations by ring
- `hBA_ne`, `hCA_ne`, `hCB_ne`: vertex distinctness from non-degeneracy
- `area_from_A/B/C`: three equivalent area formulas
- `sinA/B/C_pos`: sin positivity from cross product / area
- `law_of_sines_ab`, `law_of_sines_ac`, `law_of_sines`: the main theorem

### Mathematical Content
Area = (1/2)cb sinα = (1/2)ca sinβ → cb sinα = ca sinβ → a/sinα = b/sinβ.
Algebra handled by ring_nf + linarith + mul_left_cancel₀.
-/

#check @Triangle.law_of_sines
#check @lagrange_2d

end Triangle

end LawOfSines

end
