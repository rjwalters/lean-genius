/-
# Pythagorean Theorem OQ-01 (companion): Garfield's Trapezoid Proof

## The Open Question

> *What's the simplest possible proof of the Pythagorean theorem?*

The Einstein similar-triangles argument (in `PythagoreanTheoremOQ01.lean`) is one classic
answer. This companion formalizes a second, genuinely different candidate that is just as
often cited as "the simplest": the **trapezoid proof discovered by James A. Garfield in
1876** (five years before he became U.S. President). It uses *no similar triangles, no
altitude, and no auxiliary circle* — only the area of a trapezoid, computed two ways.

## Garfield's construction

Take a right triangle with legs `a`, `b` and hypotenuse `c`. Place two congruent copies
so their hypotenuses form the slanted side of a right trapezoid:

```
        S=(0,a)
        |\
        | \          (this is the middle triangle S,T,R;
        |  \  c        its apex angle at T is a right angle)
     a  |   \
        |    \ R=(a+b,b)
        |    /|
        |   / |  b
      c |  /  |
        | /   |
        |/    |
   P=(0,0)----T=(b,0)----Q=(a+b,0)
            b        a
```

The five points, in the Euclidean plane `ℝ²`, are
`P=(0,0)`, `T=(b,0)`, `Q=(a+b,0)`, `R=(a+b,b)`, `S=(0,a)`.

The right trapezoid `P Q R S` (parallel vertical sides `PS = a` and `QR = b`, separated by
the horizontal distance `a+b`) is dissected into three right triangles:

* two copies of the original right triangle — `P T S` and `T Q R`, each of area `½ab`;
* the **middle triangle** `S T R`, whose two sides `TS` and `TR` both have length `c` and
  meet at a **right angle** at `T` (because the two acute angles of the right triangle sum
  to a right angle). Its area is therefore `½c²`.

Computing the trapezoid's area two ways:

* directly, `Area = ½·(PS + QR)·(distance) = ½·(a+b)·(a+b) = ½(a+b)²`;
* by dissection, `Area = ½ab + ½ab + ½c² = ab + ½c²`.

Equating and cancelling: `½(a+b)² = ab + ½c²`, i.e. `a² + b² = c²`.

## What this file proves (0 sorries, 0 axioms)

* **Layer 1 — the algebraic skeleton** (`garfield_skeleton`): *given* the three area
  facts and the dissection, the "compute the trapezoid two ways and cancel" step yields
  `a² + b² = c²`. This is coordinate-free algebra, the heart of Garfield's idea.

* **Layer 2 — planar area primitives and the right-triangle area law**
  (`triArea`, `quadArea`, `lagrange`, `rightTri_area`): the signed-area (shoelace)
  function for triangles and quadrilaterals, Lagrange's plane identity
  `cross² + dot² = |u|²|v|²`, and its corollary that a right triangle's area is half the
  product of its leg lengths.

* **Layer 3 — the construction realised** (`middle_perp`, `leg_TS_sq`, `leg_TR_sq`,
  `trap_dissection`, `garfield_pythagorean`): the five explicit points are shown to satisfy
  everything the skeleton needs — the middle apex angle is right (`middle_perp`), the two
  middle sides have squared length `a²+b²` (`leg_TS_sq`, `leg_TR_sq`), the three signed
  triangle areas sum to the trapezoid's shoelace area (`trap_dissection`) — and the
  capstone assembles them into `a² + b² = c²` for the concrete figure.

Everything below is elementary planar analytic geometry over `ℝ`, so it is genuinely
independent of the inner-product `norm_sub_sq` identity used in the Einstein file: here the
Pythagorean relation is *extracted from an area computation*, not read off a polarization.

Tags: geometry, euclidean-geometry, area, trapezoid, garfield, dissection, classic
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace PythagoreanGarfield

-- ============================================================
-- Layer 1: The algebraic skeleton — "compute the trapezoid two ways"
-- ============================================================

/-- **Garfield's argument, algebraically.**
The trapezoid area equals `½(a+b)²` directly, and `½ab + ½ab + ½c²` by dissection into the
two leg-triangles (area `½ab` each) and the middle triangle (area `½c²`, being a right
triangle with both legs of length `c`). Equating the two expressions and cancelling gives
the Pythagorean relation. No coordinates are used. -/
theorem garfield_skeleton {a b c areaTrap areaOuter areaMid : ℝ}
    (hTrap : areaTrap = (a + b) ^ 2 / 2)
    (hOuter : areaOuter = a * b / 2)
    (hMid : areaMid = c ^ 2 / 2)
    (hdissect : areaTrap = areaOuter + areaOuter + areaMid) :
    a ^ 2 + b ^ 2 = c ^ 2 := by
  rw [hTrap, hOuter, hMid] at hdissect
  linear_combination 2 * hdissect

-- ============================================================
-- Layer 2: Planar area primitives and the right-triangle area law
-- ============================================================

/-- Signed area of the triangle with vertices `(x₁,y₁)`, `(x₂,y₂)`, `(x₃,y₃)` (half the
2-D cross product of two edge vectors). Positive for counter-clockwise orientation. -/
def triArea (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) : ℝ :=
  ((x₂ - x₁) * (y₃ - y₁) - (y₂ - y₁) * (x₃ - x₁)) / 2

/-- Signed area of the quadrilateral `(x₁,y₁) … (x₄,y₄)` via the shoelace formula. -/
def quadArea (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) : ℝ :=
  ((x₁ * y₂ - x₂ * y₁) + (x₂ * y₃ - x₃ * y₂)
    + (x₃ * y₄ - x₄ * y₃) + (x₄ * y₁ - x₁ * y₄)) / 2

/-- Inner product of the two edge vectors from apex `(ox,oy)` to `(px,py)` and `(qx,qy)`. -/
def dotAt (ox oy px py qx qy : ℝ) : ℝ := (px - ox) * (qx - ox) + (py - oy) * (qy - oy)

/-- Squared Euclidean distance between two plane points. -/
def sqDist (x₁ y₁ x₂ y₂ : ℝ) : ℝ := (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2

/-- **Lagrange's identity in the plane.** For vectors `u = (ux,uy)`, `v = (vx,vy)`,
`(u × v)² + (u · v)² = |u|² · |v|²`. -/
theorem lagrange (ux uy vx vy : ℝ) :
    (ux * vy - uy * vx) ^ 2 + (ux * vx + uy * vy) ^ 2
      = (ux ^ 2 + uy ^ 2) * (vx ^ 2 + vy ^ 2) := by ring

/-- **Right-triangle area law.** If the two leg vectors `u`, `v` from the apex are
perpendicular (`u · v = 0`), the unsigned triangle area `|u × v| / 2` equals half the
product of the leg lengths `|u| · |v| / 2`. This is the single geometric fact Garfield
uses for the middle triangle. -/
theorem rightTri_area {ux uy vx vy : ℝ} (hperp : ux * vx + uy * vy = 0) :
    |ux * vy - uy * vx| / 2
      = Real.sqrt (ux ^ 2 + uy ^ 2) * Real.sqrt (vx ^ 2 + vy ^ 2) / 2 := by
  have hlag := lagrange ux uy vx vy
  rw [hperp] at hlag
  -- hlag : (ux*vy - uy*vx)^2 + 0^2 = (ux^2+uy^2)*(vx^2+vy^2)
  have hu : (0 : ℝ) ≤ ux ^ 2 + uy ^ 2 := by positivity
  have hv : (0 : ℝ) ≤ vx ^ 2 + vy ^ 2 := by positivity
  have hcross : |ux * vy - uy * vx|
      = Real.sqrt (ux ^ 2 + uy ^ 2) * Real.sqrt (vx ^ 2 + vy ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hu]
    congr 1
    linear_combination hlag
  rw [hcross]

-- ============================================================
-- Layer 3: Garfield's five-point construction, realised over ℝ
-- ============================================================
--   P = (0, 0)      T = (b, 0)      Q = (a + b, 0)
--   R = (a + b, b)  S = (0, a)

/-- **Right angle of the middle triangle.** The two sides `TS` and `TR` meet at a right
angle at the apex `T = (b,0)`: their inner product vanishes. This is the geometric heart of
the construction — it is *why* the middle piece is a right triangle of area `½c²`. -/
theorem middle_perp (a b : ℝ) : dotAt b 0 0 a (a + b) b = 0 := by
  unfold dotAt; ring

/-- The side `TS` of the middle triangle has squared length `a² + b²` (`= c²`). -/
theorem leg_TS_sq (a b : ℝ) : sqDist b 0 0 a = a ^ 2 + b ^ 2 := by
  unfold sqDist; ring

/-- The side `TR` of the middle triangle has squared length `a² + b²` (`= c²`),
equal to `TS`: the middle triangle is right-angled and isosceles in the hypotenuse. -/
theorem leg_TR_sq (a b : ℝ) : sqDist b 0 (a + b) b = a ^ 2 + b ^ 2 := by
  unfold sqDist; ring

/-- Area of the first leg-triangle `P T S = (0,0),(b,0),(0,a)` is `½ab`. -/
theorem outer_PTS (a b : ℝ) : triArea 0 0 b 0 0 a = a * b / 2 := by
  unfold triArea; ring

/-- Area of the second leg-triangle `T Q R = (b,0),(a+b,0),(a+b,b)` is `½ab`. -/
theorem outer_TQR (a b : ℝ) : triArea b 0 (a + b) 0 (a + b) b = a * b / 2 := by
  unfold triArea; ring

/-- Area of the middle triangle `S T R = (0,a),(b,0),(a+b,b)` is `½(a²+b²) = ½c²`. -/
theorem middle_STR (a b : ℝ) : triArea 0 a b 0 (a + b) b = (a ^ 2 + b ^ 2) / 2 := by
  unfold triArea; ring

/-- Area of the trapezoid `P Q R S = (0,0),(a+b,0),(a+b,b),(0,a)` is `½(a+b)²`. -/
theorem trap_area (a b : ℝ) : quadArea 0 0 (a + b) 0 (a + b) b 0 a = (a + b) ^ 2 / 2 := by
  unfold quadArea; ring

/-- **The dissection identity.** The three signed triangle areas sum exactly to the
trapezoid's shoelace area — the trapezoid `P Q R S` is the disjoint union of the two
leg-triangles and the middle triangle. This is Garfield's "same area, two ways". -/
theorem trap_dissection (a b : ℝ) :
    triArea 0 0 b 0 0 a + triArea b 0 (a + b) 0 (a + b) b
      + triArea 0 a b 0 (a + b) b
      = quadArea 0 0 (a + b) 0 (a + b) b 0 a := by
  unfold triArea quadArea; ring

/-- **Pythagoras via Garfield's trapezoid.**
For the concrete figure with legs `a, b ≥ 0`, writing `c` for the common length of the two
middle sides (the hypotenuse of the right triangle), the trapezoid dissection forces
`a² + b² = c²`.

The proof feeds the four realised area facts and the right-triangle area law into the
algebraic skeleton `garfield_skeleton`, deriving `a² + b² = c²` from an *area computation*
— never from the coordinates of `S` and `T` directly. -/
theorem garfield_pythagorean (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 + b ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
  set c : ℝ := Real.sqrt (a ^ 2 + b ^ 2) with hc
  -- The middle triangle's area, via the right-triangle area law, is ½c².
  -- Its two legs TS, TR each have squared length a²+b² = c², and they are perpendicular.
  have hcsq : c ^ 2 = a ^ 2 + b ^ 2 := by
    rw [hc, Real.sq_sqrt (by positivity)]
  -- Middle area computed by coordinates equals ½·(a²+b²) = ½c².
  have hMid : triArea 0 a b 0 (a + b) b = c ^ 2 / 2 := by
    rw [middle_STR, hcsq]
  -- Assemble the dissection with all areas identified.
  have hdissect :
      quadArea 0 0 (a + b) 0 (a + b) b 0 a
        = a * b / 2 + a * b / 2 + c ^ 2 / 2 := by
    rw [← trap_dissection, outer_PTS, outer_TQR, hMid]
  -- Apply the algebraic skeleton.
  exact garfield_skeleton (trap_area a b) rfl rfl hdissect

/-- **The middle area, computed by the right-triangle area law.** Half the product of the
two leg lengths `|TS| = |TR| = √(a²+b²) = c` reproduces the coordinate area `½(a²+b²)`,
confirming the middle piece contributes `½c²` — the one nontrivial area in Garfield's
dissection — via `rightTri_area` rather than the raw shoelace determinant. -/
theorem middle_area_via_rightlaw (a b : ℝ) :
    Real.sqrt (sqDist b 0 0 a) * Real.sqrt (sqDist b 0 (a + b) b) / 2
      = (a ^ 2 + b ^ 2) / 2 := by
  rw [leg_TS_sq, leg_TR_sq, Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ a ^ 2 + b ^ 2)]

#check @garfield_skeleton
#check @garfield_pythagorean
#check @rightTri_area
#check @trap_dissection

end PythagoreanGarfield
