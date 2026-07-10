/-
# Pythagorean Theorem OQ-01 (companion): The Rearrangement / Dissection Proof

## The Open Question

> *What's the simplest possible proof of the Pythagorean theorem?*

The Einstein similar-triangles argument (`PythagoreanTheoremOQ01.lean`) and Garfield's
trapezoid argument (`PythagoreanTheoremOQ01Garfield.lean`) are two classic answers. This
companion formalizes a third — the one most often reproduced as a single wordless picture
and, by many accounts, *the* simplest: the **rearrangement (dissection) proof**, known in
India as **Bhāskara's "Behold!" proof** and in China as the **xuán-tú** of the *Zhoubi
Suanjing*. It uses *no similar triangles, no altitude, and no trapezoid* — only the fact
that area is additive over a dissection, applied to a single square built from four copies
of the right triangle.

## The construction

Take a right triangle with legs `a`, `b` and hypotenuse `c`. Arrange four congruent
copies inside a large square of side `a + b`, one in each corner, so that their
hypotenuses bound a smaller, tilted square in the middle:

```
   D(0,a+b) ________________ C(a+b,a+b)
        |  \      T4       /|
        |    \           /  |
        |      P3(b,a+b)    |
        | T1 /  (tilted     \|
   P4(0,b) /    inner        P2(a+b,a)
        | /     square)   /  |
        |/      T2      \    |
   A(0,0)‾‾‾‾‾‾P1(a,0)‾‾‾‾‾‾ B(a+b,0)
```

The four corner triangles `T1 … T4` are the right triangle (legs `a`, `b`); the tilted
inner quadrilateral `P1 P2 P3 P4` has all four sides equal to the hypotenuse and all four
angles right, so it is a **square built on the hypotenuse**.

## The argument

The area of the large square is computed **two ways**:

* directly, it is `(a + b)²`;
* by dissection, it is the four triangles plus the inner square:
  `4 · (½ab) + c²`.

Equating, `(a + b)² = 2ab + c²`, and since `(a + b)² = a² + 2ab + b²`, the `2ab` cancels
and `c² = a² + b²`.

## What This File Proves (0 sorries, 0 axioms)

- **Layer 1 — the algebraic skeleton** (`dissection_skeleton`): *given* the two-ways area
  equation `(a+b)² = 4·(½ab) + q`, cancelling forces `q = a² + b²`. This is the entire
  logical content, coordinate-free.

- **Layer 2 — the plane primitives**: shoelace signed areas (`triArea`, `quadArea`),
  squared distance (`sqDist`), and the edge dot product (`dotAt`).

- **Layer 3 — the concrete tiling**: every piece is placed at explicit coordinates and its
  area is computed (`outer_area`, `corner_bl/br/tr/tl`, `inner_area`); the inner
  quadrilateral is shown to be a genuine square built on the hypotenuse
  (`inner_side_*_sq`, `inner_right_angle`, `hyp_is_inner_side`).

- **Capstone** (`area_two_ways`, `pythagorean_via_dissection`): the outer square equals the
  four triangles plus the square on the hypotenuse, and therefore the hypotenuse of a right
  triangle with legs `a`, `b` satisfies `c² = a² + b²`.

Everything is a polynomial identity over `ℝ`, discharged by `ring` / `linear_combination`;
no similar triangles and no square roots appear.
-/

import Mathlib.Tactic

namespace PythagoreanDissection

-- ============================================================
-- Layer 1: The algebraic skeleton — "compute the big square two ways"
-- ============================================================

/-- **The rearrangement argument, algebraically.**
The large square of side `a + b` is dissected into four copies of the right triangle
(each of area `½ab`) and the tilted inner square (area `q`, the square on the hypotenuse).
Its area is `(a + b)²` directly and `4·(½ab) + q` by dissection; equating and cancelling
the `2ab` forces the inner square's area to be `a² + b²`. This is the whole proof, with no
coordinates. -/
theorem dissection_skeleton {a b q : ℝ}
    (hdissect : (a + b) ^ 2 = 4 * (a * b / 2) + q) :
    q = a ^ 2 + b ^ 2 := by
  linear_combination -hdissect

-- ============================================================
-- Layer 2: Planar area and length primitives
-- ============================================================

/-- Signed area of the triangle with vertices `(x₁,y₁)`, `(x₂,y₂)`, `(x₃,y₃)` via the
shoelace formula. Positive for counter-clockwise orientation. -/
def triArea (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ) : ℝ :=
  ((x₁ * y₂ - x₂ * y₁) + (x₂ * y₃ - x₃ * y₂) + (x₃ * y₁ - x₁ * y₃)) / 2

/-- Signed area of the quadrilateral `(x₁,y₁) … (x₄,y₄)` (vertices in order) via the
shoelace formula. Positive for counter-clockwise orientation. -/
def quadArea (x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ℝ) : ℝ :=
  ((x₁ * y₂ - x₂ * y₁) + (x₂ * y₃ - x₃ * y₂)
    + (x₃ * y₄ - x₄ * y₃) + (x₄ * y₁ - x₁ * y₄)) / 2

/-- Squared Euclidean distance between two plane points. -/
def sqDist (x₁ y₁ x₂ y₂ : ℝ) : ℝ := (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2

/-- Inner product of the two edge vectors from apex `(ox,oy)` to `(px,py)` and `(qx,qy)`. -/
def dotAt (ox oy px py qx qy : ℝ) : ℝ := (px - ox) * (qx - ox) + (py - oy) * (qy - oy)

-- ============================================================
-- Layer 3: The concrete tiling in coordinates
--
-- Large square   A=(0,0)  B=(a+b,0)  C=(a+b,a+b)  D=(0,a+b)
-- Inner vertices  P1=(a,0)  P2=(a+b,a)  P3=(b,a+b)  P4=(0,b)
-- ============================================================

/-- Area of the large square `A B C D` of side `a + b`. -/
theorem outer_area (a b : ℝ) :
    quadArea 0 0 (a + b) 0 (a + b) (a + b) 0 (a + b) = (a + b) ^ 2 := by
  unfold quadArea; ring

/-- Bottom-left corner triangle `A P1 P4 = (0,0)(a,0)(0,b)`: legs `a`, `b`, area `½ab`. -/
theorem corner_bl (a b : ℝ) : triArea 0 0 a 0 0 b = a * b / 2 := by
  unfold triArea; ring

/-- Bottom-right corner triangle `B P2 P1 = (a+b,0)(a+b,a)(a,0)`: legs `a`, `b`, area `½ab`. -/
theorem corner_br (a b : ℝ) : triArea (a + b) 0 (a + b) a a 0 = a * b / 2 := by
  unfold triArea; ring

/-- Top-right corner triangle `C P3 P2 = (a+b,a+b)(b,a+b)(a+b,a)`: legs `a`, `b`, area `½ab`. -/
theorem corner_tr (a b : ℝ) : triArea (a + b) (a + b) b (a + b) (a + b) a = a * b / 2 := by
  unfold triArea; ring

/-- Top-left corner triangle `D P4 P3 = (0,a+b)(0,b)(b,a+b)`: legs `a`, `b`, area `½ab`. -/
theorem corner_tl (a b : ℝ) : triArea 0 (a + b) 0 b b (a + b) = a * b / 2 := by
  unfold triArea; ring

/-- Area of the tilted inner quadrilateral `P1 P2 P3 P4`. -/
theorem inner_area (a b : ℝ) :
    quadArea a 0 (a + b) a b (a + b) 0 b = a ^ 2 + b ^ 2 := by
  unfold quadArea; ring

-- The inner quadrilateral is a genuine square built on the hypotenuse. --

/-- Side `P1 P2` has squared length `a² + b²` (the hypotenuse squared). -/
theorem inner_side_12_sq (a b : ℝ) : sqDist a 0 (a + b) a = a ^ 2 + b ^ 2 := by
  unfold sqDist; ring

/-- Side `P2 P3` has squared length `a² + b²`. -/
theorem inner_side_23_sq (a b : ℝ) : sqDist (a + b) a b (a + b) = a ^ 2 + b ^ 2 := by
  unfold sqDist; ring

/-- Side `P3 P4` has squared length `a² + b²`. -/
theorem inner_side_34_sq (a b : ℝ) : sqDist b (a + b) 0 b = a ^ 2 + b ^ 2 := by
  unfold sqDist; ring

/-- Side `P4 P1` has squared length `a² + b²`. This side is exactly the hypotenuse of the
bottom-left corner triangle. -/
theorem inner_side_41_sq (a b : ℝ) : sqDist 0 b a 0 = a ^ 2 + b ^ 2 := by
  unfold sqDist; ring

/-- At vertex `P1` the two inner-square edges `P1→P2` and `P1→P4` are perpendicular, so the
inner quadrilateral has a right angle there (equal-length adjacent sides at a right angle
⟹ it is a square). -/
theorem inner_right_angle (a b : ℝ) : dotAt a 0 (a + b) a 0 b = 0 := by
  unfold dotAt; ring

/-- The hypotenuse of the corner right triangle `(0,0)(a,0)(0,b)` — the segment from
`P1 = (a,0)` to `P4 = (0,b)` — is the side `P4 P1` of the inner square, of squared length
`a² + b²`. -/
theorem hyp_is_inner_side (a b : ℝ) : sqDist a 0 0 b = sqDist 0 b a 0 := by
  unfold sqDist; ring

-- ============================================================
-- Capstone: area two ways ⟹ Pythagoras
-- ============================================================

/-- **The heart of the rearrangement proof: the big square, two ways.**
The area of the outer square equals the four corner triangles plus the square on the
hypotenuse (whose area is the squared side length `sqDist a 0 0 b = c²`). Concretely
`(a+b)² = 4·(½ab) + c²`. -/
theorem area_two_ways (a b : ℝ) :
    quadArea 0 0 (a + b) 0 (a + b) (a + b) 0 (a + b)
      = triArea 0 0 a 0 0 b + triArea (a + b) 0 (a + b) a a 0
        + triArea (a + b) (a + b) b (a + b) (a + b) a + triArea 0 (a + b) 0 b b (a + b)
        + sqDist a 0 0 b := by
  rw [outer_area, corner_bl, corner_br, corner_tr, corner_tl]
  unfold sqDist; ring

/-- **Pythagoras via rearrangement.**
For a right triangle with legs `a`, `b` placed at `(a,0)`–`(0,0)`–`(0,b)`, the hypotenuse
`(a,0)–(0,b)` has squared length `a² + b²`. The proof runs entirely through the dissection:
the outer square of side `a+b` is the four leg-triangles plus the square on the hypotenuse,
so that square's area — equal to the hypotenuse squared — is forced to be `a² + b²`. -/
theorem pythagorean_via_dissection (a b : ℝ) : sqDist a 0 0 b = a ^ 2 + b ^ 2 := by
  -- Two-ways area equation with the corner triangles already evaluated to `½ab`.
  have h := area_two_ways a b
  rw [outer_area, corner_bl, corner_br, corner_tr, corner_tl] at h
  -- `h : (a+b)² = ½ab + ½ab + ½ab + ½ab + sqDist a 0 0 b`; cancel to isolate the hypotenuse.
  exact dissection_skeleton (by linear_combination h)

end PythagoreanDissection
