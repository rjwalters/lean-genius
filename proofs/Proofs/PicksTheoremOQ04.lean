import Mathlib

/-!
# Pick's Theorem OQ-04: The General Shoelace Formula and its Integrality Bridge

## What This Proves

For a simple lattice polygon with vertices `(x₀,y₀), …, (x_{m-1},y_{m-1}) ∈ ℤ²`
(in cyclic order), the **shoelace (surveyor's) formula** computes twice its signed
area as

    S = Σ_{k} (x_k · y_{k+1} − x_{k+1} · y_k)        (indices mod m)

This file gives a *fully verified, axiom-free* formalization of the **general
n-gon** shoelace sum over an arbitrary vertex list, together with the structural
results that make it the right object:

1.  **Fan-triangulation bridge** (`shoelace_eq_fan`): the general shoelace sum
    equals the sum, over the fan triangles `(v₀, vᵢ, vᵢ₊₁)`, of the per-triangle
    determinant `cross2 v₀ vᵢ vᵢ₊₁`.  This is the exact lift of the gallery's
    proven *triangle* shoelace formula (`PicksTheoremOQ01.shoelaceTriangle`) to
    arbitrary `n`, and it is the heart of the file.  The proof rests on the
    algebraic identity `cross2 o a b = cross a b + cross b o − cross a o`, whose
    telescoping collapses the fan back to the closed edge sum.

2.  **Triangle reduction** (`shoelace_triangle`): for `n = 3` the formula
    reproduces the classical `x₁(y₂−y₃) + x₂(y₃−y₁) + x₃(y₁−y₂)`.

3.  **Translation invariance** (`shoelace_translate`): the shoelace sum depends
    only on the polygon's shape, not its position — an immediate corollary of the
    fan bridge plus the translation invariance of `cross2`.

4.  **Integrality bridge to Pick** (`pick_bridge`, `pick_bridge_iff`): the
    shoelace sum is, by construction, an **integer**, so the area `|S|/2` is always
    a half-integer.  For a lattice polygon whose Euclidean area equals its shoelace
    area, Pick's relation `A = i + b/2 − 1` is *equivalent* to the clean integer
    identity `|S| = 2i + b − 2`.  Both sides are the single integer `twiceArea`.

This is the arithmetic bridge between the combinatorial lattice-point count
(`i`, `b`) and the coordinate area, completing the coordinate-computable side of
Pick's theorem (#92 on Wiedijk's list of 100 theorems).

## Status
- [x] General n-gon shoelace sum over an arbitrary vertex list
- [x] Fan-triangulation bridge (general = Σ fan-triangle determinants)
- [x] Triangle reduction to the classical 3-vertex formula
- [x] Translation invariance
- [x] Integrality + Pick bridge `|S| = 2i + b − 2`
- [x] Concrete verification on triangle, square, and an L-shaped non-convex polygon
- 0 sorries, 0 axioms.

## Relation to the gallery
- `PicksTheorem.lean` — the base Pick relation `A = i + b/2 − 1`.
- `PicksTheoremOQ01.lean` — the *triangle* shoelace formula this generalizes.
- `PicksTheoremOQ01OQ01OQ01.lean` — the triangle bridge `2·Area = |det|`.

An exhaustive build-free numeric cross-check of all four claims (integrality, fan
bridge, triangle reduction, Pick agreement) on a battery of convex / non-convex /
collinear-edge lattice polygons lives in
`research/problems/picks-theorem-oq-04/verify_shoelace_integrality.py`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace PicksTheoremOQ04

/-- A lattice point: a pair of integers. -/
abbrev Pt := ℤ × ℤ

-- ============================================================
-- PART 1: The cross product and its triangle determinant
-- ============================================================

/-- The 2D wedge / cross product of two position vectors,
    `cross a b = x_a · y_b − y_a · x_b`.  This is the per-edge term of the
    shoelace sum: `cross (x_k, y_k) (x_{k+1}, y_{k+1}) = x_k y_{k+1} − x_{k+1} y_k`. -/
def cross (a b : Pt) : ℤ := a.1 * b.2 - a.2 * b.1

@[simp] lemma cross_self (a : Pt) : cross a a = 0 := by
  unfold cross; ring

/-- The cross product is antisymmetric: `cross a b = − cross b a`. -/
lemma cross_antisymm (a b : Pt) : cross a b = - cross b a := by
  unfold cross; ring

/-- Twice the signed area of triangle `(o, a, b)`: the determinant of the edge
    vectors `a − o` and `b − o`.  This is the per-triangle term of a fan
    triangulation. -/
def cross2 (o a b : Pt) : ℤ :=
  (a.1 - o.1) * (b.2 - o.2) - (a.2 - o.2) * (b.1 - o.1)

/-- **Key identity.**  The triangle determinant from apex `o` decomposes into
    closed-edge terms: `cross2 o a b = cross a b + cross b o − cross a o`.
    Summing this over a fan triangulation telescopes the `o`-terms away, which is
    exactly why the fan sum collapses to the closed shoelace sum. -/
lemma cross2_eq (o a b : Pt) :
    cross2 o a b = cross a b + cross b o - cross a o := by
  unfold cross2 cross; ring

-- ============================================================
-- PART 2: The shoelace sum of a closed polygon
-- ============================================================

/-- `shoelaceAux first vs` sums `cross` over consecutive vertices of `vs`, then
    closes the loop with the edge from the last vertex of `vs` back to `first`.
    The public entry point `shoelace` calls this with `first` equal to the first
    vertex, producing the genuine cyclic edge sum. -/
def shoelaceAux (first : Pt) : List Pt → ℤ
  | [] => 0
  | [a] => cross a first
  | a :: b :: t => cross a b + shoelaceAux first (b :: t)

/-- The signed shoelace sum of a closed polygon given by its vertex list in cyclic
    order:  `shoelace [v₀, …, v_{m-1}] = Σ_k cross(v_k, v_{k+1 mod m})`.

    Concretely, `shoelace [a, b, c] = cross a b + cross b c + cross c a`. -/
def shoelace : List Pt → ℤ
  | [] => 0
  | v0 :: rest => shoelaceAux v0 (v0 :: rest)

-- ============================================================
-- PART 3: The fan triangulation and the bridge theorem
-- ============================================================

/-- `fanAux o vs` sums the triangle determinants `cross2 o a b` over consecutive
    pairs `(a, b)` of `vs`.  For a polygon `v₀ :: rest`, `fanAux v₀ rest` is the
    fan triangulation from apex `v₀`: the triangles `(v₀, rᵢ, rᵢ₊₁)`. -/
def fanAux (o : Pt) : List Pt → ℤ
  | [] => 0
  | [_] => 0
  | a :: b :: t => cross2 o a b + fanAux o (b :: t)

/-- Bridging lemma between the open shoelace chain and the fan sum.  Peeling one
    edge at a time, `shoelaceAux o (a :: t)` differs from `fanAux o (a :: t)` by
    exactly the closing term `cross a o`.  Proved by induction on `t` with the
    leading vertex `a` universally quantified. -/
lemma shoelaceAux_eq_fanAux (o : Pt) (t : List Pt) :
    ∀ a : Pt, shoelaceAux o (a :: t) = fanAux o (a :: t) + cross a o := by
  induction t with
  | nil => intro a; simp [shoelaceAux, fanAux]
  | cons b t' ih =>
    intro a
    simp only [shoelaceAux, fanAux]
    rw [ih b, cross2_eq]
    ring

/-- **Fan-triangulation bridge (the headline result).**

    The general n-gon shoelace sum equals the sum of the per-triangle determinants
    of its fan triangulation from the first vertex:

        shoelace (v₀ :: rest) = Σ over triangles (v₀, rᵢ, rᵢ₊₁) of cross2 v₀ rᵢ rᵢ₊₁.

    This lifts the gallery's proven *triangle* shoelace formula to arbitrary `n`,
    and is the formal content of claim (II) of the problem statement. -/
theorem shoelace_eq_fan (v0 : Pt) (rest : List Pt) :
    shoelace (v0 :: rest) = fanAux v0 rest := by
  have h := shoelaceAux_eq_fanAux v0 rest v0
  have hshoe : shoelace (v0 :: rest) = shoelaceAux v0 (v0 :: rest) := rfl
  rw [hshoe, h, cross_self, add_zero]
  cases rest with
  | nil => rfl
  | cons r1 rs =>
    show cross2 v0 v0 r1 + fanAux v0 (r1 :: rs) = fanAux v0 (r1 :: rs)
    rw [show cross2 v0 v0 r1 = 0 from by simp [cross2], zero_add]

-- ============================================================
-- PART 4: Triangle reduction (claim III)
-- ============================================================

/-- **Triangle reduction.**  For three vertices the general shoelace sum is the
    classical signed-area numerator `x₁(y₂−y₃) + x₂(y₃−y₁) + x₃(y₁−y₂)`, matching
    `PicksTheoremOQ01.shoelaceTriangle` up to the absolute value. -/
theorem shoelace_triangle (a b c : Pt) :
    shoelace [a, b, c] =
      a.1 * (b.2 - c.2) + b.1 * (c.2 - a.2) + c.1 * (a.2 - b.2) := by
  show shoelaceAux a [a, b, c] = _
  simp only [shoelaceAux, cross]
  ring

/-- The fan triangulation of a triangle is the single triangle determinant. -/
theorem shoelace_triangle_fan (a b c : Pt) :
    shoelace [a, b, c] = cross2 a b c := by
  rw [show ([a, b, c] : List Pt) = a :: [b, c] from rfl, shoelace_eq_fan]
  simp [fanAux]

-- ============================================================
-- PART 5: Translation invariance (claim: shape, not position)
-- ============================================================

/-- Translate a single lattice point by `d`. -/
def shift (d p : Pt) : Pt := (p.1 + d.1, p.2 + d.2)

/-- Translate every vertex of a polygon by `d`. -/
def translate (d : Pt) (vs : List Pt) : List Pt := vs.map (shift d)

/-- The triangle determinant is translation invariant (it depends only on edge
    differences). -/
lemma cross2_translate (d o a b : Pt) :
    cross2 (shift d o) (shift d a) (shift d b) = cross2 o a b := by
  simp only [cross2, shift]; ring

/-- The fan sum is translation invariant. -/
lemma fanAux_translate (d o : Pt) :
    ∀ l : List Pt, fanAux (shift d o) (translate d l) = fanAux o l := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' =>
      show cross2 (shift d o) (shift d a) (shift d b)
            + fanAux (shift d o) (translate d (b :: t'))
          = cross2 o a b + fanAux o (b :: t')
      rw [cross2_translate, ih]

/-- **Translation invariance.**  The shoelace sum is unchanged by translating the
    whole polygon — it measures shape, not position.  Immediate from the fan
    bridge and the translation invariance of `cross2`. -/
theorem shoelace_translate (d : Pt) (vs : List Pt) :
    shoelace (translate d vs) = shoelace vs := by
  cases vs with
  | nil => rfl
  | cons v0 rest =>
    show shoelace (shift d v0 :: translate d rest) = shoelace (v0 :: rest)
    rw [shoelace_eq_fan, shoelace_eq_fan, fanAux_translate]

-- ============================================================
-- PART 6: Integrality and the bridge to Pick's theorem (claims I, IV)
-- ============================================================

/-- Twice the unsigned area of the polygon: `|S|`.  By construction an integer,
    hence the area `twiceArea/2` is always a half-integer (claim I). -/
def twiceArea (vs : List Pt) : ℤ := |shoelace vs|

/-- The (Euclidean) area as a rational, `|S|/2`. -/
def area (vs : List Pt) : ℚ := (twiceArea vs : ℚ) / 2

theorem twiceArea_nonneg (vs : List Pt) : 0 ≤ twiceArea vs := abs_nonneg _

theorem two_mul_area (vs : List Pt) : 2 * area vs = (twiceArea vs : ℚ) := by
  unfold area; ring

/-- **Integrality bridge to Pick (claim IV).**  For a simple lattice polygon whose
    Euclidean area equals its shoelace area, Pick's relation `A = i + b/2 − 1`
    forces the clean integer identity `2·Area = |S| = 2i + b − 2`.  This is the
    arithmetic bridge tying the coordinate area to the lattice-point counts. -/
theorem pick_bridge (vs : List Pt) (i b : ℕ)
    (hpick : area vs = (i : ℚ) + (b : ℚ) / 2 - 1) :
    twiceArea vs = 2 * (i : ℤ) + (b : ℤ) - 2 := by
  have h2 : (twiceArea vs : ℚ) = 2 * (i : ℚ) + (b : ℚ) - 2 := by
    rw [← two_mul_area, hpick]; ring
  exact_mod_cast h2

/-- The bridge is an equivalence: Pick's relation and the integer identity carry
    the same content, namely the value of `twiceArea`. -/
theorem pick_bridge_iff (vs : List Pt) (i b : ℕ) :
    area vs = (i : ℚ) + (b : ℚ) / 2 - 1 ↔
      twiceArea vs = 2 * (i : ℤ) + (b : ℤ) - 2 := by
  constructor
  · exact pick_bridge vs i b
  · intro h
    have hq : (twiceArea vs : ℚ) = 2 * (i : ℚ) + (b : ℚ) - 2 := by exact_mod_cast h
    have : 2 * area vs = 2 * (i : ℚ) + (b : ℚ) - 2 := by rw [two_mul_area]; exact hq
    linarith

-- ============================================================
-- PART 7: Concrete verification (matching verify_shoelace_integrality.py)
-- ============================================================

/-- Unit right triangle `(0,0),(1,0),(0,1)`: `S = 1`, area `1/2`. -/
example : shoelace [(0, 0), (1, 0), (0, 1)] = 1 := by decide

/-- Right triangle `(0,0),(3,0),(0,3)`: `S = 9`, area `9/2`. -/
example : shoelace [(0, 0), (3, 0), (0, 3)] = 9 := by decide

/-- `3 × 4` rectangle: `S = 24`, area `12`. -/
example : shoelace [(0, 0), (3, 0), (3, 4), (0, 4)] = 24 := by decide

/-- L-shaped non-convex hexagon: `S = 24`, area `12`. -/
example :
    shoelace [(0, 0), (4, 0), (4, 2), (2, 2), (2, 4), (0, 4)] = 24 := by decide

/-- **Concrete Pick agreement, unit triangle.**  `i = 0`, `b = 3`, so
    `2i + b − 2 = 1 = twiceArea`. -/
example : twiceArea [(0, 0), (1, 0), (0, 1)] = 2 * (0 : ℤ) + 3 - 2 := by
  have h : shoelace [(0, 0), (1, 0), (0, 1)] = 1 := by decide
  unfold twiceArea; rw [h]; norm_num

/-- **Concrete Pick agreement, `3 × 4` rectangle.**  Interior count
    `i = 2·3 = 6`, boundary count `b = 2·(3+4) = 14`, so
    `2i + b − 2 = 24 = twiceArea`. -/
example : twiceArea [(0, 0), (3, 0), (3, 4), (0, 4)] = 2 * (6 : ℤ) + 14 - 2 := by
  have h : shoelace [(0, 0), (3, 0), (3, 4), (0, 4)] = 24 := by decide
  unfold twiceArea; rw [h]; norm_num

/-- **Concrete Pick agreement, L-shaped hexagon.**  Interior count `i = 5`,
    boundary count `b = 16`, so `2i + b − 2 = 24 = twiceArea`. -/
example :
    twiceArea [(0, 0), (4, 0), (4, 2), (2, 2), (2, 4), (0, 4)]
      = 2 * (5 : ℤ) + 16 - 2 := by
  have h : shoelace [(0, 0), (4, 0), (4, 2), (2, 2), (2, 4), (0, 4)] = 24 := by
    decide
  unfold twiceArea; rw [h]; norm_num

end PicksTheoremOQ04
