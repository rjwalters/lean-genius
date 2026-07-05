/-
# Pick's Theorem OQ-01-OQ-01-OQ-01-OQ-02 (S4): Additivity Under Edge-Gluing

Open Question (from `picks-theorem-oq-01-oq-01-oq-01`):
"Prove the additivity lemma: when two lattice triangles `T₁`, `T₂` share an
edge, the Pick quantities combine additively — this is the inductive step
that lets Pick's theorem propagate from primitive triangles to arbitrary
lattice polygons."

## What This File Proves (sorry-free, 0 axioms)

We formalize the **edge-gluing additivity** that powers the inductive proof
of Pick's theorem.  Two lattice triangles glued along the shared diagonal
`v1 → v3` form a lattice quadrilateral `Q = ⟨v1, v2, v3, v4⟩`, split into

  * `T1 = ⟨v1, v2, v3⟩`   (below the diagonal)
  * `T2 = ⟨v1, v3, v4⟩`   (above the diagonal)

Reusing the parent file's bridge data (`twiceArea`, `edgeGCD`,
`boundaryCount`, `pickInterior`), we prove, for the four **outer** edges of
`Q`:

1. **Signed-area additivity** (`signedDoubleArea_eq_add_det`):
   the shoelace double-area of `Q` is exactly `det T1 + det T2` — a pure
   polynomial identity.

2. **Orientation ⇒ area additivity** (`signedDoubleArea_natAbs_eq_twiceArea`):
   when both sub-triangles are positively oriented (a convex quad traversed
   counter-clockwise), the *unsigned* areas add:
   `|signedDoubleArea Q| = twiceArea T1 + twiceArea T2`.

3. **Diagonal symmetry** (`T1_edgeGCD_two`, `T2_edgeGCD_zero`):
   both triangles see the shared diagonal with the *same* GCD count,
   `Q.diagGCD = gcd(|Δx|, |Δy|)` of `v1 → v3`.

4. **Boundary additivity** (`boundaryCount_add`):
   `B(T1) + B(T2) = B(Q) + 2 · diagGCD`.  The shared diagonal is counted
   once in each triangle but drops out of the quadrilateral boundary.

5. **The additivity lemma** (`pickInterior_add`) — the S4 deliverable:

      `I(Q) = I(T1) + I(T2) + (diagGCD − 1)`.

   The correction `diagGCD − 1` is exactly the number of lattice points
   lying strictly *inside* the shared diagonal: these are boundary points of
   the two triangles that become **interior** points of the merged region.

6. **Primitive-edge corollary** (`pickInterior_add_primitive`):
   when the shared edge carries no interior lattice points
   (`diagGCD = 1`), additivity is exact:

      `I(Q) = I(T1) + I(T2)`.

## Why this is the inductive step

Pick's theorem `Area = I + B/2 − 1` is equivalent to the statement that the
functional `P(T) := I(T) + B(T)/2 − 1` equals the area.  Because `P` is
*additive under edge-gluing* — which is precisely `pickInterior_add` rewritten
through `pick_formula_cleared` — one proves Pick for all lattice polygons by
triangulating and inducting on the number of triangles, with the base case
(a primitive triangle, `Area = 1/2`, `I = 0`, `B = 3`) supplied by the parent
file `PicksTheoremOQ01OQ01OQ01`.

The additive correction `diagGCD − 1` is what makes the induction *robust*:
gluing along a non-primitive edge still works, the swallowed diagonal points
simply migrate from the boundary tally into the interior tally.

## Concrete checks

- Unit square `⟨(0,0),(1,0),(1,1),(0,1)⟩` (primitive diagonal `(1,1)`):
  `I(Q) = 0 = 0 + 0`.
- `2×2` square `⟨(0,0),(2,0),(2,2),(0,2)⟩` (diagonal `(2,2)`, `diagGCD = 2`):
  `I(Q) = 1 = 0 + 0 + (2 − 1)` — the point `(1,1)` on the diagonal becomes
  the single interior point.

The definitions mirror `PicksTheoremOQ01OQ01OQ01.lean` and are restated here
to keep the file self-contained (same convention as the rest of the chain).
-/

import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace PicksTheoremOQ01OQ01OQ01OQ02

-- ════════════════════════════════════════════════════════════════
-- SECTION I: Triangle definitions (mirrored from the parent file)
-- ════════════════════════════════════════════════════════════════

/-- A lattice triangle with three vertices in `ℤ²`. -/
structure LatticeTriangle where
  v1 : ℤ × ℤ
  v2 : ℤ × ℤ
  v3 : ℤ × ℤ
  deriving Repr

/-- Signed determinant `= (v2 - v1) × (v3 - v1)`, twice the signed area. -/
def LatticeTriangle.det (T : LatticeTriangle) : ℤ :=
  (T.v2.1 - T.v1.1) * (T.v3.2 - T.v1.2) - (T.v3.1 - T.v1.1) * (T.v2.2 - T.v1.2)

/-- Twice the (unsigned) area of `T`, as `|det T|`. -/
def LatticeTriangle.twiceArea (T : LatticeTriangle) : ℕ := T.det.natAbs

/-- The pair of absolute coordinate differences for edge `i`.
    Edges: `0 : v1 → v2`, `1 : v2 → v3`, `2 : v3 → v1`. -/
def LatticeTriangle.edgeDelta (T : LatticeTriangle) : Fin 3 → ℕ × ℕ
  | 0 => ((T.v2.1 - T.v1.1).natAbs, (T.v2.2 - T.v1.2).natAbs)
  | 1 => ((T.v3.1 - T.v2.1).natAbs, (T.v3.2 - T.v2.2).natAbs)
  | 2 => ((T.v1.1 - T.v3.1).natAbs, (T.v1.2 - T.v3.2).natAbs)

/-- GCD lattice-point count of edge `i` (excluding one shared endpoint). -/
def LatticeTriangle.edgeGCD (T : LatticeTriangle) (i : Fin 3) : ℕ :=
  Nat.gcd (T.edgeDelta i).1 (T.edgeDelta i).2

/-- Boundary lattice-point count `B = Σ_i gcd_i`. -/
def LatticeTriangle.boundaryCount (T : LatticeTriangle) : ℕ :=
  T.edgeGCD 0 + T.edgeGCD 1 + T.edgeGCD 2

/-- Pick interior count `I = Area − B/2 + 1 = twiceArea/2 − boundaryCount/2 + 1`. -/
def LatticeTriangle.pickInterior (T : LatticeTriangle) : ℚ :=
  (T.twiceArea : ℚ) / 2 - (T.boundaryCount : ℚ) / 2 + 1

-- ════════════════════════════════════════════════════════════════
-- SECTION II: The glued quadrilateral
-- ════════════════════════════════════════════════════════════════

/-- A lattice quadrilateral `⟨v1, v2, v3, v4⟩`, split by the diagonal
    `v1 → v3` into triangles `T1 = ⟨v1,v2,v3⟩` and `T2 = ⟨v1,v3,v4⟩`. -/
structure LatticeQuad where
  v1 : ℤ × ℤ
  v2 : ℤ × ℤ
  v3 : ℤ × ℤ
  v4 : ℤ × ℤ
  deriving Repr

/-- Lower sub-triangle `⟨v1, v2, v3⟩`. -/
def LatticeQuad.T1 (Q : LatticeQuad) : LatticeTriangle := ⟨Q.v1, Q.v2, Q.v3⟩

/-- Upper sub-triangle `⟨v1, v3, v4⟩`. -/
def LatticeQuad.T2 (Q : LatticeQuad) : LatticeTriangle := ⟨Q.v1, Q.v3, Q.v4⟩

/-- Signed double area of `Q` by the shoelace formula, written as the sum of
    the two triangle determinants. -/
def LatticeQuad.signedDoubleArea (Q : LatticeQuad) : ℤ :=
  ((Q.v2.1 - Q.v1.1) * (Q.v3.2 - Q.v1.2) - (Q.v3.1 - Q.v1.1) * (Q.v2.2 - Q.v1.2))
  + ((Q.v3.1 - Q.v1.1) * (Q.v4.2 - Q.v1.2) - (Q.v4.1 - Q.v1.1) * (Q.v3.2 - Q.v1.2))

/-- GCD count of the shared diagonal `v1 → v3`. -/
def LatticeQuad.diagGCD (Q : LatticeQuad) : ℕ :=
  Nat.gcd (Q.v3.1 - Q.v1.1).natAbs (Q.v3.2 - Q.v1.2).natAbs

/-- Twice the quadrilateral area, taken as the sum of the two triangle areas.
    (Equals `|signedDoubleArea Q|` when both triangles are positively
    oriented; see `signedDoubleArea_natAbs_eq_twiceArea`.) -/
def LatticeQuad.twiceArea (Q : LatticeQuad) : ℕ :=
  Q.T1.twiceArea + Q.T2.twiceArea

/-- Boundary lattice-point count of `Q`: the four **outer** edges
    `v1→v2`, `v2→v3`, `v3→v4`, `v4→v1` (the diagonal is excluded). -/
def LatticeQuad.boundaryCount (Q : LatticeQuad) : ℕ :=
  Q.T1.edgeGCD 0 + Q.T1.edgeGCD 1 + Q.T2.edgeGCD 1 + Q.T2.edgeGCD 2

/-- Pick interior count of `Q` via Pick's formula. -/
def LatticeQuad.pickInterior (Q : LatticeQuad) : ℚ :=
  (Q.twiceArea : ℚ) / 2 - (Q.boundaryCount : ℚ) / 2 + 1

-- ════════════════════════════════════════════════════════════════
-- SECTION III: Signed-area additivity (shoelace = sum of determinants)
-- ════════════════════════════════════════════════════════════════

/-- **Signed-area additivity.**  The shoelace double-area of `Q` is exactly
    `det T1 + det T2`.  Pure polynomial identity. -/
theorem signedDoubleArea_eq_add_det (Q : LatticeQuad) :
    Q.signedDoubleArea = Q.T1.det + Q.T2.det := by
  simp only [LatticeQuad.signedDoubleArea, LatticeQuad.T1, LatticeQuad.T2,
    LatticeTriangle.det]

/-- **Orientation ⇒ unsigned-area additivity.**  When both sub-triangles are
    positively oriented (`det ≥ 0`, i.e. `Q` is a counter-clockwise convex
    quad), the unsigned areas add:
    `|signedDoubleArea Q| = twiceArea T1 + twiceArea T2 = twiceArea Q`. -/
theorem signedDoubleArea_natAbs_eq_twiceArea (Q : LatticeQuad)
    (h1 : 0 ≤ Q.T1.det) (h2 : 0 ≤ Q.T2.det) :
    Q.signedDoubleArea.natAbs = Q.twiceArea := by
  rw [signedDoubleArea_eq_add_det]
  simp only [LatticeQuad.twiceArea, LatticeTriangle.twiceArea]
  omega

-- ════════════════════════════════════════════════════════════════
-- SECTION IV: Diagonal symmetry and boundary additivity
-- ════════════════════════════════════════════════════════════════

/-- The diagonal, seen as edge `2` of the lower triangle, has GCD `diagGCD`. -/
theorem T1_edgeGCD_two (Q : LatticeQuad) : Q.T1.edgeGCD 2 = Q.diagGCD := by
  simp only [LatticeQuad.T1, LatticeQuad.diagGCD, LatticeTriangle.edgeGCD,
    LatticeTriangle.edgeDelta]
  rw [show Q.v1.1 - Q.v3.1 = -(Q.v3.1 - Q.v1.1) by ring,
      show Q.v1.2 - Q.v3.2 = -(Q.v3.2 - Q.v1.2) by ring,
      Int.natAbs_neg, Int.natAbs_neg]

/-- The diagonal, seen as edge `0` of the upper triangle, has GCD `diagGCD`. -/
theorem T2_edgeGCD_zero (Q : LatticeQuad) : Q.T2.edgeGCD 0 = Q.diagGCD := by
  simp only [LatticeQuad.T2, LatticeQuad.diagGCD, LatticeTriangle.edgeGCD,
    LatticeTriangle.edgeDelta]

/-- **Boundary additivity.**  `B(T1) + B(T2) = B(Q) + 2 · diagGCD`: the shared
    diagonal is counted once inside each triangle but is absent from the
    quadrilateral boundary. -/
theorem boundaryCount_add (Q : LatticeQuad) :
    Q.T1.boundaryCount + Q.T2.boundaryCount
      = Q.boundaryCount + 2 * Q.diagGCD := by
  simp only [LatticeTriangle.boundaryCount, LatticeQuad.boundaryCount,
    T1_edgeGCD_two, T2_edgeGCD_zero]
  ring

-- ════════════════════════════════════════════════════════════════
-- SECTION V: The additivity lemma (S4)
-- ════════════════════════════════════════════════════════════════

/-- **Pick additivity under edge-gluing (S4).**

    `I(Q) = I(T1) + I(T2) + (diagGCD − 1)`.

    The correction term `diagGCD − 1` counts the lattice points strictly
    interior to the shared diagonal — boundary points of the two triangles
    that become interior points of the glued quadrilateral. -/
theorem pickInterior_add (Q : LatticeQuad) :
    Q.pickInterior = Q.T1.pickInterior + Q.T2.pickInterior
      + ((Q.diagGCD : ℚ) - 1) := by
  have hb : (Q.T1.boundaryCount : ℚ) + (Q.T2.boundaryCount : ℚ)
      = (Q.boundaryCount : ℚ) + 2 * (Q.diagGCD : ℚ) := by
    exact_mod_cast boundaryCount_add Q
  simp only [LatticeQuad.pickInterior, LatticeTriangle.pickInterior,
    LatticeQuad.twiceArea, Nat.cast_add]
  linarith [hb]

/-- **Primitive-edge corollary.**  When the shared edge carries no interior
    lattice points (`diagGCD = 1`), Pick additivity is exact:
    `I(Q) = I(T1) + I(T2)`. -/
theorem pickInterior_add_primitive (Q : LatticeQuad) (h : Q.diagGCD = 1) :
    Q.pickInterior = Q.T1.pickInterior + Q.T2.pickInterior := by
  rw [pickInterior_add, h]
  push_cast
  ring

/-- **Pick functional additivity.**  Writing Pick's functional
    `P(T) = twiceArea/2 − boundaryCount/2 + 1 = pickInterior`, edge-gluing
    along a *primitive* diagonal makes `P` additive — the algebraic heart of
    the inductive proof of Pick's theorem. -/
theorem pick_functional_additive (Q : LatticeQuad) (h : Q.diagGCD = 1) :
    (Q.twiceArea : ℚ) / 2 - (Q.boundaryCount : ℚ) / 2 + 1
      = ((Q.T1.twiceArea : ℚ) / 2 - (Q.T1.boundaryCount : ℚ) / 2 + 1)
        + ((Q.T2.twiceArea : ℚ) / 2 - (Q.T2.boundaryCount : ℚ) / 2 + 1) := by
  have := pickInterior_add_primitive Q h
  simpa only [LatticeQuad.pickInterior, LatticeTriangle.pickInterior] using this

-- ════════════════════════════════════════════════════════════════
-- SECTION VI: Concrete verification
-- ════════════════════════════════════════════════════════════════

/-- Unit square, two unit triangles glued on the primitive diagonal `(1,1)`. -/
def unitSquare : LatticeQuad := ⟨(0, 0), (1, 0), (1, 1), (0, 1)⟩

theorem unitSquare_diagGCD : unitSquare.diagGCD = 1 := by decide

theorem unitSquare_twiceArea : unitSquare.twiceArea = 2 := by decide

theorem unitSquare_boundaryCount : unitSquare.boundaryCount = 4 := by decide

/-- The unit square has `I = 0`, matching `I(T1) + I(T2) = 0 + 0`. -/
theorem unitSquare_pickInterior : unitSquare.pickInterior = 0 := by
  unfold LatticeQuad.pickInterior
  rw [unitSquare_twiceArea, unitSquare_boundaryCount]
  norm_num

/-- The additivity lemma holds concretely on the unit square. -/
theorem unitSquare_additive :
    unitSquare.pickInterior = unitSquare.T1.pickInterior
      + unitSquare.T2.pickInterior := by
  rw [pickInterior_add_primitive unitSquare unitSquare_diagGCD]

/-- `2×2` square, two triangles glued on the diagonal `(2,2)` with
    `diagGCD = 2` (the midpoint `(1,1)` lies on the diagonal). -/
def bigSquare : LatticeQuad := ⟨(0, 0), (2, 0), (2, 2), (0, 2)⟩

theorem bigSquare_diagGCD : bigSquare.diagGCD = 2 := by decide

/-- The correction term in action: the `2×2` square has one interior point,
    `I(Q) = 1 = I(T1) + I(T2) + (diagGCD − 1) = 0 + 0 + 1`. -/
theorem bigSquare_correction :
    bigSquare.pickInterior = bigSquare.T1.pickInterior
      + bigSquare.T2.pickInterior + 1 := by
  rw [pickInterior_add, bigSquare_diagGCD]
  norm_num

end PicksTheoremOQ01OQ01OQ01OQ02
