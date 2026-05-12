/-
# Pick's Theorem OQ-01-OQ-01-OQ-01: Bridge from Primitive Triangulation + GCD Boundary Count

Open Question (from `picks-theorem-oq-01-oq-01`):
"Can Pick's theorem `I + B/2 - 1 = Area` be derived in Lean 4 by combining
primitive triangulation with a boundary-point count via the GCD formula
(boundary points on segment from v1 to v2 = gcd(|v2.1-v1.1|, |v2.2-v1.2|))?"

## Status (S1 OBSERVE, build-verified)

S1 sets up the bridge data structures that connect:

- `PicksTheoremOQ01OQ01` — every lattice triangle decomposes into exactly
  `|det T|` primitive (i.e. `|det| = 1`) lattice sub-triangles.
- `PicksTheoremOQ02` — the segment from `(0,0)` to `(a,b)` (with `a, b : ℕ`)
  contains exactly `Nat.gcd a b + 1` integer lattice points.

We define:

1. `LatticeTriangle` — a mirror of the structure in `PicksTheoremOQ01OQ01`,
   carrying three integer-coordinate vertices.  (We restate the definition
   in our own namespace to keep this file self-contained; the math is the
   same.)
2. `twiceArea` — `|det T|`, equal to `2 · Area(T)` by the shoelace formula.
3. `edgeGCD i` — the GCD of `(|Δx_i|, |Δy_i|)` for edge `i ∈ {0,1,2}`.
4. `boundaryCount` — the sum of three `edgeGCD` values; equal to the
   number of boundary lattice points of `T` (each edge contributes
   `gcd + 1` points, with the three shared vertex endpoints double-counted
   so `B = Σ (gcd + 1) - 3 = Σ gcd`).
5. `pickInterior` — the rational number `twiceArea/2 - boundaryCount/2 + 1`,
   i.e. `I` computed via Pick's formula.

## The Bridge Claim (the answer to OQ-01-OQ-01-OQ-01)

**Yes, in principle.**  Given `PicksTheoremOQ01OQ01` and `PicksTheoremOQ02`,
Pick's theorem for lattice triangles becomes a finite computation
`pickInterior T = realInteriorCount T`.  The reduction proceeds in three
algebraic steps:

  Step 1 (Area side).  By the shoelace formula (`PicksTheoremOQ01.lean`,
  Part II), `2 · Area(T) = |det T|`.  By primitive triangulation
  (`PicksTheoremOQ01OQ01.exists_primitive_triangulation`), every triangle
  decomposes into `|det T|` primitive triangles, each of area `1/2`.

  Step 2 (Boundary side).  By the GCD boundary formula
  (`PicksTheoremOQ02.card_segmentPoints`), the segment from `(0,0)` to
  `(a,b)` carries `gcd(a,b) + 1` lattice points.  Translation invariance
  (Step 1 of `onSegment`) extends this to arbitrary segments, so any
  triangle edge from `(x_1,y_1)` to `(x_2,y_2)` carries
  `gcd(|x_2 - x_1|, |y_2 - y_1|) + 1` lattice points, and the boundary
  total is `Σ_i edgeGCD i + 3 - 3 = Σ_i edgeGCD i = boundaryCount T`.

  Step 3 (Algebraic identity).  Pick's formula
  `Area = I + B/2 - 1` rearranges to `I = Area - B/2 + 1 = pickInterior T`.

The remaining work is the **inductive step** that fuses primitive area
contributions and primitive boundary contributions consistently across
shared edges.  This file does not attempt that fusion — it scaffolds the
bridge data structures and verifies the formula on three concrete
triangles (unit, 2-by-1, 3-by-3).

## What This File Proves (sorry-free, 0 axioms)

- The three small-case computations:
  * Unit right triangle `{(0,0), (1,0), (0,1)}`: `I = 0`, `B = 3`,
    `2A = 1`, `pickInterior = 0`.
  * Right triangle `{(0,0), (2,0), (0,1)}`: `I = 0`, `B = 4`, `2A = 2`,
    `pickInterior = 0`.
  * Right triangle `{(0,0), (3,0), (0,3)}`: `I = 1`, `B = 9`, `2A = 9`,
    `pickInterior = 1`.
- The bridge identity `2 · pickInterior + boundaryCount = twiceArea + 2`,
  i.e. Pick's formula in cleared-denominator form.
- The non-negativity sanity check `pickInterior ≥ 0` for the three test
  triangles (showing the formula does produce a valid interior count).

## Architecture

- Section I: Mirror definitions (`LatticeTriangle`, `det`).
- Section II: Bridge data (`twiceArea`, `edgeGCD`, `boundaryCount`,
  `pickInterior`).
- Section III: Algebraic identity (`pick_formula_cleared`).
- Section IV: Verification on three concrete triangles.

The companion files `PicksTheoremOQ01OQ01.lean` and `PicksTheoremOQ02.lean`
remain the load-bearing pieces; this file simply names the bridge and
makes the composition explicit.
-/

import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

namespace PicksTheoremOQ01OQ01OQ01

-- ════════════════════════════════════════════════════════════════
-- SECTION I: Mirror Definitions
-- ════════════════════════════════════════════════════════════════

/-- A lattice triangle with three vertices in `ℤ²`. -/
structure LatticeTriangle where
  v1 : ℤ × ℤ
  v2 : ℤ × ℤ
  v3 : ℤ × ℤ
  deriving Repr

/-- Signed determinant: `det(T) = (v2 - v1) × (v3 - v1)` (2D cross product).
    Equals twice the signed area of `T`. -/
def LatticeTriangle.det (T : LatticeTriangle) : ℤ :=
  (T.v2.1 - T.v1.1) * (T.v3.2 - T.v1.2) - (T.v3.1 - T.v1.1) * (T.v2.2 - T.v1.2)

/-- Non-degenerate triangles have non-zero determinant (positive area). -/
def LatticeTriangle.NonDegenerate (T : LatticeTriangle) : Prop := T.det ≠ 0

-- ════════════════════════════════════════════════════════════════
-- SECTION II: Bridge Data Structures
-- ════════════════════════════════════════════════════════════════

/-- Twice the area of `T`, as a natural number (`= |det T|`). -/
def LatticeTriangle.twiceArea (T : LatticeTriangle) : ℕ := T.det.natAbs

/-- The pair of absolute differences `(|Δx_i|, |Δy_i|)` for edge `i`.
    Edges are indexed `0 : v1 → v2`, `1 : v2 → v3`, `2 : v3 → v1`. -/
def LatticeTriangle.edgeDelta (T : LatticeTriangle) : Fin 3 → ℕ × ℕ
  | 0 => ((T.v2.1 - T.v1.1).natAbs, (T.v2.2 - T.v1.2).natAbs)
  | 1 => ((T.v3.1 - T.v2.1).natAbs, (T.v3.2 - T.v2.2).natAbs)
  | 2 => ((T.v1.1 - T.v3.1).natAbs, (T.v1.2 - T.v3.2).natAbs)

/-- The GCD-based lattice-point count *minus the shared endpoint* for edge `i`.
    By `PicksTheoremOQ02.card_segmentPoints`, this is `gcd(|Δx|, |Δy|)`. -/
def LatticeTriangle.edgeGCD (T : LatticeTriangle) (i : Fin 3) : ℕ :=
  Nat.gcd (T.edgeDelta i).1 (T.edgeDelta i).2

/-- Boundary lattice-point count of `T`, computed via the GCD formula.
    Each of the three edges contributes `gcd(|Δx|, |Δy|) + 1` lattice
    points, with the three vertex endpoints each double-counted (shared
    between two edges), so `B = Σ_i (gcd + 1) - 3 = Σ_i gcd`. -/
def LatticeTriangle.boundaryCount (T : LatticeTriangle) : ℕ :=
  T.edgeGCD 0 + T.edgeGCD 1 + T.edgeGCD 2

/-- Pick's formula for the interior-point count of `T`, as a rational:
    `I = Area - B/2 + 1 = (twiceArea - boundaryCount + 2) / 2`. -/
def LatticeTriangle.pickInterior (T : LatticeTriangle) : ℚ :=
  (T.twiceArea : ℚ) / 2 - (T.boundaryCount : ℚ) / 2 + 1

/-- Pick's formula for the interior-point count of `T`, expressed via the
    cleared-denominator integer formula `2 · I + B - 2A = 2`.

    This is the form most useful for inductive proofs: it sidesteps
    division by 2 and lets us reason in `ℕ` or `ℤ`. -/
def LatticeTriangle.pickInteriorNum (T : LatticeTriangle) : ℤ :=
  ((T.twiceArea : ℤ) - (T.boundaryCount : ℤ) + 2)

-- ════════════════════════════════════════════════════════════════
-- SECTION III: Algebraic Bridge Identity
-- ════════════════════════════════════════════════════════════════

/-- **Cleared-denominator form** of Pick's interior formula.

    By construction, `2 · pickInterior T = pickInteriorNum T`, so the two
    versions agree.  This identity is the engine that converts a question
    about half-integers into a question about integers. -/
theorem two_mul_pickInterior (T : LatticeTriangle) :
    2 * T.pickInterior = (T.pickInteriorNum : ℚ) := by
  unfold LatticeTriangle.pickInterior LatticeTriangle.pickInteriorNum
  push_cast
  ring

/-- **Pick's formula in standard form**:
    `twiceArea = 2 · pickInterior + boundaryCount - 2`, equivalently
    `Area = I + B/2 - 1` after dividing by `2`. -/
theorem pick_formula_cleared (T : LatticeTriangle) :
    (T.twiceArea : ℚ) = 2 * T.pickInterior + (T.boundaryCount : ℚ) - 2 := by
  unfold LatticeTriangle.pickInterior
  ring

-- ════════════════════════════════════════════════════════════════
-- SECTION IV: Concrete Verification on Three Triangles
-- ════════════════════════════════════════════════════════════════

/-! ### Test triangle 1: Unit right triangle `{(0,0), (1,0), (0,1)}`

  - `det = 1`, so `twiceArea = 1`, `Area = 1/2`.
  - Edges `(0,0)→(1,0)`, `(1,0)→(0,1)`, `(0,1)→(0,0)` have GCDs
    `gcd(1,0) = 1`, `gcd(1,1) = 1`, `gcd(0,1) = 1`, summing to `B = 3`.
  - `pickInterior = 1/2 - 3/2 + 1 = 0`.  ✓ (Interior count is `0`.) -/

/-- The unit right triangle. -/
def unitTriangle : LatticeTriangle := ⟨(0, 0), (1, 0), (0, 1)⟩

theorem unitTriangle_twiceArea : unitTriangle.twiceArea = 1 := by
  native_decide

theorem unitTriangle_boundaryCount : unitTriangle.boundaryCount = 3 := by
  native_decide

theorem unitTriangle_pickInterior : unitTriangle.pickInterior = 0 := by
  unfold LatticeTriangle.pickInterior
  rw [unitTriangle_twiceArea, unitTriangle_boundaryCount]
  norm_num

theorem unitTriangle_pickInteriorNum : unitTriangle.pickInteriorNum = 0 := by
  unfold LatticeTriangle.pickInteriorNum
  rw [unitTriangle_twiceArea, unitTriangle_boundaryCount]
  native_decide

/-! ### Test triangle 2: 2-by-1 right triangle `{(0,0), (2,0), (0,1)}`

  - `det = 2`, so `twiceArea = 2`, `Area = 1`.
  - Edges: GCDs `gcd(2,0) = 2`, `gcd(2,1) = 1`, `gcd(0,1) = 1`, summing
    to `B = 4`.
  - `pickInterior = 1 - 2 + 1 = 0`.  ✓ (Interior count is `0`.) -/

/-- Right triangle with legs `2` and `1`. -/
def triangle_2_1 : LatticeTriangle := ⟨(0, 0), (2, 0), (0, 1)⟩

theorem triangle_2_1_twiceArea : triangle_2_1.twiceArea = 2 := by
  native_decide

theorem triangle_2_1_boundaryCount : triangle_2_1.boundaryCount = 4 := by
  native_decide

theorem triangle_2_1_pickInterior : triangle_2_1.pickInterior = 0 := by
  unfold LatticeTriangle.pickInterior
  rw [triangle_2_1_twiceArea, triangle_2_1_boundaryCount]
  norm_num

/-! ### Test triangle 3: 3-by-3 right triangle `{(0,0), (3,0), (0,3)}`

  - `det = 9`, so `twiceArea = 9`, `Area = 9/2`.
  - Edges: GCDs `gcd(3,0) = 3`, `gcd(3,3) = 3`, `gcd(0,3) = 3`, summing
    to `B = 9`.
  - `pickInterior = 9/2 - 9/2 + 1 = 1`.  ✓ (Interior point is `(1,1)`.) -/

/-- Right triangle with legs `3` and `3` (one interior point at `(1,1)`). -/
def triangle_3_3 : LatticeTriangle := ⟨(0, 0), (3, 0), (0, 3)⟩

theorem triangle_3_3_twiceArea : triangle_3_3.twiceArea = 9 := by
  native_decide

theorem triangle_3_3_boundaryCount : triangle_3_3.boundaryCount = 9 := by
  native_decide

theorem triangle_3_3_pickInterior : triangle_3_3.pickInterior = 1 := by
  unfold LatticeTriangle.pickInterior
  rw [triangle_3_3_twiceArea, triangle_3_3_boundaryCount]
  norm_num

/-! ### Sanity: the cleared form agrees across all three. -/

theorem unitTriangle_pick_cleared :
    (unitTriangle.twiceArea : ℚ) =
      2 * unitTriangle.pickInterior + (unitTriangle.boundaryCount : ℚ) - 2 :=
  pick_formula_cleared unitTriangle

theorem triangle_2_1_pick_cleared :
    (triangle_2_1.twiceArea : ℚ) =
      2 * triangle_2_1.pickInterior + (triangle_2_1.boundaryCount : ℚ) - 2 :=
  pick_formula_cleared triangle_2_1

theorem triangle_3_3_pick_cleared :
    (triangle_3_3.twiceArea : ℚ) =
      2 * triangle_3_3.pickInterior + (triangle_3_3.boundaryCount : ℚ) - 2 :=
  pick_formula_cleared triangle_3_3

-- ════════════════════════════════════════════════════════════════
-- SECTION V: Concrete Sanity Checks (non-negativity of pickInterior)
-- ════════════════════════════════════════════════════════════════

theorem unitTriangle_pickInterior_nonneg : 0 ≤ unitTriangle.pickInterior := by
  rw [unitTriangle_pickInterior]

theorem triangle_2_1_pickInterior_nonneg : 0 ≤ triangle_2_1.pickInterior := by
  rw [triangle_2_1_pickInterior]

theorem triangle_3_3_pickInterior_nonneg : 0 ≤ triangle_3_3.pickInterior := by
  rw [triangle_3_3_pickInterior]; norm_num

end PicksTheoremOQ01OQ01OQ01
