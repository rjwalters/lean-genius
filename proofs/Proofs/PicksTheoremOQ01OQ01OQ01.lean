/-
# Pick's Theorem OQ-01-OQ-01-OQ-01: Bridge from Primitive Triangulation + GCD Boundary Count

Open Question (from `picks-theorem-oq-01-oq-01`):
"Can Pick's theorem `I + B/2 - 1 = Area` be derived in Lean 4 by combining
primitive triangulation with a boundary-point count via the GCD formula
(boundary points on segment from v1 to v2 = gcd(|v2.1-v1.1|, |v2.2-v1.2|))?"

## Status (S2 OBSERVE — base-case interior count, build-verified)

S2 introduces a decidable definition of the *real* strictly-interior
lattice-point count (`realInteriorCount`) as a `Finset` cardinality, and
verifies on three concrete triangles that `realInteriorCount = pickInterior`.
This closes the "base case" of the eventual Pick induction: for every
primitive (`|det| = 1`) triangle, the formula `pickInterior = 0` agrees
with the true count of strictly-interior lattice points.

S1 set up the bridge data structures that connect:

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
    `2A = 1`, `pickInterior = 0`, **`realInteriorCount = 0`** (S2).
  * Right triangle `{(0,0), (2,0), (0,1)}`: `I = 0`, `B = 4`, `2A = 2`,
    `pickInterior = 0`, **`realInteriorCount = 0`** (S2).
  * Right triangle `{(0,0), (3,0), (0,3)}`: `I = 1`, `B = 9`, `2A = 9`,
    `pickInterior = 1`, **`realInteriorCount = 1`** (S2; interior point
    `(1, 1)`).
- The bridge identity `2 · pickInterior + boundaryCount = twiceArea + 2`,
  i.e. Pick's formula in cleared-denominator form.
- The non-negativity sanity check `pickInterior ≥ 0` for the three test
  triangles (showing the formula does produce a valid interior count).
- S2: the agreement theorem `realInteriorCount T = pickInterior T` on each
  of the three test triangles (cast to `ℚ`).

## Architecture

- Section I: Mirror definitions (`LatticeTriangle`, `det`).
- Section II: Bridge data (`twiceArea`, `edgeGCD`, `boundaryCount`,
  `pickInterior`).
- Section III: Algebraic identity (`pick_formula_cleared`).
- Section IV: Verification on three concrete triangles (`pickInterior`).
- Section V: Non-negativity sanity checks.
- Section VI (S2): Real strictly-interior lattice-point count via a
  decidable bounding-box filter (`StrictInterior`, `boundingBox`,
  `realInterior`, `realInteriorCount`).
- Section VII (S2): `realInteriorCount = pickInterior` on the three test
  triangles (base-case agreement).

The companion files `PicksTheoremOQ01OQ01.lean` and `PicksTheoremOQ02.lean`
remain the load-bearing pieces; this file simply names the bridge and
makes the composition explicit.
-/

import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Prod
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

-- ════════════════════════════════════════════════════════════════
-- SECTION VI (S2): Real Strictly-Interior Lattice-Point Count
-- ════════════════════════════════════════════════════════════════

/-- Twice the signed area of triangle `(a, b, p)` via the 2D cross product
    `(b - a) × (p - a)`.  The sign records orientation: positive when
    `(a, b, p)` is counter-clockwise. -/
def cross2 (a b p : ℤ × ℤ) : ℤ :=
  (b.1 - a.1) * (p.2 - a.2) - (p.1 - a.1) * (b.2 - a.2)

/-- A lattice point `p` is **strictly interior** to a triangle `T` if all
    three edge cross products (for the cyclic sequence `(v_i, v_{i+1}, p)`)
    share the same strict sign.  This excludes edge and vertex points.

    The two disjuncts handle the two possible orientations of `T`
    (counter-clockwise: all cross products `> 0`; clockwise: all `< 0`). -/
def LatticeTriangle.StrictInterior (T : LatticeTriangle) (p : ℤ × ℤ) : Prop :=
  (0 < cross2 T.v1 T.v2 p ∧ 0 < cross2 T.v2 T.v3 p ∧ 0 < cross2 T.v3 T.v1 p) ∨
  (cross2 T.v1 T.v2 p < 0 ∧ cross2 T.v2 T.v3 p < 0 ∧ cross2 T.v3 T.v1 p < 0)

instance (T : LatticeTriangle) (p : ℤ × ℤ) : Decidable (T.StrictInterior p) := by
  unfold LatticeTriangle.StrictInterior
  infer_instance

/-- Smallest `x`-coordinate among the vertices of `T`. -/
def LatticeTriangle.xmin (T : LatticeTriangle) : ℤ :=
  min (min T.v1.1 T.v2.1) T.v3.1

/-- Largest `x`-coordinate among the vertices of `T`. -/
def LatticeTriangle.xmax (T : LatticeTriangle) : ℤ :=
  max (max T.v1.1 T.v2.1) T.v3.1

/-- Smallest `y`-coordinate among the vertices of `T`. -/
def LatticeTriangle.ymin (T : LatticeTriangle) : ℤ :=
  min (min T.v1.2 T.v2.2) T.v3.2

/-- Largest `y`-coordinate among the vertices of `T`. -/
def LatticeTriangle.ymax (T : LatticeTriangle) : ℤ :=
  max (max T.v1.2 T.v2.2) T.v3.2

/-- The bounding-box `Finset` of lattice points enclosing the vertices of
    `T`.  Every interior (and boundary) lattice point of `T` lies in this
    finite rectangle. -/
def LatticeTriangle.boundingBox (T : LatticeTriangle) : Finset (ℤ × ℤ) :=
  (Finset.Icc T.xmin T.xmax) ×ˢ (Finset.Icc T.ymin T.ymax)

/-- The set of strictly-interior lattice points of `T` as a `Finset`,
    obtained by filtering the bounding box through `StrictInterior`. -/
def LatticeTriangle.realInterior (T : LatticeTriangle) : Finset (ℤ × ℤ) :=
  T.boundingBox.filter T.StrictInterior

/-- The strictly-interior lattice-point count `I(T)`.  This is the "real"
    geometric quantity Pick's formula `pickInterior` is supposed to match. -/
def LatticeTriangle.realInteriorCount (T : LatticeTriangle) : ℕ :=
  T.realInterior.card

-- ════════════════════════════════════════════════════════════════
-- SECTION VII (S2): Base-Case Agreement `realInteriorCount = pickInterior`
-- ════════════════════════════════════════════════════════════════

/-! ### Unit triangle `{(0,0), (1,0), (0,1)}` — primitive (`|det| = 1`).

  This is the **base case** of the future Pick induction: for any
  primitive triangle, `realInteriorCount = 0 = pickInterior`.  Here we
  verify the unit instance; the general primitive case will be proved
  in S3 once we have the additivity lemma for shared edges. -/

theorem unitTriangle_realInteriorCount : unitTriangle.realInteriorCount = 0 := by
  native_decide

/-- Pick's formula holds on the unit triangle:
    `realInteriorCount = pickInterior = 0`. -/
theorem unitTriangle_pick_agrees :
    (unitTriangle.realInteriorCount : ℚ) = unitTriangle.pickInterior := by
  rw [unitTriangle_realInteriorCount, unitTriangle_pickInterior]
  norm_num

/-! ### 2-by-1 right triangle `{(0,0), (2,0), (0,1)}` (interior count = 0). -/

theorem triangle_2_1_realInteriorCount : triangle_2_1.realInteriorCount = 0 := by
  native_decide

theorem triangle_2_1_pick_agrees :
    (triangle_2_1.realInteriorCount : ℚ) = triangle_2_1.pickInterior := by
  rw [triangle_2_1_realInteriorCount, triangle_2_1_pickInterior]
  norm_num

/-! ### 3-by-3 right triangle `{(0,0), (3,0), (0,3)}` (interior count = 1).

  The unique strictly-interior lattice point is `(1, 1)`:
  - `cross2 (0,0) (3,0) (1,1) = 3·1 - 1·0 = 3 > 0`
  - `cross2 (3,0) (0,3) (1,1) = (-3)·1 - (-2)·3 = 3 > 0`
  - `cross2 (0,3) (0,0) (1,1) = 0·(-2) - 1·(-3) = 3 > 0`
  All three cross products are strictly positive, so `(1,1) ∈ realInterior`.
  No other point in `[0,3]²` satisfies all three. -/

theorem triangle_3_3_realInteriorCount : triangle_3_3.realInteriorCount = 1 := by
  native_decide

theorem triangle_3_3_pick_agrees :
    (triangle_3_3.realInteriorCount : ℚ) = triangle_3_3.pickInterior := by
  rw [triangle_3_3_realInteriorCount, triangle_3_3_pickInterior]
  norm_num

/-! ### Summary

  The three theorems `unitTriangle_pick_agrees`, `triangle_2_1_pick_agrees`,
  and `triangle_3_3_pick_agrees` establish base-case agreement between the
  real interior-lattice-point count and the rational `pickInterior` on the
  three test triangles.  Combined with Section IV's
  `unitTriangle_pickInterior`, `triangle_2_1_pickInterior`, and
  `triangle_3_3_pickInterior`, we obtain Pick's theorem **as a verified
  computation** on these specific triangles, fully discharging the
  formula's claim there.

  The remaining steps (S3, S4) are:

  - S3: Additivity lemma — when two triangles `T₁`, `T₂` share an edge
    `e` with `gcd(e) = 1` (no interior boundary lattice points), the real
    interior counts satisfy
    `realInteriorCount (T₁ ∪ T₂) = realInteriorCount T₁
                                    + realInteriorCount T₂
                                    + (boundary points strictly on e)`,
    and the same identity holds for `pickInterior` by `pick_formula_cleared`.
  - S4: Close the induction via
    `PicksTheoremOQ01OQ01.exists_primitive_triangulation`: every lattice
    triangle decomposes into `|det|` primitive sub-triangles, each
    contributing `pickInterior = 0`, and the boundary/area accounting
    aggregates correctly via the additivity lemma. -/

-- ════════════════════════════════════════════════════════════════
-- SECTION VIII (S3-prep): Primitive Case `twiceArea = 1` ⇒ `I = 0`
-- ════════════════════════════════════════════════════════════════

/-! ### The partition-sum identity

For any test point `p`, the three edge cross-products of `T` against
`p` sum to the signed determinant `T.det`.  Geometrically: the three
sub-triangles `(v_i, v_{i+1}, p)` tile `T` (with signs), so twice
their signed areas sum to twice the signed area of `T`. -/

/-- **Partition-sum identity**: the three edge cross-products of `T`
    against any lattice point `p` sum to `T.det` (= twice the signed
    area of `T`).  Discrete analogue of the additivity of signed
    area under triangulation: the three sub-triangles `(vᵢ, vᵢ₊₁, p)`
    tile `T` with appropriate signs. -/
theorem cross2_partition_sum (T : LatticeTriangle) (p : ℤ × ℤ) :
    cross2 T.v1 T.v2 p + cross2 T.v2 T.v3 p + cross2 T.v3 T.v1 p = T.det := by
  unfold cross2 LatticeTriangle.det
  ring

/-! ### No strict-interior lattice points in a primitive triangle

If `T.twiceArea = 1`, the `StrictInterior` predicate fails at every
lattice point.  This is the general primitive base case of the
Pick induction. -/

/-- **Primitive case — no strict interior points**: for a primitive
    lattice triangle (`twiceArea = 1`), no lattice point is strictly
    interior.

    *Proof idea.* The three cross-products `cross2 vᵢ vᵢ₊₁ p` sum to
    `T.det` (`cross2_partition_sum`), whose absolute value is
    `T.twiceArea = 1`.  If all three were of the same strict sign
    (the `StrictInterior` condition), each would have absolute value
    `≥ 1`, so the sum would have absolute value `≥ 3`, contradicting
    `|sum| = 1`.  `omega` discharges the integer-arithmetic
    contradiction in both orientations. -/
theorem primitive_no_strict_interior (T : LatticeTriangle)
    (h : T.twiceArea = 1) (p : ℤ × ℤ) : ¬ T.StrictInterior p := by
  intro hsi
  have hsum := cross2_partition_sum T p
  unfold LatticeTriangle.twiceArea at h
  unfold LatticeTriangle.StrictInterior at hsi
  rcases hsi with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega

/-- **Primitive case (S3-prep): `twiceArea = 1` ⇒ `realInteriorCount = 0`**.

    For every lattice triangle `T` with `|det T| = 1`, the strictly-
    interior lattice-point count is zero.  This is the **general
    primitive base case** of the Pick induction.

    The lemma strictly generalises `unitTriangle_realInteriorCount`
    (which handled the specific triangle `{(0,0), (1,0), (0,1)}` via
    `native_decide`) to *every* primitive triangle in `ℤ²`,
    independent of orientation, vertex labelling, or position.

    The proof is purely algebraic: combining `cross2_partition_sum`
    with `|T.det| = T.twiceArea = 1` forces the three cross-products
    not to all share the same strict sign, which is exactly the
    failure of `StrictInterior p`.  No bounding-box enumeration is
    required; the conclusion holds at every lattice point. -/
theorem primitive_realInteriorCount_zero (T : LatticeTriangle)
    (h : T.twiceArea = 1) : T.realInteriorCount = 0 := by
  unfold LatticeTriangle.realInteriorCount LatticeTriangle.realInterior
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun p _ => primitive_no_strict_interior T h p

/-- **Sanity check**: the unit-triangle base case `unitTriangle_realInteriorCount`
    is now recovered as a *uniform* corollary of the general primitive
    lemma — not relying on `native_decide` on the specific vertex
    coordinates.  This proves that the S3-prep generalisation is
    consistent with the S2 base-case computation. -/
example : unitTriangle.realInteriorCount = 0 :=
  primitive_realInteriorCount_zero unitTriangle unitTriangle_twiceArea

-- ════════════════════════════════════════════════════════════════
-- SECTION IX (S3a-plus): Primitive case — `pickInterior = 0`
-- ════════════════════════════════════════════════════════════════

/-! ### Primitive case: every edge GCD is `1`, hence `pickInterior T = 0`

S3-prep (`primitive_realInteriorCount_zero`) closed the geometric side
of the primitive base case: every primitive triangle has zero strictly-
interior lattice points.  S3a-plus closes the *formula* side: every
primitive triangle also has `pickInterior T = 0` (by Pick's identity,
since `boundaryCount = 3` once each edge GCD is `1`).

Combining the two, `(realInteriorCount T : ℚ) = pickInterior T` for
every primitive `T`, not only the three concrete witnesses verified by
`native_decide` in Section VII.

The proof factors through the signed edge vector for each edge: define
`signedDelta i : ℤ × ℤ` (the absolute-value-free version of
`edgeDelta i`), express `T.det` cyclically as a `ℤ`-linear combination
of its two components, and conclude `edgeGCD i ∣ T.twiceArea`; with
`T.twiceArea = 1` the only natural-number divisor is `1`.

Per the S3a-prep bearer audit (`#18950`), the Mathlib v4.26.0 / Lean
core API points used are: `Nat.gcd_dvd_left/right`,
`Nat.eq_one_of_dvd_one`, `Int.natCast_dvd_natCast`, `Int.dvd_natAbs`,
`Int.natAbs_dvd_natAbs` — all stable on the lockfile pin. -/

/-- The **signed** edge vector for edge `i`, retaining direction
    information that `edgeDelta i` (which is component-wise
    `Int.natAbs`) discards.  Used purely to express `T.det` as a
    `ℤ`-linear combination uniformly across the three edges. -/
def LatticeTriangle.signedDelta (T : LatticeTriangle) : Fin 3 → ℤ × ℤ
  | 0 => (T.v2.1 - T.v1.1, T.v2.2 - T.v1.2)
  | 1 => (T.v3.1 - T.v2.1, T.v3.2 - T.v2.2)
  | 2 => (T.v1.1 - T.v3.1, T.v1.2 - T.v3.2)

/-- `edgeDelta i` recovers `signedDelta i` componentwise via `Int.natAbs`. -/
lemma edgeDelta_eq_natAbs_signedDelta (T : LatticeTriangle) (i : Fin 3) :
    T.edgeDelta i = ((T.signedDelta i).1.natAbs, (T.signedDelta i).2.natAbs) := by
  fin_cases i <;> rfl

/-- The *other* edge vector emanating from `v_i` in the cyclic
    factorisation of `T.det`.  Pairs with `signedDelta i` so that
    `T.det = signedDelta_i.1 · crossDelta_i.2 − crossDelta_i.1 · signedDelta_i.2`. -/
def LatticeTriangle.crossDelta (T : LatticeTriangle) : Fin 3 → ℤ × ℤ
  | 0 => (T.v3.1 - T.v1.1, T.v3.2 - T.v1.2)
  | 1 => (T.v1.1 - T.v2.1, T.v1.2 - T.v2.2)
  | 2 => (T.v2.1 - T.v3.1, T.v2.2 - T.v3.2)

/-- **Cyclic factorisation of the determinant**: for every edge index
    `i`, `T.det` is a `ℤ`-linear combination of the two coordinates of
    `signedDelta i`, with `crossDelta i` supplying the cofactors.

    This is the algebraic content of "the 2×2 determinant is invariant
    under cyclic permutation of the three vertices" — for `i = 0` it is
    the literal definition of `T.det`; for `i = 1, 2` it is the same
    determinant computed against a cyclically shifted base vertex. -/
lemma det_eq_signedDelta_factor (T : LatticeTriangle) (i : Fin 3) :
    T.det = (T.signedDelta i).1 * (T.crossDelta i).2
             - (T.crossDelta i).1 * (T.signedDelta i).2 := by
  unfold LatticeTriangle.det LatticeTriangle.signedDelta LatticeTriangle.crossDelta
  fin_cases i <;> ring

/-- The edge GCD (as a `ℤ`) divides the first component of `signedDelta i`. -/
lemma edgeGCD_dvd_signedDelta_fst (T : LatticeTriangle) (i : Fin 3) :
    (T.edgeGCD i : ℤ) ∣ (T.signedDelta i).1 := by
  have h : T.edgeGCD i ∣ (T.signedDelta i).1.natAbs := by
    unfold LatticeTriangle.edgeGCD
    rw [edgeDelta_eq_natAbs_signedDelta]
    exact Nat.gcd_dvd_left _ _
  exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)

/-- The edge GCD (as a `ℤ`) divides the second component of `signedDelta i`. -/
lemma edgeGCD_dvd_signedDelta_snd (T : LatticeTriangle) (i : Fin 3) :
    (T.edgeGCD i : ℤ) ∣ (T.signedDelta i).2 := by
  have h : T.edgeGCD i ∣ (T.signedDelta i).2.natAbs := by
    unfold LatticeTriangle.edgeGCD
    rw [edgeDelta_eq_natAbs_signedDelta]
    exact Nat.gcd_dvd_right _ _
  exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)

/-- The edge GCD (as a `ℤ`) divides `T.det`.  Combines the cyclic
    determinant factorisation with the two component-wise divisibilities. -/
lemma edgeGCD_dvd_det (T : LatticeTriangle) (i : Fin 3) :
    (T.edgeGCD i : ℤ) ∣ T.det := by
  rw [det_eq_signedDelta_factor T i]
  exact ((edgeGCD_dvd_signedDelta_fst T i).mul_right _).sub
        ((edgeGCD_dvd_signedDelta_snd T i).mul_left _)

/-- The edge GCD divides `T.twiceArea` (= `|T.det|`).  Direct corollary
    of `edgeGCD_dvd_det` after collapsing through `Int.natAbs`. -/
lemma edgeGCD_dvd_twiceArea (T : LatticeTriangle) (i : Fin 3) :
    T.edgeGCD i ∣ T.twiceArea := by
  have h : (T.edgeGCD i : ℤ) ∣ T.det := edgeGCD_dvd_det T i
  have h' : (T.edgeGCD i : ℤ).natAbs ∣ T.det.natAbs :=
    Int.natAbs_dvd_natAbs.mpr h
  simpa [LatticeTriangle.twiceArea] using h'

/-- **Primitive case — every edge GCD is `1`**.  For every primitive
    lattice triangle (`twiceArea = 1`) and every edge index `i`, the
    edge GCD equals `1` — equivalently, the segment from `v_i` to
    `v_{i+1}` contains no interior lattice points. -/
theorem primitive_edgeGCD_eq_one (T : LatticeTriangle) (h : T.twiceArea = 1)
    (i : Fin 3) : T.edgeGCD i = 1 := by
  have hdvd : T.edgeGCD i ∣ T.twiceArea := edgeGCD_dvd_twiceArea T i
  rw [h] at hdvd
  exact Nat.eq_one_of_dvd_one hdvd

/-- **Primitive case — boundary count is `3`**.  Each edge contributes
    `edgeGCD = 1` lattice points to the boundary count, so the total is
    exactly `3` (one for each vertex/edge cycle). -/
theorem primitive_boundaryCount_eq_three (T : LatticeTriangle)
    (h : T.twiceArea = 1) : T.boundaryCount = 3 := by
  unfold LatticeTriangle.boundaryCount
  rw [primitive_edgeGCD_eq_one T h 0, primitive_edgeGCD_eq_one T h 1,
      primitive_edgeGCD_eq_one T h 2]

/-- **Primitive case — Pick's formula gives `pickInterior = 0`**.  For
    every primitive lattice triangle (`twiceArea = 1`), Pick's formula
    `I = A − B/2 + 1 = 1/2 − 3/2 + 1` evaluates to `0`.  This matches the
    geometric count `realInteriorCount = 0` (S3-prep). -/
theorem primitive_pickInterior_zero (T : LatticeTriangle)
    (h : T.twiceArea = 1) : T.pickInterior = 0 := by
  unfold LatticeTriangle.pickInterior
  rw [primitive_boundaryCount_eq_three T h, h]
  norm_num

/-- **Primitive base case — agreement of `realInteriorCount` and
    `pickInterior`**.  For every primitive lattice triangle
    (`twiceArea = 1`), the geometric count of strictly-interior lattice
    points matches the rational value of Pick's formula.  This is the
    clean primitive base case of the eventual Pick induction. -/
theorem primitive_pick_agrees (T : LatticeTriangle) (h : T.twiceArea = 1) :
    (T.realInteriorCount : ℚ) = T.pickInterior := by
  rw [primitive_realInteriorCount_zero T h, primitive_pickInterior_zero T h]
  simp

/-- **Sanity check**: the unit-triangle agreement
    `unitTriangle.realInteriorCount = unitTriangle.pickInterior`
    (originally `native_decide` in S2, restated `unfold + norm_num` in S1)
    is now recovered uniformly as a corollary of `primitive_pick_agrees`. -/
example : (unitTriangle.realInteriorCount : ℚ) = unitTriangle.pickInterior :=
  primitive_pick_agrees unitTriangle unitTriangle_twiceArea

-- ════════════════════════════════════════════════════════════════
-- SECTION VIII (S3b-act-1): ℤ-anchored Lattice Segment Points
-- ════════════════════════════════════════════════════════════════

namespace LatticeTriangle

/-- Lattice points lying on the closed segment from `v` to `w` in `ℤ × ℤ`,
    parametrised by `k · (Δ / g)` where `g = Int.gcd Δx Δy` and `Δ = w - v`.
    Generalises `PicksTheoremOQ02.segmentPoints (a b : ℕ)` (origin-anchored
    ℕ-coords) to arbitrary ℤ-coord, vertex-anchored segments. -/
noncomputable def latticeSegmentPoints (v w : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  let dx : ℤ := w.1 - v.1
  let dy : ℤ := w.2 - v.2
  let g  : ℕ := Int.gcd dx dy
  (Finset.range (g + 1)).image
    (fun k : ℕ => (v.1 + (k : ℤ) * (dx / (g : ℤ)),
                   v.2 + (k : ℤ) * (dy / (g : ℤ))))

end LatticeTriangle

/-- Injectivity of the segment parametrisation on `Finset.range (g + 1)`.
    Used by `card_latticeSegmentPoints` to count via `Finset.card_image_of_injOn`. -/
private theorem parametrisation_injOn_range (v w : ℤ × ℤ) :
    Set.InjOn
      (fun k : ℕ => (v.1 + (k : ℤ) * ((w.1 - v.1) / ((Int.gcd (w.1 - v.1) (w.2 - v.2) : ℕ) : ℤ)),
                     v.2 + (k : ℤ) * ((w.2 - v.2) / ((Int.gcd (w.1 - v.1) (w.2 - v.2) : ℕ) : ℤ))))
      ↑(Finset.range ((Int.gcd (w.1 - v.1) (w.2 - v.2) : ℕ) + 1)) := by
  set dx : ℤ := w.1 - v.1 with hdx_def
  set dy : ℤ := w.2 - v.2 with hdy_def
  set g  : ℕ := Int.gcd dx dy with hg_def
  intro k₁ hk₁ k₂ hk₂ heq
  rw [Finset.mem_coe, Finset.mem_range] at hk₁ hk₂
  by_cases hg : g = 0
  · -- g = 0 ⟹ Finset.range 1 = {0} ⟹ k₁, k₂ < 1 ⟹ k₁ = k₂ = 0 by omega.
    omega
  · -- g ≠ 0. Pair-eq decomposition; cancel v.{1,2}; factor (k₁-k₂)·(d/g) = 0.
    obtain ⟨hxeq, hyeq⟩ := Prod.mk.inj heq
    have hk_dx : ((k₁ : ℤ) - k₂) * (dx / (g : ℤ)) = 0 := by linear_combination hxeq
    have hk_dy : ((k₁ : ℤ) - k₂) * (dy / (g : ℤ)) = 0 := by linear_combination hyeq
    -- `Int.ne_zero_of_gcd` : `Int.gcd x y ≠ 0 → x ≠ 0 ∨ y ≠ 0`
    -- (Mathlib/Data/Int/GCD.lean:202).
    rcases Int.ne_zero_of_gcd hg with hxne | hyne
    · -- dx ≠ 0 ⟹ dx/g ≠ 0 (since g ∣ dx exactly and dx ≠ 0)
      have hdx_g_ne : dx / (g : ℤ) ≠ 0 := by
        intro hzero
        have := Int.ediv_mul_cancel (Int.gcd_dvd_left dx dy : (g : ℤ) ∣ dx)
        rw [hzero, zero_mul] at this
        exact hxne this.symm
      have hcast : (k₁ : ℤ) = (k₂ : ℤ) := by
        rcases mul_eq_zero.mp hk_dx with h | h
        · linarith
        · exact absurd h hdx_g_ne
      exact_mod_cast hcast
    · -- symmetric: dy ≠ 0 ⟹ dy/g ≠ 0 ⟹ k₁ = k₂
      have hdy_g_ne : dy / (g : ℤ) ≠ 0 := by
        intro hzero
        have := Int.ediv_mul_cancel (Int.gcd_dvd_right dx dy : (g : ℤ) ∣ dy)
        rw [hzero, zero_mul] at this
        exact hyne this.symm
      have hcast : (k₁ : ℤ) = (k₂ : ℤ) := by
        rcases mul_eq_zero.mp hk_dy with h | h
        · linarith
        · exact absurd h hdy_g_ne
      exact_mod_cast hcast

/-- Cardinality of `latticeSegmentPoints`: counts `Int.gcd Δx Δy + 1` lattice
    points on the closed segment from `v` to `w`. Generalises
    `PicksTheoremOQ02.card_segmentPoints` to ℤ-coords. -/
theorem card_latticeSegmentPoints (v w : ℤ × ℤ) :
    (LatticeTriangle.latticeSegmentPoints v w).card =
    Int.gcd (w.1 - v.1) (w.2 - v.2) + 1 := by
  unfold LatticeTriangle.latticeSegmentPoints
  rw [Finset.card_image_of_injOn (parametrisation_injOn_range v w),
      Finset.card_range]

end PicksTheoremOQ01OQ01OQ01
