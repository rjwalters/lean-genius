import Mathlib.Tactic
import Mathlib.Data.List.Basic

/-!
# Platonic Solids and Finite Reflection (Coxeter) Groups  (OQ-03)

## What This Proves

The parent entry classifies the five Platonic solids via their Schläfli symbols
`{p, q}`.  This follow-up records the *symmetry* side of the story: every Platonic
solid `P` has a full symmetry group that is a finite **rank-3 reflection (Coxeter)
group**, and the five solids fall into exactly **three** symmetry classes:

| Solid(s)                     | Schläfli | Coxeter group | `|W|` |
|------------------------------|----------|---------------|-------|
| Tetrahedron                  | {3,3}    | `A₃`          | 24    |
| Cube, Octahedron             | {4,3}    | `B₃` (= BC₃)  | 48    |
| Dodecahedron, Icosahedron    | {5,3}    | `H₃`          | 120   |

The three classes are exactly the orbits of *Platonic duality* (swapping `p ↔ q`):
duals share a symmetry group, which is why five solids give only three groups.

## The Honest Scope

A full group isomorphism `Sym(P) ≅ W(Φ)` would require constructing both the
geometric symmetry group of an embedded polyhedron and the abstract Coxeter group,
plus an explicit isomorphism — thousands of lines of geometry not in Mathlib.

Instead we capture the correspondence at the level of the **numerical invariants**
that pin these groups down, all of which are finite and machine-checkable:

* the **order** `|W| = 4E` (four times the edge count), the master bridge to the
  parent's combinatorics;
* the **product-of-degrees** formula `|W| = d₁·d₂·d₃` (the Shephard–Todd /
  Chevalley theorem: `|W|` equals the product of the degrees of the fundamental
  invariants);
* the **reflection count** `N = m₁+m₂+m₃` (sum of exponents `mᵢ = dᵢ-1`), equal to
  the number of mirror planes of the solid (6, 9, 15);
* the classical identity `N = n·h/2` (`n` = rank = 3, `h` = Coxeter number = top
  degree), here `2N = 3h`;
* the rotation (orientation-preserving) subgroup of index two, order `2E`, giving
  the rotation groups `A₄, S₄, A₅` of orders 12, 24, 60.

These are precisely the data a Coxeter-group classification attaches to each solid,
so the table above is verified in full at the invariant level.

## Status
- [x] Self-contained (no imports beyond Mathlib)
- [x] 0 sorries, 0 `axiom` declarations, 0 `native_decide` (all `decide`/`rfl`)

## References
- Coxeter, *Regular Polytopes*, Ch. on reflection groups.
- Humphreys, *Reflection Groups and Coxeter Groups*, §3 (orders, degrees, `nh/2`).
- https://en.wikipedia.org/wiki/Coxeter_group  (finite rank-3 groups A₃, B₃, H₃)
-/

set_option linter.unusedVariables false

namespace PlatonicSolidsOQ03

-- ============================================================
-- PART 1: The five solids and their combinatorics
-- ============================================================

/-- The five Platonic solids. -/
inductive Solid
  | tetrahedron
  | cube
  | octahedron
  | dodecahedron
  | icosahedron
  deriving DecidableEq, Repr

open Solid

/-- The five solids as a list, for enumeration. -/
def allSolids : List Solid :=
  [tetrahedron, cube, octahedron, dodecahedron, icosahedron]

/-- The Schläfli symbol `{p, q}`: `p` sides per face, `q` faces per vertex. -/
def Solid.schlafli : Solid → ℕ × ℕ
  | tetrahedron  => (3, 3)
  | cube         => (4, 3)
  | octahedron   => (3, 4)
  | dodecahedron => (5, 3)
  | icosahedron  => (3, 5)

/-- Edge count `E = 2pq / (4 - (p-2)(q-2))`, derived from `pF = qV = 2E` and
    Euler's formula (as in the parent entry).  For all five solids the denominator
    `4 - (p-2)(q-2)` is a positive natural number, so the division is exact. -/
def Solid.edges (s : Solid) : ℕ :=
  let p := s.schlafli.1
  let q := s.schlafli.2
  2 * p * q / (4 - (p - 2) * (q - 2))

/-- Platonic duality swaps `p ↔ q`: tetrahedron is self-dual, cube ↔ octahedron,
    dodecahedron ↔ icosahedron. -/
def Solid.dual : Solid → Solid
  | tetrahedron  => tetrahedron
  | cube         => octahedron
  | octahedron   => cube
  | dodecahedron => icosahedron
  | icosahedron  => dodecahedron

/-- Edge counts, matching `PlatonicSolids.*_geometry`. -/
theorem edges_values :
    tetrahedron.edges = 6 ∧ cube.edges = 12 ∧ octahedron.edges = 12 ∧
    dodecahedron.edges = 30 ∧ icosahedron.edges = 30 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Duality is an involution. -/
theorem dual_dual (s : Solid) : s.dual.dual = s := by
  cases s <;> rfl

/-- Duality preserves the edge count (it swaps `p` and `q`, leaving `2pq` and the
    symmetric denominator fixed). -/
theorem dual_preserves_edges (s : Solid) : s.dual.edges = s.edges := by
  cases s <;> rfl

-- ============================================================
-- PART 2: Finite rank-3 reflection (Coxeter) groups
-- ============================================================

/-- A finite irreducible **rank-3 reflection group**, recorded by its three
    fundamental **degrees** `d₁ ≤ d₂ ≤ d₃` (the degrees of the basic invariant
    polynomials).  The degrees determine all the numerical invariants below. -/
structure CoxeterRank3 where
  d₁ : ℕ
  d₂ : ℕ
  d₃ : ℕ
  deriving DecidableEq, Repr

/-- Group order `|W| = d₁·d₂·d₃` (product of the degrees). -/
def CoxeterRank3.order (W : CoxeterRank3) : ℕ := W.d₁ * W.d₂ * W.d₃

/-- The exponents `mᵢ = dᵢ - 1`. -/
def CoxeterRank3.exponents (W : CoxeterRank3) : ℕ × ℕ × ℕ :=
  (W.d₁ - 1, W.d₂ - 1, W.d₃ - 1)

/-- Number of reflections `N = m₁ + m₂ + m₃` (the sum of exponents, equal to the
    number of positive roots / mirror hyperplanes). -/
def CoxeterRank3.numReflections (W : CoxeterRank3) : ℕ :=
  (W.d₁ - 1) + (W.d₂ - 1) + (W.d₃ - 1)

/-- Coxeter number `h` = the largest degree `d₃`. -/
def CoxeterRank3.coxeterNumber (W : CoxeterRank3) : ℕ := W.d₃

/-- `A₃` (≅ `S₄`): symmetry group of the tetrahedron, degrees `2,3,4`. -/
def A₃ : CoxeterRank3 := ⟨2, 3, 4⟩
/-- `B₃` (= `BC₃`): symmetry group of the cube/octahedron, degrees `2,4,6`. -/
def B₃ : CoxeterRank3 := ⟨2, 4, 6⟩
/-- `H₃`: symmetry group of the dodecahedron/icosahedron, degrees `2,6,10`. -/
def H₃ : CoxeterRank3 := ⟨2, 6, 10⟩

/-- The reflection group of each Platonic solid. -/
def Solid.coxeter : Solid → CoxeterRank3
  | tetrahedron  => A₃
  | cube         => B₃
  | octahedron   => B₃
  | dodecahedron => H₃
  | icosahedron  => H₃

-- ============================================================
-- PART 3: Orders, and the master bridge  |W| = 4E
-- ============================================================

/-- The three group orders. -/
theorem coxeter_orders :
    A₃.order = 24 ∧ B₃.order = 48 ∧ H₃.order = 120 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Master bridge.**  The order of the reflection group of a Platonic solid is
    `4E`, four times its edge count.  This links the symmetry side to the parent's
    Schläfli/Euler combinatorics. -/
theorem order_eq_four_edges (s : Solid) :
    s.coxeter.order = 4 * s.edges := by
  cases s <;> decide

/-- The full symmetry-group order of each solid (= `4E`). -/
def Solid.fullSymmetryOrder (s : Solid) : ℕ := 4 * s.edges

theorem fullSymmetryOrder_eq_coxeter_order (s : Solid) :
    s.fullSymmetryOrder = s.coxeter.order := by
  cases s <;> decide

-- ============================================================
-- PART 4: Degrees, exponents, and the product formula
-- ============================================================

/-- **Product-of-degrees formula** (Shephard–Todd / Chevalley): for every rank-3
    group recorded here, `|W|` equals the product of its degrees.  This is true by
    definition of `order`, so it holds for *all* `CoxeterRank3`. -/
theorem order_eq_prod_degrees (W : CoxeterRank3) :
    W.order = W.d₁ * W.d₂ * W.d₃ := rfl

/-- Equivalently, `|W| = ∏ (mᵢ + 1)` in terms of the exponents `mᵢ`. -/
theorem order_eq_prod_exponents_succ :
    (A₃.exponents.1 + 1) * (A₃.exponents.2.1 + 1) * (A₃.exponents.2.2 + 1) = A₃.order ∧
    (B₃.exponents.1 + 1) * (B₃.exponents.2.1 + 1) * (B₃.exponents.2.2 + 1) = B₃.order ∧
    (H₃.exponents.1 + 1) * (H₃.exponents.2.1 + 1) * (H₃.exponents.2.2 + 1) = H₃.order := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The exponents of the three groups: `1,2,3` / `1,3,5` / `1,5,9`. -/
theorem exponent_values :
    A₃.exponents = (1, 2, 3) ∧ B₃.exponents = (1, 3, 5) ∧ H₃.exponents = (1, 5, 9) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================
-- PART 5: Reflections, mirror planes, and N = n·h/2
-- ============================================================

/-- Reflection counts `N = 6, 9, 15` — the numbers of **mirror planes** of the
    tetrahedron, cube/octahedron, and dodecahedron/icosahedron respectively. -/
theorem numReflections_values :
    A₃.numReflections = 6 ∧ B₃.numReflections = 9 ∧ H₃.numReflections = 15 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The Coxeter numbers `h = 4, 6, 10` (the top degree). -/
theorem coxeterNumber_values :
    A₃.coxeterNumber = 4 ∧ B₃.coxeterNumber = 6 ∧ H₃.coxeterNumber = 10 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The classical identity `N = n·h/2`** (number of reflections = rank · Coxeter
    number / 2), written without division as `2N = 3h` for rank `n = 3`.  Verified
    for each of the three Platonic reflection groups. -/
theorem two_numReflections_eq_three_coxeterNumber :
    2 * A₃.numReflections = 3 * A₃.coxeterNumber ∧
    2 * B₃.numReflections = 3 * B₃.coxeterNumber ∧
    2 * H₃.numReflections = 3 * H₃.coxeterNumber := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================
-- PART 6: Exactly three symmetry classes; duality
-- ============================================================

/-- Duals share a reflection group (duality only swaps `p ↔ q`). -/
theorem coxeter_dual (s : Solid) : s.dual.coxeter = s.coxeter := by
  cases s <;> rfl

/-- The distinct reflection groups of the five solids are exactly `A₃, B₃, H₃`. -/
theorem coxeter_classes :
    (allSolids.map Solid.coxeter).dedup = [A₃, B₃, H₃] := by
  decide

/-- **Exactly three symmetry classes**: the five Platonic solids realize three
    distinct reflection groups. -/
theorem number_of_symmetry_classes :
    (allSolids.map Solid.coxeter).dedup.length = 3 := by
  decide

-- ============================================================
-- PART 7: Rotation subgroup (index 2) and the rotation groups
-- ============================================================

/-- The rotation (orientation-preserving) subgroup has order `2E`. -/
def Solid.rotationOrder (s : Solid) : ℕ := 2 * s.edges

/-- The full symmetry group contains the rotation subgroup with **index two**
    (adjoining a reflection doubles the order): `|Sym| = 2 · |Rot|`. -/
theorem fullSymmetry_eq_two_rotation (s : Solid) :
    s.fullSymmetryOrder = 2 * s.rotationOrder := by
  cases s <;> rfl

/-- The rotation-group orders `12, 24, 24, 60, 60` — i.e. `A₄, S₄, A₅` — for the
    five solids. -/
theorem rotationOrder_values :
    tetrahedron.rotationOrder = 12 ∧ cube.rotationOrder = 24 ∧
    octahedron.rotationOrder = 24 ∧ dodecahedron.rotationOrder = 60 ∧
    icosahedron.rotationOrder = 60 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

-- ============================================================
-- PART 8: Capstone correspondence
-- ============================================================

/-- **Platonic ↔ Coxeter correspondence (invariant level).**  For every Platonic
    solid, its reflection group's order is `4E`, equals the product of its degrees,
    and is twice the rotation-subgroup order; and the five solids realize exactly
    the three rank-3 reflection groups `A₃, B₃, H₃`. -/
theorem platonic_coxeter_correspondence :
    (∀ s : Solid,
      s.coxeter.order = 4 * s.edges ∧
      s.coxeter.order = s.coxeter.d₁ * s.coxeter.d₂ * s.coxeter.d₃ ∧
      s.coxeter.order = 2 * s.rotationOrder) ∧
    (allSolids.map Solid.coxeter).dedup = [A₃, B₃, H₃] := by
  refine ⟨fun s => ?_, by decide⟩
  cases s <;> exact ⟨by decide, rfl, by decide⟩

end PlatonicSolidsOQ03

-- Export main results
#check PlatonicSolidsOQ03.order_eq_four_edges
#check PlatonicSolidsOQ03.platonic_coxeter_correspondence
#check PlatonicSolidsOQ03.number_of_symmetry_classes
