/-
# A concrete *closed* n = 3 pseudomanifold: `hdoor` on the boundary of the 4-simplex

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

The companion file `SpernerTuckerHexagonPseudomanifold.lean` discharges the abstract
door-counting engine's geometric input `hdoor` (each door/facet borders `≤ 2`
simplices — the *pseudomanifold* property) on a concrete `n = 2` triangulation (the
hexagon disc).  This file does the same one dimension up, on a **closed** manifold,
and uses the contrast to record an architectural point.

## The model: `∂Δ⁴`, the simplicial 3-sphere

Take the boundary of the standard 4-simplex on vertices `{0,1,2,3,4}`.  Its top cells
are the five tetrahedra `Sᵢ = {0,1,2,3,4} \ {i}` (the facet *opposite* vertex `i`); its
doors are the ten triangles, each a 3-subset.  A triangle is a face of `Sᵢ` exactly
when `i` is *not* one of its three vertices — equivalently, encoding a triangle by the
**pair `{a,b}` of vertices it omits**, the triangle `dₐᵦ = {0,…,4}\{a,b}` is a face of
`Sᵢ` iff `i ∈ {a,b}`.  So tetrahedra are indexed by `Fin 5` and doors by the ten pairs
(`dpair : Fin 10 → Fin 5 × Fin 5`), with

> `inc i d  ⟺  i = (dpair d).1 ∨ i = (dpair d).2`.

## What this file proves (all by kernel `decide`, 0 axioms)

* `hdoor`        — every triangle borders `≤ 2` tetrahedra: the pseudomanifold property
  in dimension 3.
* `closed_incidence` — in fact **exactly 2**: `∂Δ⁴` is a *closed* pseudomanifold (no
  boundary), so every door is interior, sharpening `hdoor` to an equality.
* `hpair`        — two distinct tetrahedra share `≤ 1` triangle (indeed exactly one: two
  distinct 4-subsets of a 5-set meet in a unique 3-subset).
* `simplex_degree` — running the engine's degree formula
  (`SpernerTuckerDoorGraph.doorGraph_degree_eq_shared`) on this incidence gives **degree
  4** for every tetrahedron: the raw door graph of `∂Δ⁴` is the complete graph `K₅`.

## The architectural point (`simplex_degree` vs. the hexagon)

The engine's *conclusion* needs a max-degree-`≤ 2` graph (a disjoint union of paths and
cycles).  The hexagon's raw door graph happened to be the 6-cycle, but that is **not**
a consequence of `hdoor` alone: here `hdoor` holds (exactly 2 everywhere) yet the raw
door graph is `K₅`, with degree 4.  The degree-`≤ 2` structure that drives
path-following comes from restricting to the **complementary** doors under the labelling
(the `hsimplex` bound of `SpernerTuckerDoorLemma`), *not* from the pseudomanifold
property.  So `hdoor` and `hsimplex` are genuinely independent engine inputs: `hdoor` is
geometric (a property of the triangulation), `hsimplex` is combinatorial (a property of
the colouring).  This file is the concrete witness that the two cannot be conflated.

Self-contained: imports Mathlib and the engine.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — NO `native_decide`/`ofReduceBool`).
-/
import Mathlib
import Proofs.SpernerTuckerDoorGraph

namespace SpernerTuckerSimplexBoundaryPseudomanifold

open Finset

/-! ## The `∂Δ⁴` incidence -/

/-- The five tetrahedra of `∂Δ⁴`, indexed by the vertex each one omits. -/
abbrev Tet := Fin 5

/-- The ten triangles (doors) of `∂Δ⁴`. -/
abbrev Door := Fin 10

/-- A door, encoded by the **pair of vertices it omits**.  The ten pairs `{a,b}`
with `a < b` of `{0,1,2,3,4}`. -/
def dpair : Door → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- **Incidence.**  The tetrahedron `Sᵢ = {0,…,4}\{i}` carries the door `d = {0,…,4}\{a,b}`
iff `i` is one of the omitted vertices `a, b`. -/
def inc (i : Tet) (d : Door) : Prop :=
  i = (dpair d).1 ∨ i = (dpair d).2

instance : DecidableRel inc := fun i d => by unfold inc; infer_instance

/-! ## The pseudomanifold property in dimension 3 — by `decide` -/

/-- **The pseudomanifold property / engine `hdoor`, dimension 3.**  Every triangle of
`∂Δ⁴` borders at most two tetrahedra.  By the kernel (no axioms). -/
theorem hdoor : ∀ d : Door, #{i | inc i d} ≤ 2 := by decide

/-- **`∂Δ⁴` is closed.**  Every door borders *exactly two* tetrahedra — there is no
boundary, so the `hdoor` bound is attained at every door.  (Contrast the hexagon disc,
whose six boundary edges border only one triangle.) -/
theorem closed_incidence : ∀ d : Door, #{i | inc i d} = 2 := by decide

/-- **The pair bound / engine `hpair`.**  Two distinct tetrahedra share at most one
triangle.  (Two distinct 4-subsets of a 5-set meet in a unique 3-subset.)  By `decide`. -/
theorem hpair : ∀ d d' : Door, ∀ i j : Tet, i ≠ j →
    inc i d → inc j d → inc i d' → inc j d' → d = d' := by decide

/-! ## Running the engine: the raw door graph is `K₅` -/

open SpernerTuckerDoorGraph

/-- **The engine's degree formula on `∂Δ⁴`.**  `doorGraph_degree_eq_shared` (which needs
only `hdoor` and `hpair`) identifies the graph degree with the number of *shared* doors.
Every tetrahedron shares one of its four triangular faces with each of the other four
tetrahedra, so its degree is `4`: the raw door graph of `∂Δ⁴` is the complete graph `K₅`.

This is the concrete witness that `hdoor` (the pseudomanifold property, here holding with
exact incidence `2`) does **not** by itself yield the max-degree-`≤ 2` graph the
path-following engine consumes — that structure comes from the *complementary-door*
restriction (`hsimplex`), an independent input. -/
theorem simplex_degree (i : Tet) : (doorGraph inc).degree i = 4 := by
  rw [doorGraph_degree_eq_shared inc hdoor hpair i]
  revert i; decide

end SpernerTuckerSimplexBoundaryPseudomanifold
