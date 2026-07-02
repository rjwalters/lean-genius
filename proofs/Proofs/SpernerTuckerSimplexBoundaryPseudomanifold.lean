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

/-! ## The general case: `∂Δ^{n+1}` is a closed pseudomanifold in every dimension

The `decide` proofs above are pinned to `n = 3` (`∂Δ⁴`).  The same statement holds in
*every* dimension and needs no case enumeration.  Model `∂Δ^{n+1}` on the vertex set
`Fin (n+2)`: the top cell `Sᵢ = univ.erase i` is the facet opposite vertex `i`
(`n+1` vertices), and a door is any `n`-vertex face `d`.  Then `d ⊆ Sᵢ ⟺ i ∉ d`, so the
top cells containing a fixed door `d` are exactly the vertices *not* in `d`, of which
there are `(n+2) - n = 2`.  This is the pseudomanifold property (`hdoor`, the `≤ 2`
bound) together with closedness (exact incidence `2`) for all `n` at once. -/

/-- **General closed pseudomanifold property of `∂Δ^{n+1}`.**  For every `n`-vertex door
`d` of the boundary of the standard `(n+1)`-simplex, exactly two top cells
`Sᵢ = univ.erase i` contain it — in every dimension, with no per-dimension `decide`. -/
theorem boundary_simplex_closed_incidence {n : ℕ}
    (d : Finset (Fin (n + 2))) (hd : d.card = n) :
    #{i | d ⊆ Finset.univ.erase i} = 2 := by
  have hset : Finset.univ.filter (fun i => d ⊆ Finset.univ.erase i) = dᶜ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.subset_erase, Finset.subset_univ]
  rw [hset, Finset.card_compl, Fintype.card_fin, hd]
  omega

/-- **General `hdoor` (the pseudomanifold `≤ 2` bound) for `∂Δ^{n+1}`, all `n`.**  An
immediate consequence of `boundary_simplex_closed_incidence`: every door borders at most
two top cells, in every dimension. -/
theorem boundary_simplex_hdoor {n : ℕ}
    (d : Finset (Fin (n + 2))) (hd : d.card = n) :
    #{i | d ⊆ Finset.univ.erase i} ≤ 2 :=
  (boundary_simplex_closed_incidence d hd).le

/-! ## The pair bound `hpair` for `∂Δ^{n+1}`, all `n`

The concrete `hpair` above (two distinct tetrahedra share `≤ 1` triangle) is proved for
`∂Δ⁴` by `decide`.  It too is dimension-free: a door `d` incident to *both* top cells
`Sᵢ = univ.erase i` and `Sⱼ = univ.erase j` with `i ≠ j` is pinned to the single face
`{i, j}ᶜ`.  Indeed `d ⊆ univ.erase i` forces `i ∉ d` and likewise `j ∉ d`, so
`d ⊆ {i, j}ᶜ`; the complement has card `(n+2) - 2 = n = d.card`, so the containment is an
equality.  Two doors each incident to the same pair `{i, j}` are therefore both `{i, j}ᶜ`,
hence equal — the `hpair` bound in every dimension, with no per-dimension `decide`. -/

/-- **The shared door of two distinct top cells is forced.**  A door `d` (an `n`-vertex
face) contained in both `univ.erase i` and `univ.erase j` (with `i ≠ j`) is exactly the
complement `{i, j}ᶜ`.  Dimension-free. -/
theorem boundary_simplex_door_eq {n : ℕ} (d : Finset (Fin (n + 2)))
    (hd : d.card = n) {i j : Fin (n + 2)} (hij : i ≠ j)
    (hi : d ⊆ Finset.univ.erase i) (hj : d ⊆ Finset.univ.erase j) :
    d = ({i, j} : Finset (Fin (n + 2)))ᶜ := by
  have hi' : i ∉ d := fun h => (Finset.mem_erase.mp (hi h)).1 rfl
  have hj' : j ∉ d := fun h => (Finset.mem_erase.mp (hj h)).1 rfl
  have hsub : d ⊆ ({i, j} : Finset (Fin (n + 2)))ᶜ := by
    intro x hx
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hi' (h ▸ hx), fun h => hj' (h ▸ hx)⟩
  have hcard : ({i, j} : Finset (Fin (n + 2)))ᶜ.card = n := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hij]
    omega
  exact Finset.eq_of_subset_of_card_le hsub (hcard.trans hd.symm).le

/-- **General `hpair` (the pair bound) for `∂Δ^{n+1}`, all `n`.**  Two doors `d`, `d'`
each incident to the *same* two distinct top cells `Sᵢ`, `Sⱼ` are equal: both are pinned
to `{i, j}ᶜ` by `boundary_simplex_door_eq`.  This discharges the engine's `hpair` input in
every dimension, removing the per-dimension `decide`. -/
theorem boundary_simplex_hpair {n : ℕ} (d d' : Finset (Fin (n + 2)))
    (hd : d.card = n) (hd' : d'.card = n) {i j : Fin (n + 2)} (hij : i ≠ j)
    (hi : d ⊆ Finset.univ.erase i) (hj : d ⊆ Finset.univ.erase j)
    (hi' : d' ⊆ Finset.univ.erase i) (hj' : d' ⊆ Finset.univ.erase j) :
    d = d' := by
  rw [boundary_simplex_door_eq d hd hij hi hj,
      boundary_simplex_door_eq d' hd' hij hi' hj']

end SpernerTuckerSimplexBoundaryPseudomanifold
