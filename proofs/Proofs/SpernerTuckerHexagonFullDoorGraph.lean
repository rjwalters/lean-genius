/-
# The full all-signs complementary-edge door graph on the hexagon is paths-and-cycles

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

The abstract door-counting engine (`SpernerTuckerDoorGraph.doorGraph_degree_le_two`)
turns a finite door-incidence relation `inc : Room → Door → Prop` satisfying

* `hdoor`    — each door borders `≤ 2` rooms (pseudomanifold), and
* `hsimplex` — each room has `≤ 2` doors,

into a max-degree-`≤2` graph (a disjoint union of paths and cycles), then reads
Tucker off an **odd** count of boundary doors.

Two earlier n = 2 obstructions on the standard hexagon + centre triangulation of `B²`
(`SpernerTuckerHexagon`, `SpernerTuckerHexagonDoorObstruction`) showed that a door
graph built from a **single fixed complementary sign** is not a complete certificate:
its complementary-edge *count* is not a parity invariant, and its interior spoke-door
graph can be entirely empty while Tucker still holds.  The natural repair flagged there
is to let the doors range over **all** signs and include **boundary** edges.

## What this file proves (all by kernel `decide`, 0 axioms)

This file supplies that full door graph and pins down exactly how far it gets.

Doors are **all** complementary edges (of either sign), interior *and* boundary:
`inc t e := (e is a side of triangle t) ∧ (e is complementary under the labelling)`.

* `hsimplex` — every triangle has `≤ 2` complementary doors, for **every** antipodal
  labelling: the room bound the engine needs.
* `no_triangle_all_complementary` — the sharp reason: **no** triangle ever has all
  three of its sides complementary.  Hence the room bound is `≤ 2`, never `3`.
* `hdoor` — every edge borders `≤ 2` triangles (the pseudomanifold bound, independent
  of the labelling).

Together `hdoor` + `hsimplex` are precisely the hypotheses of
`SpernerTuckerDoorGraph.doorGraph_degree_le_two`, so **the full all-signs
complementary-edge door graph of the hexagon disk is a disjoint union of paths and
cycles on every antipodal labelling** — the engine's structural hypothesis, realized
for the first time by the *complete* (interior + boundary, all-sign) FT door graph on
real n = 2 geometry, not just its interior spoke part.

* `boundary_door_count_even` — yet the number of **boundary doors** (complementary
  boundary edges) is always **even**, so the parity engine cannot fire on it.
* `half_boundary_parity_not_invariant` — and passing to a fundamental domain of the
  antipodal action (three consecutive boundary edges) does *not* rescue an odd seed:
  the half-ring complementary count is even on some labellings and odd on others.

## Honest status

A **scoping result**, sharpening the two existing obstructions: the complete door
graph *does* satisfy the engine's max-degree hypothesis (a genuine positive: the FT
door structure over all signs is paths-and-cycles), but **no unsigned door count
supplies the odd boundary seed** — neither the full boundary ring (even) nor its
antipodal-quotient half (not a parity invariant).  The remaining FT input is therefore
provably an *oriented / antipodally-signed* count, not any door-counting parity.

Self-contained: imports Mathlib only.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib

namespace SpernerTuckerHexagonFullDoorGraph

open Finset

/-! ## Labelling model (same encoding as `SpernerTuckerHexagon`) -/

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The six boundary labels from three free labels `a,b,c` on `v0,v1,v2`, with the
antipodal condition `v(i+3) = -v(i)` built in. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- Cyclic successor around the hexagon boundary. -/
def rot (i : Fin 6) : Fin 6 := i + 1

/-! ## The hexagon disk triangulation and complementary-edge doors

`Tri = Fin 6` are the six triangles `T i = (centre, v i, v (i+1))`; `Edge = Fin 12`
with `0..5` the spokes (`spoke i = centre–v i`) and `6..11` the boundary edges
(`boundary i = v i–v (i+1)`).  Same indexing as `SpernerTuckerHexagonPseudomanifold`. -/

abbrev Tri := Fin 6
abbrev Edge := Fin 12

/-- Spoke `centre–v i` as edge index `0..5`. -/
def spoke (i : Fin 6) : Edge := i.castLE (by norm_num)
/-- Boundary edge `v i–v (i+1)` as edge index `6..11`. -/
def boundaryE (i : Fin 6) : Edge := ⟨6 + i.val, by omega⟩

/-- Geometric incidence: triangle `t` carries its three sides `spoke t`,
`spoke (t+1)`, `boundaryE t`. -/
def geo (t : Tri) (e : Edge) : Prop := e = spoke t ∨ e = spoke (t + 1) ∨ e = boundaryE t

instance : DecidableRel geo := fun t e => by unfold geo; infer_instance

/-- Whether an edge is **complementary** under the labelling `(a,b,c,d)` (centre `d`):
a spoke `centre–v i` is complementary iff `d = -v i`; a boundary edge `v i–v (i+1)` iff
`v (i+1) = -v i`. -/
def edgeCompl (a b c d : Fin 4) (e : Edge) : Bool :=
  if h : e.val < 6 then
    decide (d = negL (V a b c ⟨e.val, h⟩))
  else
    decide (V a b c (rot ⟨e.val - 6, by omega⟩) = negL (V a b c ⟨e.val - 6, by omega⟩))

/-- **Door incidence**: `t` has door `e` iff `e` is a side of `t` and `e` is
complementary — doors are *all* complementary edges, interior and boundary. -/
def inc (a b c d : Fin 4) (t : Tri) (e : Edge) : Prop := geo t e ∧ edgeCompl a b c d e

instance (a b c d : Fin 4) : DecidableRel (inc a b c d) := fun t e => by
  unfold inc; infer_instance

/-! ## The two engine hypotheses, for every antipodal labelling -/

/-- **Engine `hsimplex`.**  Every triangle has at most two complementary doors, for
every antipodal labelling.  Verified over all `4⁴ = 256` labellings. -/
theorem hsimplex : ∀ a b c d : Fin 4, ∀ t : Tri, #{e | inc a b c d t e} ≤ 2 := by decide

/-- **No fully-complementary triangle.**  The sharp reason `hsimplex` holds: no triangle
ever has all three of its sides complementary — the room degree is `≤ 2`, never `3`. -/
theorem no_triangle_all_complementary :
    ∀ a b c d : Fin 4, ∀ t : Tri, #{e | inc a b c d t e} ≠ 3 := by decide

/-- **Engine `hdoor`.**  Every edge borders at most two triangles (the pseudomanifold
bound), hence at most two triangles carry it as a door.  Independent of the labelling. -/
theorem hdoor : ∀ a b c d : Fin 4, ∀ e : Edge, #{t | inc a b c d t e} ≤ 2 := by decide

/-! ## The boundary doors carry no odd seed -/

/-- Number of **boundary doors**: complementary boundary edges `v i–v (i+1)`. -/
def boundaryDoors (a b c : Fin 4) : ℕ :=
  ((List.finRange 6).filter (fun i => decide (V a b c (rot i) = negL (V a b c i)))).length

/-- **The boundary-door count is always even.**  So the parity engine (which needs an
*odd* number of boundary doors) cannot fire on the unsigned complementary-edge doors. -/
theorem boundary_door_count_even : ∀ a b c : Fin 4, Even (boundaryDoors a b c) := by decide

/-- Complementary boundary edges in a **fundamental domain** of the antipodal action:
three consecutive boundary edges `bd 0, bd 1, bd 2`. -/
def halfBoundaryDoors (a b c : Fin 4) : ℕ :=
  (([0, 1, 2] : List (Fin 6)).filter (fun i => decide (V a b c (rot i) = negL (V a b c i)))).length

/-- **The antipodal-quotient half-ring count is not a parity invariant.**  Some
labellings give an even half-ring count and others an odd one, so restricting to a
fundamental domain of the antipodal action does not manufacture the odd seed either. -/
theorem half_boundary_parity_not_invariant :
    (∃ a b c : Fin 4, Even (halfBoundaryDoors a b c)) ∧
    (∃ a b c : Fin 4, Odd (halfBoundaryDoors a b c)) := by decide

#print axioms hsimplex
#print axioms no_triangle_all_complementary
#print axioms hdoor
#print axioms boundary_door_count_even
#print axioms half_boundary_parity_not_invariant

end SpernerTuckerHexagonFullDoorGraph
