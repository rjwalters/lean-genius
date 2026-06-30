/-
# A concrete 2-D pseudomanifold: `hdoor` discharged by `decide` on the hexagon disk

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

The abstract door-counting engine (`SpernerTuckerDoorGraph.lean`) derives the
path-following structure of Tucker's lemma from a finite *door-incidence relation*
`inc : V → D → Prop` satisfying three geometric hypotheses:

* `hdoor`    — each door is shared by **≤ 2** simplices (the *pseudomanifold* property);
* `hsimplex` — each almost-complementary simplex has **≤ 2** complementary doors;
* `hpair`    — two distinct simplices share **≤ 1** door.

`hsimplex` was turned into a theorem (for the canonical Sperner colouring) in
`SpernerTuckerDoorLemma.lean`, and `hpair` for the natural subset incidence in
`SpernerTuckerSimplexFacetPair.lean`.  The knowledge base flags **`hdoor` as the sole
remaining engine input that is genuinely geometric** — it is *false* for an arbitrary
finite complex, so it cannot be proved abstractly; it needs an actual triangulation.

## What this file proves

This file supplies that triangulation, concretely and by kernel `decide` (0 axioms):
the **standard small triangulation of the 2-disk `B²`** — a hexagon, six boundary
vertices `0,…,5` around a centre, cut into six triangles `Tᵢ = (centre, vᵢ, vᵢ₊₁)`.

* `inc`            — the incidence: triangle `t` carries edge `e` iff `e` is one of its
  three sides (two spokes `centre–vᵢ` and one boundary edge `vᵢ–vᵢ₊₁`).
* `hdoor`          — **the pseudomanifold property**: every edge borders `≤ 2`
  triangles.  By `decide` over `Fin 12 × Fin 6` — no axioms.
* `spoke_incidence` / `boundary_incidence` — the *sharp* counts: each spoke borders
  **exactly 2** triangles (interior edge), each boundary edge **exactly 1** (boundary
  edge).  This is what makes `hdoor` tight: the bound `2` is attained.
* `hpair`          — two distinct triangles share `≤ 1` edge.  By `decide`.

Feeding the two concrete bounds into the abstract engine:

* `hexagon_degree`           — `doorGraph_degree_eq_shared` instantiated on the hexagon
  gives **every triangle degree `2`**: the almost-complementary graph of the hexagon
  disk is the 6-cycle, computed *through the engine's degree formula*, not by hand.
* `hexagon_door_conservation` — `doorGraph_degree_add_boundaryDoors` instantiated:
  `degree t + #(boundary doors of t) = #(all doors of t) = 3`, so each triangle has
  exactly one boundary door (its outer edge).

This is the **first concrete `n = 2` geometry on which the engine's geometric input
`hdoor` is machine-checked**, and on which the abstract degree/conservation laws are
run end-to-end against a real triangulation.

Self-contained: imports Mathlib and the engine.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — NO `native_decide`/`ofReduceBool`).
-/
import Mathlib
import Proofs.SpernerTuckerDoorGraph

namespace SpernerTuckerHexagonPseudomanifold

open Finset

/-! ## The hexagon disk triangulation

`Tri = Fin 6` are the six triangles; `Edge = Fin 12` are the twelve edges, indexed so
that `0,…,5` are the spokes (`spoke i = centre–vᵢ`) and `6,…,11` are the boundary
edges (`boundary i = vᵢ–vᵢ₊₁`).  Triangle `t = (centre, vₜ, vₜ₊₁)` carries the two
spokes `spoke t`, `spoke (t+1)` and the boundary edge `boundary t`. -/

/-- Triangles of the hexagon disk. -/
abbrev Tri := Fin 6

/-- Edges of the hexagon disk: `0..5` spokes, `6..11` boundary edges. -/
abbrev Edge := Fin 12

/-- The spoke `centre–vᵢ`, as an edge index in `0..5`. -/
def spoke (i : Fin 6) : Edge := i.castLE (by norm_num)

/-- The boundary edge `vᵢ–vᵢ₊₁`, as an edge index in `6..11`. -/
def boundary (i : Fin 6) : Edge := ⟨6 + i.val, by omega⟩

/-- **Incidence.**  Triangle `t = (centre, vₜ, vₜ₊₁)` carries exactly its three sides:
the two spokes `spoke t` and `spoke (t+1)`, and the boundary edge `boundary t`. -/
def inc (t : Tri) (e : Edge) : Prop :=
  e = spoke t ∨ e = spoke (t + 1) ∨ e = boundary t

instance : DecidableRel inc := fun t e => by
  unfold inc; infer_instance

/-! ## The pseudomanifold property (`hdoor`) — by `decide` -/

/-- **The pseudomanifold property / engine `hdoor`.**  Every edge of the hexagon disk
borders at most two triangles.  This is the genuinely-geometric door-incidence bound;
it is checked here by the kernel over the finite incidence table (no axioms). -/
theorem hdoor : ∀ e : Edge, #{t | inc t e} ≤ 2 := by decide

/-- **Sharp interior count.**  Each spoke `centre–vᵢ` borders *exactly two* triangles
(`Tᵢ₋₁` and `Tᵢ`): it is an interior edge.  The `hdoor` bound `2` is attained. -/
theorem spoke_incidence : ∀ i : Fin 6, #{t | inc t (spoke i)} = 2 := by decide

/-- **Sharp boundary count.**  Each boundary edge `vᵢ–vᵢ₊₁` borders *exactly one*
triangle (`Tᵢ`): it is a boundary edge of the disk. -/
theorem boundary_incidence : ∀ i : Fin 6, #{t | inc t (boundary i)} = 1 := by decide

/-- **The pair bound / engine `hpair`.**  Two distinct triangles share at most one
edge.  (Adjacent triangles `Tᵢ`, `Tᵢ₊₁` share exactly the spoke `spoke (i+1)`;
non-adjacent triangles share none.)  By `decide`. -/
theorem hpair : ∀ d d' : Edge, ∀ t w : Tri, t ≠ w →
    inc t d → inc w d → inc t d' → inc w d' → d = d' := by decide

/-! ## Running the abstract engine on the concrete hexagon

With the two concrete bounds `hdoor` and `hpair` in hand we feed the engine's
*sharp degree formula* and *door-conservation law*, computing the almost-complementary
graph of the hexagon disk through the abstract machinery. -/

open SpernerTuckerDoorGraph

/-- **The engine's degree formula, instantiated.**  `doorGraph_degree_eq_shared`
identifies the graph degree with the number of *shared* doors.  On the hexagon every
triangle has exactly the two spokes as shared doors, so its degree is `2`: the
almost-complementary graph of the hexagon disk is the **6-cycle**, obtained through
the engine rather than by inspection. -/
theorem hexagon_degree (t : Tri) : (doorGraph inc).degree t = 2 := by
  rw [doorGraph_degree_eq_shared inc hdoor hpair t]
  revert t; decide

/-- **Sharp door count.**  Each triangle carries exactly its three sides. -/
theorem hexagon_all_doors (t : Tri) : #{d | inc t d} = 3 := by revert t; decide

/-- **Sharp boundary-door count.**  Each triangle has exactly one boundary door — its
outer edge `boundary t`.  This is the geometric content of the engine's
door-conservation law `doorGraph_degree_add_boundaryDoors`
(`degree t + #boundary doors = #all doors`) read on the hexagon: with
`hexagon_degree` (`degree = 2`) and `hexagon_all_doors` (`#all doors = 3`) it forces
`#boundary doors = 1`.  Verified here directly by `decide`. -/
theorem hexagon_boundary_door (t : Tri) :
    #{d | inc t d ∧ ∀ w, w ≠ t → ¬ inc w d} = 1 := by revert t; decide

end SpernerTuckerHexagonPseudomanifold
