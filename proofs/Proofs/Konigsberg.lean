/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, enhanced for lean-genius
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum

/-!
# Königsberg Bridges Problem

## What This Proves
The Seven Bridges of Königsberg problem asks: can one walk through the city
crossing each of its seven bridges exactly once? Euler proved in 1736 that
this is impossible, founding the field of graph theory in the process.

This proof formalizes the impossibility by showing that the Königsberg graph
has four vertices of odd degree, while an Eulerian path requires 0 or 2.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `SimpleGraph` and `IsEulerian`
  from `Mathlib.Combinatorics.SimpleGraph.Trails`.
- **Original Contributions:** The graph modeling and degree calculations are
  presented pedagogically to illustrate Euler's original reasoning.
- **Proof Techniques Demonstrated:** Decidable instances for finite graphs,
  degree counting, case analysis.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `SimpleGraph` : Undirected graphs without self-loops
- `Walk.IsEulerian` : Predicate for Eulerian trails
- `Walk.IsEulerian.card_odd_degree` : Key theorem about odd-degree vertices

Historical Note: Euler's 1736 paper "Solutio problematis ad geometriam situs
pertinentis" (Solution of a problem relating to the geometry of position)
is considered the first paper in graph theory and topology.
-/

namespace Konigsberg

/-!
## Part 1: Modeling the Königsberg Graph

The city of Königsberg (now Kaliningrad, Russia) was built on both sides of
the Pregel River, with two islands in the middle. Seven bridges connected
these four landmasses.

We model this as a graph with:
- 4 landmass vertices (V1, V2, V3, V4)
- 7 bridge vertices (B1, B2, B3, B4, B5, B6, B7)

Each bridge connects exactly two landmasses, so bridge vertices have degree 2.
The landmasses have degrees: V1=5, V2=3, V3=3, V4=3.

Why use bridge vertices? This creates a simple graph (no multi-edges) while
faithfully representing the multiple bridges between landmasses.
-/

/-- Vertices of the Königsberg graph: 4 landmasses and 7 bridges -/
inductive Verts : Type
  | V1  -- North bank (Altstadt-Löbenicht)
  | V2  -- South bank (Kneiphof Island)
  | V3  -- West island (Vorstadt)
  | V4  -- East island (Lomse)
  | B1  -- Bridge 1: V1 to V2
  | B2  -- Bridge 2: V1 to V2
  | B3  -- Bridge 3: V1 to V4
  | B4  -- Bridge 4: V1 to V3
  | B5  -- Bridge 5: V1 to V3
  | B6  -- Bridge 6: V2 to V4
  | B7  -- Bridge 7: V3 to V4
  deriving DecidableEq, Fintype

open Verts

/-!
## Part 2: Edge Set Definition

We define the edges as pairs (landmass, bridge) where the bridge touches
that landmass. The full path across a bridge goes: landmass → bridge → landmass.
-/

/-- The edge list: each bridge connects to exactly two landmasses -/
def edges : List (Verts × Verts) :=
  [(V1, B1), (V1, B2), (V1, B3), (V1, B4), (V1, B5),  -- V1 connects to 5 bridges
   (B1, V2), (B2, V2),                                 -- B1, B2 go to V2
   (B3, V4),                                           -- B3 goes to V4
   (B4, V3), (B5, V3),                                 -- B4, B5 go to V3
   (V2, B6), (B6, V4),                                 -- B6: V2 to V4
   (V3, B7), (B7, V4)]                                 -- B7: V3 to V4

/-- Adjacency relation: symmetric membership in edge list -/
def adj (v w : Verts) : Bool := (v, w) ∈ edges || (w, v) ∈ edges

/-!
## Part 3: The Königsberg Simple Graph

We construct a `SimpleGraph` from our adjacency relation, proving it's
symmetric and irreflexive (no self-loops).
-/

/-- The Königsberg bridges graph as a SimpleGraph -/
@[simps]
def graph : SimpleGraph Verts where
  Adj v w := adj v w
  symm := by dsimp [Symmetric, adj]; decide
  loopless := by dsimp [Irreflexive, adj]; decide

instance : DecidableRel graph.Adj := fun a b => inferInstanceAs <| Decidable (adj a b)

/-!
## Part 4: Degree Calculation

The key insight of Euler's proof: the degree of each vertex determines
whether an Eulerian path exists.

- Bridge vertices: degree 2 (connect exactly two landmasses)
- V1 (north bank): degree 5 (connected to 5 bridges)
- V2, V3, V4: degree 3 each (connected to 3 bridges each)
-/

/-- Explicit degree calculation for each vertex -/
def degree : Verts → ℕ
  | V1 => 5  -- 5 bridges touch the north bank
  | V2 => 3  -- 3 bridges touch the south bank
  | V3 => 3  -- 3 bridges touch the west island
  | V4 => 3  -- 3 bridges touch the east island
  | B1 => 2 | B2 => 2 | B3 => 2 | B4 => 2 | B5 => 2 | B6 => 2 | B7 => 2

/-- The graph degree matches our explicit calculation -/
@[simp]
lemma degree_eq_degree (v : Verts) : graph.degree v = degree v := by cases v <;> rfl

/-!
## Part 5: Identifying Odd-Degree Vertices

A vertex has odd degree if an odd number of edges touch it.
All four landmasses have odd degree (5, 3, 3, 3).
All seven bridges have even degree (2 each).
-/

/-- Characterization of vertices with odd degree -/
lemma not_even_degree_iff (w : Verts) :
    ¬Even (degree w) ↔ w = V1 ∨ w = V2 ∨ w = V3 ∨ w = V4 := by
  cases w <;> decide

/-- The set of odd-degree vertices is exactly the four landmasses -/
lemma setOf_odd_degree_eq :
    {v | Odd (graph.degree v)} = {Verts.V1, Verts.V2, Verts.V3, Verts.V4} := by
  ext w
  simp [not_even_degree_iff, Nat.odd_iff_not_even]

/-!
## Part 6: The Main Theorem

Euler's theorem states that a connected graph has an Eulerian path if and only if
it has exactly 0 or 2 vertices of odd degree.

The Königsberg graph has 4 vertices of odd degree, so no Eulerian path exists.
This means it's impossible to walk through Königsberg crossing each bridge
exactly once.
-/

/-- **The Königsberg Bridges Theorem**

There is no Eulerian path in the Königsberg graph. This means it's impossible
to walk through the city crossing each of the seven bridges exactly once.

The proof uses `IsEulerian.card_odd_degree`, which states that if an Eulerian
path exists, the number of odd-degree vertices must be 0 or 2. Since the
Königsberg graph has 4 odd-degree vertices, no Eulerian path exists. -/
theorem not_isEulerian {u v : Verts} (p : graph.Walk u v) (h : p.IsEulerian) : False := by
  -- Get the constraint on odd-degree vertex count from Eulerian path theory
  have h := h.card_odd_degree
  -- Substitute in our explicit characterization
  have h' := setOf_odd_degree_eq
  apply_fun Fintype.card at h'
  rw [h'] at h
  -- The set {V1, V2, V3, V4} has cardinality 4, not 0 or 2
  simp at h

/-!
## Historical Notes

### Euler's Original Paper (1736)

Euler didn't use "graphs" explicitly. He realized the key abstraction:
only the connections matter, not the exact layout. He observed:

1. Each time you cross a bridge to a landmass, you must leave by another bridge
2. For interior landmasses (not start/end), bridges come in pairs
3. Therefore interior landmasses must have even degree
4. At most 2 landmasses can have odd degree (start and end)

Since Königsberg has 4 odd-degree vertices, the walk is impossible.

### Why This Matters

This problem marked the birth of:
- **Graph theory**: Abstracting structure as vertices and edges
- **Topology**: The study of properties preserved under continuous deformation
- **Network analysis**: Understanding connectivity in complex systems

Today, Eulerian paths are used in:
- DNA sequencing (assembling fragments)
- Circuit design (single-stroke drawings)
- Route optimization (postal carriers, garbage trucks)
-/

#check @not_isEulerian

end Konigsberg
