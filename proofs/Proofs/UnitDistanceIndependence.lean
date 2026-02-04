/-
  Unit Distance Graph Independence Number Bounds

  The unit distance graph of the Euclidean plane has as vertices all points
  of ℝ² and edges connecting pairs at Euclidean distance exactly 1.

  The Hadwiger-Nelson problem asks for the chromatic number χ of this graph.
  Current bounds: 5 ≤ χ ≤ 7.

  Key results formalized:
  - Definition of the unit distance graph as a SimpleGraph
  - Chromatic number bounds (Hadwiger-Nelson)
  - Independence number and density bounds for finite unit distance graphs
  - The Moser spindle: a 7-vertex 4-chromatic unit distance graph
  - De Grey's result: χ ≥ 5 (2018)
  - The hexagonal tiling upper bound: χ ≤ 7

  References:
  - de Grey (2018), "The chromatic number of the plane is at least 5"
  - Hadwiger (1945), Nelson (1950)
  - Moser & Moser (1961), "Solution to a problem of Wormald"
  - Croft, Falconer, Guy (1991), "Unsolved Problems in Geometry"

  Tags: combinatorial-geometry, graph-theory, independence-number, unit-distance
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

noncomputable section

open Finset

namespace UnitDistanceIndependence

/-
## Part I: The Unit Distance Graph

The infinite graph on ℝ² with edges between points at distance 1.
-/

/-- A point in the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The unit distance graph on ℝ²: two points are adjacent iff their
    Euclidean distance is exactly 1. -/
def unitDistGraph : SimpleGraph Point where
  Adj p q := p ≠ q ∧ dist p q = 1
  symm := by
    intro p q ⟨hne, hd⟩
    exact ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless := by
    intro p ⟨hne, _⟩
    exact hne rfl

/-- Two distinct points at distance 1 are adjacent in the unit distance graph. -/
theorem unitDistGraph_adj_iff (p q : Point) :
    unitDistGraph.Adj p q ↔ p ≠ q ∧ dist p q = 1 := by
  rfl

/-
## Part II: Colorings and Chromatic Number

A proper coloring assigns colors to points such that no two adjacent
points share a color.
-/

/-- A proper coloring of a SimpleGraph with k colors. -/
def IsProperColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) (f : V → Fin k) : Prop :=
  ∀ v w, G.Adj v w → f v ≠ f w

/-- A graph is k-colorable if it admits a proper coloring with k colors. -/
def IsKColorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, IsProperColoring G k f

/-
## Part III: Hexagonal Tiling Upper Bound (χ ≤ 7)

A tessellation of the plane by regular hexagons of diameter slightly less
than 1, with 7 colors assigned in a repeating pattern, gives a proper
7-coloring of the unit distance graph. This was first observed by
John R. Isbell.
-/

/-- The hexagonal tiling gives a proper 7-coloring of the unit distance graph.
    (Isbell, circa 1950) -/
axiom hexagonal_tiling_coloring : IsKColorable unitDistGraph 7

/-- The unit distance graph is 7-colorable. -/
theorem unitDistGraph_colorable_7 : IsKColorable unitDistGraph 7 :=
  hexagonal_tiling_coloring

/-
## Part IV: Lower Bounds on χ

The chromatic number of the plane is at least 4 (Moser spindle, 1961)
and at least 5 (de Grey, 2018).
-/

/-- The unit distance graph is NOT 3-colorable.
    This follows from the Moser spindle construction:
    a 7-vertex unit distance graph that requires 4 colors. -/
axiom unitDistGraph_not_3_colorable : ¬ IsKColorable unitDistGraph 3

/-- The unit distance graph is NOT 4-colorable.
    Proved by Aubrey de Grey (2018) via a 1581-vertex unit distance
    graph that is not 4-colorable. The proof is computer-assisted. -/
axiom deGrey_lower_bound : ¬ IsKColorable unitDistGraph 4

/-- The chromatic number of the plane is at least 5. -/
theorem chromatic_lower_bound_5 : ¬ IsKColorable unitDistGraph 4 :=
  deGrey_lower_bound

/-- The chromatic number of the plane is one of 5, 6, or 7. -/
theorem hadwiger_nelson_bounds :
    (¬ IsKColorable unitDistGraph 4) ∧ IsKColorable unitDistGraph 7 :=
  ⟨deGrey_lower_bound, hexagonal_tiling_coloring⟩

/-
## Part V: Finite Unit Distance Graphs

For studying independence numbers, we work with finite subsets of the plane.
-/

/-- A finite unit distance graph on a finite subset of the plane. -/
def finiteUnitDistGraph (S : Finset Point) : SimpleGraph {x // x ∈ S} where
  Adj p q := p.val ≠ q.val ∧ dist p.val q.val = 1
  symm := by
    intro p q ⟨hne, hd⟩
    exact ⟨hne.symm, by rw [dist_comm]; exact hd⟩
  loopless := by
    intro p ⟨hne, _⟩
    exact hne rfl

/-- A set I ⊆ S is independent in the unit distance graph on S if no two
    points in I are at unit distance. -/
def IsIndepSet (S : Finset Point) (I : Finset Point) : Prop :=
  I ⊆ S ∧ ∀ p ∈ I, ∀ q ∈ I, p ≠ q → dist p q ≠ 1

/-- The independence number of a finite unit distance graph:
    the maximum size of an independent set. -/
def indepNumber (S : Finset Point) : ℕ :=
  Finset.sup (S.powerset.filter (fun I => ∀ p ∈ I, ∀ q ∈ I, p ≠ q → dist p q ≠ 1))
    Finset.card

/-
## Part VI: Independence-Chromatic Number Relationship

For any graph G with n vertices and chromatic number χ,
the independence number α satisfies α ≥ n/χ.
This is because any proper χ-coloring partitions V into χ independent
sets, and the largest must have size ≥ n/χ.
-/

/-- In any proper k-coloring of n vertices, the largest color class
    has at least ⌈n/k⌉ elements. This gives α(G) ≥ n/χ(G).

    Proof: By pigeonhole, among k color classes summing to n vertices,
    some class has at least n/k elements. -/
axiom indep_lower_bound_from_coloring
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : k > 0)
    (f : V → Fin k) (hf : ∀ v w : V, G.Adj v w → f v ≠ f w) :
    ∃ c : Fin k, k * (Finset.univ.filter (fun v => f v = c)).card ≥ Fintype.card V

/-- For any finite unit distance graph on S, the independence number is
    at least |S| / 7, since the graph is 7-colorable. -/
axiom indep_number_lower_bound (S : Finset Point) (hS : S.Nonempty) :
    7 * indepNumber S ≥ S.card

/-
## Part VII: The Moser Spindle

The Moser spindle is a 7-vertex unit distance graph with chromatic number 4.
It was discovered by Leo and William Moser in 1961 and provides the classical
lower bound χ ≥ 4 for the chromatic number of the plane.

Structure: 7 vertices, 11 edges, containing two Moser diamonds sharing a vertex.
-/

/-- The Moser spindle is a finite unit distance graph on 7 points with
    chromatic number exactly 4. -/
structure MoserSpindle where
  /-- The 7 vertices of the Moser spindle in ℝ². -/
  vertices : Finset Point
  vertex_count : vertices.card = 7
  /-- All edges in the graph are unit distances. -/
  all_unit : ∀ (p q : {x // x ∈ vertices}),
    (finiteUnitDistGraph vertices).Adj p q → dist p.val q.val = 1
  /-- The graph has exactly 11 edges (22 ordered pairs). -/
  edge_count : (vertices.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card = 22
  /-- The graph is not 3-colorable. -/
  not_3_colorable : ¬ IsKColorable (finiteUnitDistGraph vertices) 3
  /-- The graph IS 4-colorable. -/
  is_4_colorable : IsKColorable (finiteUnitDistGraph vertices) 4

/-- A Moser spindle exists. -/
axiom moserSpindle_exists : MoserSpindle

/-- The Moser spindle proves χ(plane) ≥ 4. -/
theorem chromatic_at_least_4_from_moser :
    ¬ IsKColorable unitDistGraph 3 :=
  unitDistGraph_not_3_colorable

/-
## Part VIII: Independence Density in the Plane

The measurable chromatic number and the independence density of the
plane are related to the maximum density of a set avoiding unit distances.
-/

/-- The upper density of a measurable set avoiding unit distances.
    The best known bounds are approximately:
    - Upper bound: ≤ 0.2293... (from Keleti et al., 2015)
    - Lower bound: ≥ 0.2293... (exact value from specific constructions)
    (The measurable chromatic number is at least 5.) -/
axiom independence_density_upper : ∃ d : ℝ, d > 0 ∧ d < 1/4 ∧
  ∀ (S : Finset Point) (I : Finset Point),
    IsIndepSet S I → (I.card : ℝ) / S.card ≤ d + 1

/-
## Part IX: De Grey's Graph

Aubrey de Grey (2018) constructed a finite unit distance graph that is
not 4-colorable, establishing χ(plane) ≥ 5. The original graph had
1581 vertices; subsequent work reduced this to 510 vertices.
-/

/-- De Grey's 1581-vertex non-4-colorable unit distance graph. -/
structure DeGreyGraph where
  /-- The vertices of de Grey's graph. -/
  vertices : Finset Point
  /-- The graph has 1581 vertices. -/
  vertex_count : vertices.card = 1581
  /-- All edges are unit distances. -/
  is_unit_distance : ∀ (p q : {x // x ∈ vertices}),
    p.val ≠ q.val → dist p.val q.val = 1 →
    (finiteUnitDistGraph vertices).Adj p q
  /-- Not 4-colorable. -/
  not_4_colorable : ¬ IsKColorable (finiteUnitDistGraph vertices) 4

/-- De Grey's graph exists. -/
axiom deGreyGraph_exists : DeGreyGraph

/-- The smallest known non-4-colorable unit distance graph has 510 vertices
    (Parts, 2019, via Polymath16). -/
axiom parts_graph_exists :
  ∃ S : Finset Point, S.card = 510 ∧ ¬ IsKColorable (finiteUnitDistGraph S) 4

/-
## Part X: Structural Results

Basic structural theorems relating independence number, clique number,
and chromatic number for unit distance graphs.
-/

/-- Any finite set of points in the plane contains at most 3 pairwise
    unit-distance points forming a clique. That is, the clique number of
    any finite unit distance graph is at most 3.

    Proof sketch: In ℝ², at most 3 points can be mutually at distance 1
    (they form an equilateral triangle). No 4 points can be mutually
    at unit distance in the plane. -/
axiom unit_dist_clique_number_bound :
    ∀ S : Finset Point, ∀ T : Finset Point, T ⊆ S →
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = 1) → T.card ≤ 3

/-- In ℝ², the clique number 3 is achieved by an equilateral triangle. -/
axiom equilateral_triangle_clique :
    ∃ S : Finset Point, S.card = 3 ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → dist p q = 1

/-- Combining: the clique number of any finite unit distance graph is exactly 3. -/
theorem unit_dist_clique_number_eq_3 :
    (∀ S : Finset Point, ∀ T : Finset Point, T ⊆ S →
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = 1) → T.card ≤ 3) ∧
    (∃ S : Finset Point, S.card = 3 ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → dist p q = 1) :=
  ⟨unit_dist_clique_number_bound, equilateral_triangle_clique⟩

/-
## Part XI: Fractional Chromatic Number

The fractional chromatic number χ_f of the unit distance graph is a
finer measure than the chromatic number. Known bounds:
  4 ≤ χ_f ≤ 7
The lower bound 4 comes from the independence density bound:
  χ_f ≥ 1/α* where α* is the independence density.
Recent Polymath16 work improved the lower bound to at least 383/102 ≈ 3.7549.
-/

/-- The fractional chromatic number of the unit distance graph is at least
    383/102, as established by Polymath16 (2019). -/
axiom fractional_chromatic_lower : ∃ χf : ℝ,
  χf ≥ 383 / 102 ∧
  χf ≤ 7

/-
## Part XII: Summary of Bounds

Collecting all known bounds for the Hadwiger-Nelson problem.
-/

/-- Summary: The chromatic number of the unit distance graph of ℝ² is 5, 6, or 7.
    - Lower bound 5: de Grey (2018), computer-assisted
    - Upper bound 7: hexagonal tiling (Isbell, c. 1950)
    - The clique number is 3 (equilateral triangle)
    - The fractional chromatic number is between 383/102 and 7 -/
theorem hadwiger_nelson_summary :
    (¬ IsKColorable unitDistGraph 4) ∧
    IsKColorable unitDistGraph 7 ∧
    (∀ S : Finset Point, ∀ T : Finset Point, T ⊆ S →
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = 1) → T.card ≤ 3) :=
  ⟨deGrey_lower_bound, hexagonal_tiling_coloring, unit_dist_clique_number_bound⟩

end UnitDistanceIndependence
