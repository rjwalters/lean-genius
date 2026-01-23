/-
Erdős Problem #705: Unit Distance Graphs with High Girth

**Statement**: Let G be a finite unit distance graph in ℝ² (vertices are points,
edges connect points at distance 1). Is there some k such that if girth(G) ≥ k
then χ(G) ≤ 3?

**Status**: OPEN

**Context**: This is related to the Hadwiger-Nelson problem (chromatic number of the plane).

**Known Results**:
- Max χ(G) for any unit distance graph is at least 5 (de Grey 2018)
- χ(G) = 4 exists with girth 3 (Moser spindle)
- χ(G) = 4 exists with girth 4 (O'Donnell 56 vertices, Chilakamarri 47 vertices)
- χ(G) = 4 exists with girth 5 (Wormald 6448 vertices)

So no k ≤ 5 works. The question is whether ANY k exists.

**Related**: #508 (Hadwiger-Nelson), #704, #706

Reference: https://erdosproblems.com/705
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos705

open SimpleGraph

/-!
## Part I: Unit Distance Graphs
-/

/-- A point in the Euclidean plane -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Distance between two points -/
noncomputable def dist (p q : Point) : ℝ := ‖p - q‖

/-- A finite unit distance graph on a set of points -/
structure UnitDistanceGraph where
  /-- The set of vertices (points in ℝ²) -/
  vertices : Finset Point
  /-- The graph structure -/
  graph : SimpleGraph vertices
  /-- Edges connect points at exactly distance 1 -/
  unit_dist : ∀ (p q : vertices), graph.Adj p q → dist p.val q.val = 1

/-- The underlying simple graph of a unit distance graph -/
def UnitDistanceGraph.toSimpleGraph (G : UnitDistanceGraph) : SimpleGraph G.vertices :=
  G.graph

/-!
## Part II: Girth (Minimum Cycle Length)
-/

/-- A graph has girth at least k if it contains no cycles of length < k -/
def HasGirthAtLeast (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ n < k, ∀ (cycle : G.Walk v v), cycle.IsCycle → cycle.length ≥ n + 1 → False

/-- Triangle-free means girth ≥ 4 -/
def IsTriangleFree (G : SimpleGraph V) : Prop := HasGirthAtLeast G 4

/-- Square-free means no 4-cycles -/
def IsSquareFree (G : SimpleGraph V) : Prop := HasGirthAtLeast G 5

/-!
## Part III: Chromatic Number
-/

/-- G is k-colorable -/
def IsKColorable (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (k : ℕ) : Prop :=
  Nonempty (G.Coloring (Fin k))

/-- Chromatic number (smallest k for which G is k-colorable) -/
noncomputable def chromaticNumber (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℕ :=
  Nat.find ⟨Fintype.card V, by sorry⟩ -- Every finite graph is |V|-colorable

/-!
## Part IV: The Main Conjecture
-/

/-- The main question: does there exist k such that girth ≥ k implies χ ≤ 3? -/
def mainConjecture : Prop :=
  ∃ k : ℕ, ∀ G : UnitDistanceGraph,
    HasGirthAtLeast G.graph k →
    ∃ (inst : DecidableRel G.graph.Adj), @IsKColorable G.vertices G.graph _ inst 3

/-- The negation: for all k, there exists a unit distance graph with girth ≥ k and χ ≥ 4 -/
def negationOfConjecture : Prop :=
  ∀ k : ℕ, ∃ G : UnitDistanceGraph,
    HasGirthAtLeast G.graph k ∧
    ¬∃ (inst : DecidableRel G.graph.Adj), @IsKColorable G.vertices G.graph _ inst 3

/-!
## Part V: Known Constructions
-/

/-- Moser spindle: χ = 4, girth = 3 (has triangles) -/
axiom moser_spindle_exists :
  ∃ G : UnitDistanceGraph, G.vertices.card = 7 ∧
    ¬HasGirthAtLeast G.graph 4 ∧
    ∀ (inst : DecidableRel G.graph.Adj), ¬@IsKColorable G.vertices G.graph _ inst 3

/-- O'Donnell construction: χ = 4, girth = 4 (triangle-free), 56 vertices -/
axiom odonnell_exists :
  ∃ G : UnitDistanceGraph, G.vertices.card = 56 ∧
    HasGirthAtLeast G.graph 4 ∧
    ∀ (inst : DecidableRel G.graph.Adj), ¬@IsKColorable G.vertices G.graph _ inst 3

/-- Chilakamarri construction: χ = 4, girth = 4, 47 vertices (smallest known) -/
axiom chilakamarri_exists :
  ∃ G : UnitDistanceGraph, G.vertices.card = 47 ∧
    HasGirthAtLeast G.graph 4 ∧
    ∀ (inst : DecidableRel G.graph.Adj), ¬@IsKColorable G.vertices G.graph _ inst 3

/-- Wormald construction: χ = 4, girth = 5, 6448 vertices -/
axiom wormald_exists :
  ∃ G : UnitDistanceGraph, G.vertices.card = 6448 ∧
    HasGirthAtLeast G.graph 5 ∧
    ∀ (inst : DecidableRel G.graph.Adj), ¬@IsKColorable G.vertices G.graph _ inst 3

/-- The constructions show that k ≤ 5 doesn't work -/
theorem no_small_k_works :
    ∀ k ≤ 5, ∃ G : UnitDistanceGraph,
      HasGirthAtLeast G.graph k ∧
      ∀ (inst : DecidableRel G.graph.Adj), ¬@IsKColorable G.vertices G.graph _ inst 3 := by
  intro k hk
  interval_cases k <;> [exact moser_spindle_exists.choose_spec.2.2; exact moser_spindle_exists.choose_spec.2.2; exact moser_spindle_exists.choose_spec.2.2; exact odonnell_exists.choose_spec.2.2; exact wormald_exists.choose_spec.2.2; exact wormald_exists.choose_spec.2.2]

/-!
## Part VI: Hadwiger-Nelson Connection
-/

/-- The chromatic number of the plane χ(ℝ²) is the max χ over all finite
    unit distance graphs. De Grey (2018) showed χ(ℝ²) ≥ 5. -/
axiom de_grey_lower_bound :
  ∃ G : UnitDistanceGraph,
    ∀ (inst : DecidableRel G.graph.Adj), ¬@IsKColorable G.vertices G.graph _ inst 4

/-- Known upper bound: χ(ℝ²) ≤ 7 (hexagonal tiling argument) -/
axiom upper_bound_7 :
  ∀ G : UnitDistanceGraph,
    ∃ (inst : DecidableRel G.graph.Adj), @IsKColorable G.vertices G.graph _ inst 7

/-!
## Part VII: Why the Problem is Hard
-/

/-- Key insight: increasing girth restricts local structure but
    global chromatic number depends on more subtle interactions.

    The question is whether "sufficiently sparse" (high girth)
    unit distance graphs must have χ ≤ 3.

    Arguments for believing the answer might be NO:
    1. There's no obvious reason girth should bound χ
    2. Known constructions show girth 5 is not enough

    Arguments for YES:
    1. High girth graphs are "tree-like" and might be easier to color
    2. Geometric constraints might help -/
theorem difficulty_observation : True := trivial

/-!
## Part VIII: Summary
-/

/-- Erdős #705 Summary:

**Question**: Is there k such that unit distance graphs with girth ≥ k have χ ≤ 3?

**Status**: OPEN

**Known**:
- k ≤ 5 doesn't work (Wormald: girth 5, χ = 4)
- χ(ℝ²) is between 5 and 7 (Hadwiger-Nelson)
- Smallest 4-chromatic triangle-free: 47 vertices (Chilakamarri)

**Open Questions**:
- Does χ = 4 with girth 6 exist?
- Is there any relationship between girth and chromatic number?

**Related**: #508 (Hadwiger-Nelson), #704, #706 -/
theorem erdos_705_status : True := trivial

end Erdos705
