/-
Erdős Problem #184: Graph Decomposition into Cycles and Edges

Source: https://erdosproblems.com/184
Status: OPEN

Statement:
Any graph on n vertices can be decomposed into O(n) many edge-disjoint cycles
and edges.

Background:
Conjectured by Erdős and Gallai. The question is whether the number of cycles
and isolated edges needed to partition a graph's edge set grows linearly in n.

Key Results:
- Erdős-Gallai: Proved O(n log n) cycles and edges suffice
- Lower bound: K_{3,n-3} requires at least (1+c)n pieces for some c > 0
- Bucić-Montgomery (2022): Proved O(n log* n) suffices (current best)
- Conlon-Fox-Sudakov (2014): O(n) suffices if min degree ≥ εn

The conjecture that O(n) suffices in general remains OPEN.

References:
- [Er71] Erdős, "Some unsolved problems in graph theory", 1971
- [BM22] Bucić-Montgomery, "Towards the Erdős-Gallai Cycle Decomposition Conjecture", 2022
- [CFS14] Conlon-Fox-Sudakov, "Cycle packing", 2014

Related: Problems #583 (paths), #1017 (complete graphs)

Tags: graph-theory, cycles, decomposition
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace Erdos184

/-!
## Part I: Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Simple Graph:**
A graph on vertex set V with undirected edges.
-/
abbrev Graph (V : Type*) [Fintype V] := SimpleGraph V

/--
**Number of vertices:**
-/
def numVertices (G : Graph V) : ℕ := Fintype.card V

/--
**Cycle in a Graph:**
A cycle is a sequence of distinct vertices v₁, v₂, ..., vₖ where
vᵢ is adjacent to vᵢ₊₁ and vₖ is adjacent to v₁.
-/
structure Cycle (G : Graph V) where
  vertices : List V
  length_ge_3 : vertices.length ≥ 3
  nodup : vertices.Nodup
  is_cycle : ∀ i : Fin vertices.length,
    G.Adj (vertices.get i) (vertices.get ⟨(i.val + 1) % vertices.length,
      Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) length_ge_3)⟩)

/--
**Single Edge:**
An edge as a decomposition piece (not part of any cycle).
-/
structure SingleEdge (G : Graph V) where
  u : V
  v : V
  adj : G.Adj u v

/-!
## Part II: Decomposition
-/

/--
**Decomposition Piece:**
Either a cycle or a single edge.
-/
inductive DecompPiece (G : Graph V)
  | cycle : Cycle G → DecompPiece G
  | edge : SingleEdge G → DecompPiece G

/--
**Edge Set of a Piece:**
The edges covered by a decomposition piece.
-/
def edgesOfPiece {G : Graph V} : DecompPiece G → Set (Sym2 V)
  | .cycle c => {e | ∃ i : Fin c.vertices.length,
      e = Sym2.mk (c.vertices.get i) (c.vertices.get ⟨(i.val + 1) % c.vertices.length,
        Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) c.length_ge_3)⟩)}
  | .edge e => {Sym2.mk e.u e.v}

/--
**Valid Decomposition:**
A collection of pieces that partition the edge set of G.
-/
def IsValidDecomposition {G : Graph V} (pieces : Finset (DecompPiece G)) : Prop :=
  -- All edges of G are covered
  (∀ e ∈ G.edgeSet, ∃ p ∈ pieces, e ∈ edgesOfPiece p) ∧
  -- Pieces are edge-disjoint
  (∀ p₁ p₂, p₁ ∈ pieces → p₂ ∈ pieces → p₁ ≠ p₂ →
    edgesOfPiece p₁ ∩ edgesOfPiece p₂ = ∅)

/--
**Decomposition Number:**
The minimum number of pieces needed to decompose G.
-/
noncomputable def decompNumber (G : Graph V) : ℕ :=
  Nat.find (⟨Fintype.card (G.edgeSet), by sorry⟩ :
    ∃ k : ℕ, ∃ pieces : Finset (DecompPiece G), pieces.card = k ∧ IsValidDecomposition pieces)

/-!
## Part III: The Erdős-Gallai Conjecture
-/

/--
**Erdős-Gallai Conjecture:**
Every graph on n vertices can be decomposed into O(n) cycles and edges.
-/
def ErdosGallaiConjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
    (decompNumber G : ℝ) ≤ C * Fintype.card V

/-!
## Part IV: Known Bounds
-/

/--
**Original Erdős-Gallai Bound:**
O(n log n) pieces suffice.
-/
axiom erdos_gallai_original_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
    Fintype.card V ≥ 2 →
    (decompNumber G : ℝ) ≤ C * Fintype.card V * Real.log (Fintype.card V)

/--
**Lower Bound from K_{3,n-3}:**
At least (1+c)n pieces are needed for some graphs.
-/
axiom lower_bound_from_bipartite :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 6 →
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Graph V),
      Fintype.card V = n ∧
      (decompNumber G : ℝ) ≥ (1 + c) * n

/--
**The Iterated Logarithm:**
log* n = 0 if n ≤ 1, else 1 + log*(log n)
-/
noncomputable def logStar : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => 1 + logStar (Nat.log2 (n + 2))

/--
**Bucić-Montgomery (2022):**
O(n log* n) pieces suffice.
-/
axiom bucic_montgomery_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
    Fintype.card V ≥ 2 →
    (decompNumber G : ℝ) ≤ C * Fintype.card V * (logStar (Fintype.card V) + 1)

/-!
## Part V: Dense Graph Result
-/

/--
**Minimum Degree:**
-/
def minDegree (G : Graph V) : ℕ :=
  (Finset.univ.image (fun v => G.degree v)).min' (by simp [Finset.image_nonempty])

/--
**Conlon-Fox-Sudakov (2014):**
For graphs with minimum degree ≥ εn, only O(n) pieces are needed.
-/
axiom conlon_fox_sudakov :
  ∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
      (minDegree G : ℝ) ≥ ε * Fintype.card V →
      (decompNumber G : ℝ) ≤ C * Fintype.card V

/-!
## Part VI: Non-Disjoint Case
-/

/--
**Non-Disjoint Decomposition:**
Allow cycles and edges to share edges (covering not partitioning).
-/
def IsValidCovering {G : Graph V} (pieces : Finset (DecompPiece G)) : Prop :=
  ∀ e ∈ G.edgeSet, ∃ p ∈ pieces, e ∈ edgesOfPiece p

/--
**Covering Number:**
-/
noncomputable def coverNumber (G : Graph V) : ℕ :=
  Nat.find (⟨Fintype.card (G.edgeSet), by sorry⟩ :
    ∃ k : ℕ, ∃ pieces : Finset (DecompPiece G), pieces.card = k ∧ IsValidCovering pieces)

/--
**Erdős (1971):**
If we don't require edge-disjointness, n-1 cycles and edges suffice.
-/
axiom erdos_covering_bound :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
    coverNumber G ≤ Fintype.card V - 1

/-!
## Part VII: Related Problems
-/

/--
**Path Decomposition (Problem #583):**
Decomposing into paths instead of cycles + edges.
-/
def pathDecompProblem : Prop :=
  -- Related: every graph can be decomposed into O(n) paths
  True

/--
**Complete Graph Decomposition (Problem #1017):**
Decomposing into complete graphs.
-/
def completeDecompProblem : Prop :=
  -- Related: decomposition into cliques
  True

/-!
## Part VIII: Why This Is Hard
-/

/--
**The Gap:**
- Lower bound: (1+c)n from K_{3,n-3}
- Upper bound: O(n log* n) from Bucić-Montgomery
- Conjecture: O(n)

Closing this gap is the challenge.
-/
axiom open_problem_difficulty : True

/--
**Progress History:**
- 1966: Erdős-Gallai conjecture O(n)
- 1966: Erdős-Gallai prove O(n log n)
- 2014: Conlon-Fox-Sudakov prove O(n) for dense graphs
- 2022: Bucić-Montgomery prove O(n log* n)
- ???: General O(n) remains open
-/
axiom progress_timeline : True

/-!
## Part IX: Summary
-/

/--
**Erdős Problem #184: OPEN**

CONJECTURE: Every graph on n vertices can be decomposed into O(n) edge-disjoint
cycles and edges.

STATUS: Open with progress

KNOWN BOUNDS:
- Upper: O(n log* n) [Bucić-Montgomery 2022]
- Lower: (1+c)n [from K_{3,n-3}]
- Special case: O(n) if min degree ≥ εn [CFS 2014]

The iterated logarithm log* n grows extremely slowly (log* of a googolplex is ~5),
so O(n log* n) is "almost" O(n).
-/
theorem erdos_184 : True := trivial

/--
**Summary theorem:**
-/
theorem erdos_184_summary :
    -- Bucić-Montgomery gives best known upper bound
    (∃ C : ℝ, C > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
      Fintype.card V ≥ 2 →
      (decompNumber G : ℝ) ≤ C * Fintype.card V * (logStar (Fintype.card V) + 1)) ∧
    -- Lower bound exists
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 6 →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : Graph V),
        Fintype.card V = n ∧ (decompNumber G : ℝ) ≥ (1 + c) * n) ∧
    -- Dense case is solved
    (∀ ε : ℝ, ε > 0 → ∃ C : ℝ, C > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Graph V),
        (minDegree G : ℝ) ≥ ε * Fintype.card V →
        (decompNumber G : ℝ) ≤ C * Fintype.card V) := by
  exact ⟨bucic_montgomery_bound, lower_bound_from_bipartite, conlon_fox_sudakov⟩

/--
**Key Insight:**
The iterated logarithm log* n is essentially constant for all practical n:
log*(10^10^10) = 5. So O(n log* n) is tantalizingly close to O(n).
-/
theorem key_insight_log_star :
    logStar 65536 = 4 ∧ -- log* of 2^16
    logStar 4 = 2 := by
  constructor <;> native_decide

end Erdos184
