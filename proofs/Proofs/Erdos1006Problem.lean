/-
  Erdős Problem #1006: Robust Acyclic Orientations

  Source: https://erdosproblems.com/1006
  Status: DISPROVED (Nešetřil-Rödl 1978)

  Statement:
  Let G be a graph with girth > 4 (no triangles or 4-cycles). Can the edges
  of G always be directed such that:
  (1) There is no directed cycle, AND
  (2) Reversing the direction of any single edge also creates no directed cycle?

  Such an orientation would be "robustly acyclic" - acyclic even after any
  single edge reversal.

  Background:
  This problem, credited to Ore by Erdős, asks whether high-girth graphs
  admit particularly stable acyclic orientations. The motivation comes from
  the observation that acyclic orientations always exist (they correspond to
  linear orderings of vertices), but some are "fragile" - reversing one edge
  creates a cycle.

  Counterexamples at girth 4:
  • Ore gave an example of a girth-4 graph without this property
  • Gallai noted the Grötzsch graph (girth 4, chromatic number 4, triangle-free)
    also lacks this property

  Resolution:
  FALSE for all girths. Nešetřil and Rödl (1978) proved using probabilistic
  methods that for every integer g ≥ 3, there exists a graph G with girth g
  such that NO orientation of G is robustly acyclic.

  Their proof uses the probabilistic method: random graphs with high girth
  and high chromatic number have the property that every acyclic orientation
  has an edge whose reversal creates a directed cycle.

  References:
  [Er71] Erdős, P. "Some unsolved problems in graph theory" (1971)
  [NeRo78b] Nešetřil, J. and Rödl, V. Proc. Amer. Math. Soc. (1978)

  Tags: graph-theory, orientation, girth, cycles, counterexample
-/

import Mathlib

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Graph Girth

The girth of a graph is the length of its shortest cycle.
-/

/-- A graph has girth at least g if it contains no cycles of length < g -/
def hasGirthAtLeast (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (cycle : List V), cycle.length < g → ¬G.IsCycle cycle

/-- A graph has girth exactly g if g is the length of its shortest cycle -/
def hasGirth (G : SimpleGraph V) (g : ℕ) : Prop :=
  hasGirthAtLeast G g ∧ ∃ (cycle : List V), cycle.length = g ∧ G.IsCycle cycle

/-
## Directed Graphs and Orientations

An orientation assigns a direction to each edge.
-/

/-- An orientation of an undirected graph G is a directed graph D where
    for each edge {u,v} in G, exactly one of (u,v) or (v,u) is in D -/
structure Orientation (G : SimpleGraph V) where
  directed : V → V → Prop
  covers : ∀ u v, G.Adj u v → (directed u v ∨ directed v u)
  exclusive : ∀ u v, ¬(directed u v ∧ directed v u)
  respects : ∀ u v, directed u v → G.Adj u v

/-- A directed path in an orientation -/
def Orientation.hasDirectedPath (O : Orientation G) (path : List V) : Prop :=
  path.length ≥ 2 ∧ ∀ i, i + 1 < path.length → O.directed (path.get ⟨i, by omega⟩) (path.get ⟨i+1, by omega⟩)

/-- An orientation is acyclic if it has no directed cycles -/
def Orientation.isAcyclic (O : Orientation G) : Prop :=
  ∀ (cycle : List V), cycle.length ≥ 3 → cycle.head? = cycle.getLast? → ¬O.hasDirectedPath cycle

/-
## Robust Acyclicity

The key property: an orientation where reversing any single edge preserves acyclicity.
-/

/-- Reverse a single edge in an orientation -/
def Orientation.reverseEdge (O : Orientation G) (u v : V) : Orientation G where
  directed := fun x y =>
    if x = u ∧ y = v then O.directed v u
    else if x = v ∧ y = u then O.directed u v
    else O.directed x y
  covers := by intro x y hadj; sorry
  exclusive := by intro x y; sorry
  respects := by intro x y hdir; sorry

/-- An orientation is robustly acyclic if it remains acyclic after any single edge reversal -/
def Orientation.isRobustlyAcyclic (O : Orientation G) : Prop :=
  O.isAcyclic ∧ ∀ u v, O.directed u v → (O.reverseEdge u v).isAcyclic

/-- A graph admits a robustly acyclic orientation -/
def admitsRobustlyAcyclicOrientation (G : SimpleGraph V) : Prop :=
  ∃ (O : Orientation G), O.isRobustlyAcyclic

/-
## The Conjecture (Disproved)

Ore's question: Do all high-girth graphs admit robustly acyclic orientations?
-/

/-- Ore's conjecture (FALSE): graphs with girth > 4 admit robust orientations -/
def oresConjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    hasGirthAtLeast G 5 → admitsRobustlyAcyclicOrientation G

/-
## Counterexamples
-/

/-- The Grötzsch graph has girth 4 and no robustly acyclic orientation -/
axiom grotzsch_counterexample :
  ∃ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    hasGirth G 4 ∧ ¬admitsRobustlyAcyclicOrientation G

/-- Nešetřil-Rödl theorem: For every g ≥ 3, there exists a graph with girth g
    that has no robustly acyclic orientation -/
axiom nesetril_rodl_1978 (g : ℕ) (hg : g ≥ 3) :
  ∃ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    hasGirth G g ∧ ¬admitsRobustlyAcyclicOrientation G

/-- Corollary: Ore's conjecture is false -/
theorem ores_conjecture_false : ¬oresConjecture := by
  intro hconj
  -- Take g = 5, get a counterexample from Nešetřil-Rödl
  have ⟨V, _, _, G, _, hgirth, hno⟩ := nesetril_rodl_1978 5 (by norm_num)
  -- The conjecture would imply G has a robust orientation
  have hhas := hconj V G hgirth.1
  -- Contradiction
  exact hno hhas

#check ores_conjecture_false
#check @nesetril_rodl_1978
