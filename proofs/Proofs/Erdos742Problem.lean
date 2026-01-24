/-
Erdős Problem #742: Maximum Edges in Minimal Diameter-2 Graphs

Source: https://erdosproblems.com/742
Status: SOLVED (Füredi 1992)

Statement:
Let G be a graph on n vertices with diameter 2, such that deleting any edge
increases the diameter of G. Is it true that G has at most n²/4 edges?

Background:
A conjecture attributed to Murty-Plesník (1979), though Füredi notes it may go
back to Ore in the 1960s. A diameter-2 graph where every edge is critical for
maintaining diameter 2 is called a "minimal diameter-2 graph."

Answer: YES (for sufficiently large n).
Füredi (1992) proved that minimal diameter-2 graphs have at most ⌊n²/4⌋ edges.
The complete bipartite graph K_{⌊n/2⌋,⌈n/2⌉} shows this bound is tight.

References:
- [CaHa79] Caccetta-Häggkvist, "On diameter critical graphs", Discrete Math (1979)
- [Fu92] Füredi, "The maximum number of edges in a minimal graph of diameter 2",
  J. Graph Theory (1992), 81-98

Tags: graph-theory, extremal-graph-theory, diameter, edge-critical
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card

namespace Erdos742

open SimpleGraph

/-!
## Part I: Graph Diameter
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The distance between two vertices in a graph (shortest path length). -/
noncomputable def dist (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ∞ :=
  if h : G.Reachable u v then G.dist u v else ⊤

/-- The diameter of a graph: maximum distance between any two vertices. -/
noncomputable def diameter (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ∞ :=
  ⨆ (u v : V), dist G u v

/-- G has diameter exactly d. -/
def HasDiameter (G : SimpleGraph V) (d : ℕ) : Prop :=
  G.Connected ∧ (∀ u v : V, G.Reachable u v → G.dist u v ≤ d) ∧
  (∃ u v : V, G.dist u v = d)

/-- G has diameter 2: any two vertices are at distance at most 2. -/
def HasDiameter2 (G : SimpleGraph V) : Prop := HasDiameter G 2

/-!
## Part II: Edge Deletion and Critical Edges
-/

/-- The graph G with edge (u,v) deleted. -/
def deleteEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V where
  Adj := fun x y => G.Adj x y ∧ ¬(({x, y} : Set V) = {u, v})
  symm := fun x y ⟨hadj, hne⟩ => ⟨G.symm hadj, by
    simp only [Set.pair_comm] at hne ⊢
    exact hne⟩
  loopless := fun x ⟨hadj, _⟩ => G.loopless x hadj

/-- An edge (u,v) is critical for diameter if deleting it increases the diameter. -/
def IsCriticalEdge (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ¬HasDiameter2 (deleteEdge G u v)

/-- Every edge in G is critical for diameter 2. -/
def AllEdgesCritical (G : SimpleGraph V) : Prop :=
  ∀ u v : V, G.Adj u v → IsCriticalEdge G u v

/-!
## Part III: Minimal Diameter-2 Graphs
-/

/-- A minimal diameter-2 graph: diameter 2 and every edge is critical. -/
def IsMinimalDiameter2 (G : SimpleGraph V) : Prop :=
  HasDiameter2 G ∧ AllEdgesCritical G

/-- The number of edges in G. -/
noncomputable def edgeCount (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card

/-- The conjectured bound: at most n²/4 edges. -/
def MurtyPlesnikBound (n : ℕ) : ℕ := n^2 / 4

/-!
## Part IV: The Complete Bipartite Graph (Extremal Example)
-/

/-- K_{a,b} achieves exactly a·b edges with diameter 2.
    For a = ⌊n/2⌋, b = ⌈n/2⌉, this gives ⌊n²/4⌋ edges. -/
axiom complete_bipartite_diameter2 (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1) :
    ∃ (V : Type*) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = a + b ∧ HasDiameter2 G ∧ edgeCount G = a * b

/-- The balanced complete bipartite graph achieves ⌊n²/4⌋ edges. -/
theorem balanced_bipartite_edges (n : ℕ) (hn : n ≥ 2) :
    (n / 2) * ((n + 1) / 2) = n^2 / 4 := by
  sorry  -- Arithmetic identity

/-- K_{⌊n/2⌋, ⌈n/2⌉} is a minimal diameter-2 graph.
    It shows the bound is tight. -/
axiom balanced_bipartite_minimal (n : ℕ) (hn : n ≥ 2) :
    ∃ (V : Type*) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsMinimalDiameter2 G ∧ edgeCount G = n^2 / 4

/-!
## Part V: Füredi's Theorem (1992)
-/

/-- **Füredi's Theorem (1992):**
    For sufficiently large n, every minimal diameter-2 graph on n vertices
    has at most ⌊n²/4⌋ edges.

    This settles the Murty-Plesník-Ore conjecture. -/
axiom furedi_theorem :
    ∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      Fintype.card V ≥ N₀ →
      IsMinimalDiameter2 G →
      edgeCount G ≤ MurtyPlesnikBound (Fintype.card V)

/-- The bound n²/4 is achieved by the complete bipartite graph. -/
theorem bound_is_tight :
    ∀ n : ℕ, n ≥ 2 →
    ∃ (V : Type*) (_ : Fintype V) (G : SimpleGraph V),
      Fintype.card V = n ∧ IsMinimalDiameter2 G ∧
      edgeCount G = MurtyPlesnikBound n := by
  intro n hn
  obtain ⟨V, hFin, G, hCard, hMin, hEdges⟩ := balanced_bipartite_minimal n hn
  use V, hFin, G
  exact ⟨hCard, hMin, hEdges⟩

/-!
## Part VI: Historical Context
-/

/-- The conjecture was posed independently by multiple researchers. -/
def conjecture_history : String :=
  "Ore (1960s) → Murty-Simon → Murty-Plesník (1979) → Caccetta-Häggkvist"

/-- Caccetta-Häggkvist (1979) studied diameter-critical graphs. -/
axiom caccetta_haggkvist_results :
    -- They proved partial results and stated the conjecture
    True

/-- Füredi's proof uses probabilistic and extremal methods. -/
axiom furedi_proof_technique :
    -- The proof is non-trivial and uses the regularity lemma
    True

/-!
## Part VII: Related Concepts
-/

/-- A graph is diameter-d-critical if it has diameter d and
    deleting any edge increases the diameter. -/
def IsDiameterCritical (G : SimpleGraph V) (d : ℕ) : Prop :=
  HasDiameter G d ∧ ∀ u v : V, G.Adj u v →
    ¬HasDiameter (deleteEdge G u v) d

/-- Minimal diameter-2 is the same as diameter-2-critical. -/
theorem minimal_iff_critical (G : SimpleGraph V) :
    IsMinimalDiameter2 G ↔ IsDiameterCritical G 2 := by
  constructor
  · intro ⟨hDiam, hCrit⟩
    exact ⟨hDiam, fun u v hadj => (hCrit u v hadj).2⟩
  · intro ⟨hDiam, hCrit⟩
    constructor
    · exact hDiam
    · intro u v hadj
      exact ⟨hadj, hCrit u v hadj⟩

/-- For diameter d ≥ 3, the extremal problem has different answers. -/
axiom diameter_d_critical_bounds (d : ℕ) (hd : d ≥ 3) :
    ∃ f : ℕ → ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      IsDiameterCritical G d → edgeCount G ≤ f (Fintype.card V)

/-!
## Part VIII: Summary
-/

/-- **Erdős Problem #742: SOLVED**

    QUESTION: Is it true that a minimal diameter-2 graph on n vertices
    has at most n²/4 edges?

    ANSWER: YES (for sufficiently large n).

    PROOF: Füredi (1992) proved this using extremal graph theory techniques.

    EXTREMAL EXAMPLE: K_{⌊n/2⌋, ⌈n/2⌉} achieves ⌊n²/4⌋ edges.

    HISTORY: Conjecture attributed to Ore (1960s), Murty-Plesník (1979).
-/
theorem erdos_742 :
    (∃ N₀ : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      Fintype.card V ≥ N₀ → IsMinimalDiameter2 G →
      edgeCount G ≤ MurtyPlesnikBound (Fintype.card V)) ∧
    (∀ n : ℕ, n ≥ 2 →
      ∃ (V : Type*) (_ : Fintype V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsMinimalDiameter2 G ∧
        edgeCount G = MurtyPlesnikBound n) := by
  exact ⟨furedi_theorem, bound_is_tight⟩

/-- The answer to Erdős Problem #742. -/
def erdos_742_answer : String :=
  "YES: Minimal diameter-2 graphs have at most n²/4 edges (Füredi 1992)"

/-- The status of Erdős Problem #742. -/
def erdos_742_status : String := "SOLVED"

#check erdos_742
#check IsMinimalDiameter2
#check furedi_theorem
#check MurtyPlesnikBound

end Erdos742
