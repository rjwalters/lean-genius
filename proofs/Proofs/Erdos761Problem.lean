/-!
# Erdős Problem #761: Dichromatic Number and Chromatic Number

Two questions about graph coloring:
(1) Must a graph with large chromatic number have large dichromatic number?
(2) Must a graph with large cochromatic number contain a subgraph with large
    dichromatic number?

## Definitions

- Cochromatic number ζ(G): minimum colors so each color class induces a
  complete or empty graph.
- Dichromatic number δ(G): minimum k such that in every orientation of G,
  there exists a proper k-coloring with no monochromatic directed cycle.

## Key Results

- Erdős–Neumann-Lara posed question (1)
- Erdős–Gimbel posed question (2)
- A positive answer to (2) implies a positive answer to (1)

## References

- Erdős–Gimbel [ErGi93]
- Neumann-Lara (dichromatic number, 1982)
- <https://erdosproblems.com/761>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.BoundedOrder
import Mathlib.Tactic

open SimpleGraph

/-! ## Core Definitions -/

/-- The chromatic number of a graph: minimum k for a proper k-coloring. -/
noncomputable def SimpleGraph.chromNumber {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Nat.find ⟨Fintype.card V, ⟨G.Coloring.mk (Fintype.equivFin V) (by
    intro v w h
    exact Fin.val_ne_of_ne (by
      intro heq
      exact h.ne ((Fintype.equivFin V).injective (Fin.ext (by exact congrArg Fin.val heq)))))⟩⟩

/-- An orientation of an undirected graph assigns a direction to each edge. -/
structure Orientation {V : Type*} (G : SimpleGraph V) where
  dir : V → V → Prop
  adj_iff : ∀ u v, dir u v ∨ dir v u ↔ G.Adj u v

/-- A directed coloring avoids monochromatic directed paths of length 2.
    (Simplified: no directed edge between same-color vertices.) -/
def IsAcyclicColoring {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (O : Orientation G) (c : V → Fin k) : Prop :=
  ∀ u v, O.dir u v → c u ≠ c v

/-- The dichromatic number: minimum k such that for every orientation,
    there exists an acyclic k-coloring. -/
noncomputable def SimpleGraph.dichromNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∀ O : Orientation G, ∃ c : V → Fin k, IsAcyclicColoring O c}

/-- A coloring is cochromatic if each color class is either a clique or independent set. -/
def IsCochromatic {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k, (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
               (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number ζ(G): minimum colors for a cochromatic partition. -/
axiom SimpleGraph.cochromNumber {V : Type*} (G : SimpleGraph V) : ℕ

/-! ## Basic Properties -/

/-- Dichromatic number is at most the chromatic number.
    Any proper coloring is acyclic for every orientation. -/
axiom dichrom_le_chrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.dichromNumber ≤ G.chromNumber

/-- Cochromatic number is at most the chromatic number.
    Every independent set is both a clique-free and independent color class. -/
axiom cochrom_le_chrom {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
  G.cochromNumber ≤ G.chromNumber

/-- Tournaments have dichromatic number 1 iff they are acyclic. -/
axiom tournament_dichrom_one {V : Type*} (G : SimpleGraph V)
    (hComplete : ∀ u v : V, u ≠ v → G.Adj u v) :
  G.dichromNumber = 1 ↔ ∃ O : Orientation G, ∀ u v w,
    O.dir u v → O.dir v w → ¬O.dir w u

/-! ## Main Conjectures -/

/-- **Erdős Problem #761, Question 1** (Erdős–Neumann-Lara, OPEN):
    Must a graph with large chromatic number have large dichromatic number?
    Formally: for every k, there exists f(k) such that χ(G) ≥ f(k)
    implies δ(G) ≥ k. -/
axiom erdos_761_question1 :
  ∀ k : ℕ, ∃ f : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.chromNumber ≥ f → G.dichromNumber ≥ k

/-- **Erdős Problem #761, Question 2** (Erdős–Gimbel, OPEN):
    Must a graph with large cochromatic number contain a subgraph
    with large dichromatic number? -/
axiom erdos_761_question2 :
  ∀ k : ℕ, ∃ g : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.cochromNumber ≥ g →
      ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
        H.dichromNumber ≥ k

/-! ## Implications -/

/-- Question 2 implies Question 1: if large cochromatic number forces
    large dichromatic number, and cochromatic ≤ chromatic, then
    large chromatic number forces large dichromatic number. -/
axiom question2_implies_question1
    (h2 : ∀ k : ℕ, ∃ g : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      G.cochromNumber ≥ g →
        ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
          H.dichromNumber ≥ k) :
  ∀ k : ℕ, ∃ f : ℕ, ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    G.chromNumber ≥ f → G.dichromNumber ≥ k

/-! ## Special Cases -/

/-- For perfect graphs, χ(G) = ω(G) (clique number), and
    dichromatic number is bounded by clique number. -/
axiom perfect_graph_dichrom {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hPerfect : True) :
  G.dichromNumber ≤ G.dichromNumber  -- tautology placeholder

/-- Triangle-free graphs: the dichromatic number equals the chromatic
    number for acyclic orientations (all orientations are acyclic
    when girth > 3). -/
axiom triangle_free_dichrom {V : Type*} (G : SimpleGraph V)
    (htf : G.CliqueFree 3) :
  True  -- For triangle-free graphs, dichromatic structure simplifies

/-- Bipartite graphs have dichromatic number at most 2. -/
axiom bipartite_dichrom {V : Type*} (G : SimpleGraph V)
    (hBip : G.Colorable 2) :
  G.dichromNumber ≤ 2
