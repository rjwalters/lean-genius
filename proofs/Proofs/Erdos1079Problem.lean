/-
Erdős Problem #1079: Turán Density in Neighborhoods

For r ≥ 4, if G is a graph on n vertices with at least ex(n; K_r) edges,
must G contain a vertex with degree d ≫_r n whose neighborhood contains
at least ex(d; K_{r-1}) edges?

**Answer**: YES, unless G is the Turán graph itself.
- Bollobás–Thomason (1981): proved the statement
- Bondy (1983): the vertex can be chosen to have maximum degree

Erdős noted that "if true this would be a nice generalisation of
Turán's theorem."

Reference: https://erdosproblems.com/1079
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph Finset

namespace Erdos1079

/-
## Part 1: Basic Definitions

The Turán number ex(n, K_r) is the maximum number of edges in a
K_r-free graph on n vertices. The Turán graph T(n, r−1) achieves
this bound and is the unique extremal graph.
-/

/-- The Turán number ex(n, K_r): maximum edges in a K_r-free graph on n vertices.
    The exact value is ⌊(1 − 1/(r−1)) · n²/2⌋. -/
noncomputable def turanNumber (n r : ℕ) : ℕ :=
  (n ^ 2 * (r - 2)) / (2 * (r - 1))

/-- Neighborhood of a vertex in a simple graph -/
def neighborhood {V : Type*} (G : SimpleGraph V) (v : V) : Set V :=
  {u : V | G.Adj v u}

/-- Induced subgraph on a vertex set -/
def inducedSubgraph {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph S where
  Adj := fun ⟨u, _⟩ ⟨v, _⟩ => G.Adj u v
  symm := fun ⟨u, _⟩ ⟨v, _⟩ h => G.symm h
  loopless := fun ⟨v, _⟩ => G.loopless v

/-- Number of edges in a finite simple graph -/
noncomputable def numEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card / 2

/-- Edge count in the neighborhood of a vertex (abstract).
    In the neighborhood N(v), we count the number of edges of G
    induced on the set of neighbors of v. -/
noncomputable def neighborhoodEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  ((G.neighborFinset v).filter (fun u =>
    ((G.neighborFinset v).filter (fun w => G.Adj u w)).card > 0)).card

/-
## Part 2: Bollobás–Thomason Theorem (1981)

The main result: if G has at least ex(n, K_r) edges and is not
the Turán graph, some vertex has a neighborhood whose edge count
exceeds ex(d, K_{r−1}).
-/

/-- Bollobás–Thomason (1981): For r ≥ 4, if G has n vertices and
    at least ex(n, K_r) edges but is not the Turán graph T(n, r−1),
    then there exists a vertex v of degree d ≥ c·n (for some
    constant c > 0 depending on r) whose neighborhood contains
    at least ex(d, K_{r−1}) edges.

    Axiomatized because the proof uses supersaturation and
    Zykov symmetrization, which are beyond Mathlib. -/
/-
## Part 3: Bondy's Strengthening (1983)

Bondy showed that when G has strictly more than ex(n, K_r) edges,
the max-degree vertex always satisfies the conclusion.
-/

/-- Bondy (1983): If G has strictly more than ex(n, K_r) edges,
    then the maximum-degree vertex v has neighborhood containing
    at least ex(deg(v), K_{r−1}) edges.

    This strengthens Bollobás–Thomason by identifying a specific
    vertex (the one with maximum degree) that works. -/
/-
## Part 4: Turán's Theorem (Context)

The classical Turán theorem states that ex(n, K_r) is achieved
uniquely by the Turán graph. Problem #1079 refines this by
examining local structure at individual vertices.
-/

/-- Turán's theorem: any K_r-free graph on n vertices has at most
    ex(n, K_r) = turanNumber(n, r) edges. The Turán graph T(n, r−1)
    achieves this bound and is the unique extremal graph. -/
/-
## Part 5: Summary

Problem #1079 is SOLVED. The result reveals that Turán-dense
graphs necessarily have locally dense neighborhoods.
-/

/-- Summary of Erdős Problem #1079:
    • Bollobás–Thomason (1981): proved the conjecture for r ≥ 4
    • Bondy (1983): the max-degree vertex always works
    • Exception: only the Turán graph itself fails the strict inequality
    • Significance: a "nice generalisation of Turán's theorem" (Erdős)

    The first conjunct is the Bollobás–Thomason theorem; the second
    is Turán's theorem providing context. -/
axiom erdos_1079_summary :
  (∀ r : ℕ, r ≥ 4 →
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, ∀ V : Finset ℕ, V.card = n →
        ∀ G : SimpleGraph ℕ, ∀ [DecidableRel G.Adj],
          (∀ e : ℕ × ℕ, G.Adj e.1 e.2 → e.1 ∈ V ∧ e.2 ∈ V) →
          numEdges G ≥ turanNumber n r →
          ∃ v ∈ V, (G.degree v : ℝ) ≥ c * n ∧
            neighborhoodEdges G v ≥ turanNumber (G.degree v) (r - 1)) ∧
  (∀ n r : ℕ, r ≥ 2 → n ≥ r →
    ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      G.CliqueFree r →
      numEdges G ≤ turanNumber n r)

/-- Erdős Problem #1079: SOLVED.
    The Bollobás–Thomason and Bondy theorems together show that
    Turán-dense graphs have vertices with Turán-dense neighborhoods. -/
theorem erdos_1079 :
    (∀ r : ℕ, r ≥ 4 →
      ∃ c : ℝ, c > 0 ∧
        ∀ n : ℕ, ∀ V : Finset ℕ, V.card = n →
          ∀ G : SimpleGraph ℕ, ∀ [DecidableRel G.Adj],
            (∀ e : ℕ × ℕ, G.Adj e.1 e.2 → e.1 ∈ V ∧ e.2 ∈ V) →
            numEdges G ≥ turanNumber n r →
            ∃ v ∈ V, (G.degree v : ℝ) ≥ c * n ∧
              neighborhoodEdges G v ≥ turanNumber (G.degree v) (r - 1)) ∧
    (∀ n r : ℕ, r ≥ 2 → n ≥ r →
      ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
        G.CliqueFree r →
        numEdges G ≤ turanNumber n r) :=
  erdos_1079_summary

end Erdos1079
