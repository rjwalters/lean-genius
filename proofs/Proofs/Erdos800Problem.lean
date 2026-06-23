/-
Erdős Problem #800: Linear Ramsey Numbers for Graphs Without Adjacent High-Degree Vertices

Source: https://erdosproblems.com/800
Status: SOLVED (Alon, 1994)

Statement:
If G is a graph on n vertices which has no two adjacent vertices of degree ≥ 3,
then R(G) ≪ n, where the implied constant is absolute.

Solution:
Noga Alon (1994) proved R(G) ≤ 12n for such graphs. This confirms a conjecture
of Burr and Erdős and shows that subdivided graphs have linear Ramsey numbers.

Background:
- R(G) = Ramsey number = minimum N such that any 2-coloring of edges of K_N
  contains a monochromatic copy of G
- A graph G has no adjacent high-degree vertices if whenever deg(u) ≥ 3 and
  deg(v) ≥ 3, we have u and v are not adjacent
- Subdivided graph = graph obtained by replacing each edge with a path
- The Burr-Erdős conjecture (now theorem, Lee 2016) generalizes this to
  all p-degenerate graphs

Significance:
This result is a special case of the broader Burr-Erdős conjecture (#163),
which states that p-degenerate graphs have linear Ramsey numbers. Alon's
proof technique uses probabilistic methods and careful counting arguments.

References:
- Alon (1994): "Subdivided graphs have linear Ramsey numbers", J. Graph Theory 18(4), 343-347
- Burr-Erdős (1975): Original conjecture
- Lee (2016): Full resolution of the Burr-Erdős conjecture (Problem #163)
- Related: Erdős Problem #163 (Burr-Erdős conjecture)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

namespace Erdos800

/- ## Part I: Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Degree of a Vertex:**
The degree of vertex v in graph G is the number of edges incident to v.
-/
def vertexDegree (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborFinset v).card

/--
**High-Degree Vertex:**
A vertex v has high degree (≥ 3) in graph G.
-/
def isHighDegree (G : SimpleGraph V) (v : V) : Prop :=
  vertexDegree G v ≥ 3

/--
**No Adjacent High-Degree Vertices:**
Graph G has no two adjacent vertices both of degree ≥ 3.
This is the key structural property in Erdős Problem #800.
-/
def noAdjacentHighDegree (G : SimpleGraph V) : Prop :=
  ∀ u v : V, G.Adj u v → ¬(isHighDegree G u ∧ isHighDegree G v)

/- ## Part II: Subdivisions
-/

/--
**Edge Subdivision:**
Subdividing an edge uv means replacing it with a path u-w-v where w is new.
A 1-subdivision replaces each edge with a path of length 2.
-/
def isSubdivisionVertex (G : SimpleGraph V) (v : V) : Prop :=
  vertexDegree G v = 2

/--
**Original Vertex:**
An original vertex is one from the base graph (before subdivision).
-/
def isOriginalVertex (G : SimpleGraph V) (v : V) : Prop :=
  vertexDegree G v ≠ 2

/--
**Subdivided Graph Property:**
A graph is a subdivision of some graph if and only if it has the property
that no two vertices of degree ≥ 3 are adjacent (all high-degree vertices
are separated by degree-2 "subdivision" vertices).
-/
theorem subdivision_implies_no_adjacent_high_degree (G : SimpleGraph V)
    (h : ∀ v : V, vertexDegree G v ≥ 3 → ∀ u : V, G.Adj v u → vertexDegree G u ≤ 2) :
    noAdjacentHighDegree G := by
  intro u v huv ⟨hu3, hv3⟩
  have : vertexDegree G v ≤ 2 := h u (hu3) v huv
  omega

/- ## Part III: Ramsey Numbers
-/

/--
**Complete Graph on N Vertices:**
K_N is the graph where every pair of distinct vertices is adjacent.
-/
def completeGraph (N : ℕ) : SimpleGraph (Fin N) where
  Adj u v := u ≠ v
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

/--
**Edge 2-Coloring:**
An edge coloring of K_N with 2 colors (red/blue).
-/
def edgeColoring (N : ℕ) : Type := (Fin N) → (Fin N) → Bool

/--
**Monochromatic Copy:**
A subgraph is monochromatic under a coloring if all its edges have the same color.
-/
def isMonochromatic (N : ℕ) (c : edgeColoring N) (f : V → Fin N) (G : SimpleGraph V) : Prop :=
  (∀ u v : V, G.Adj u v → c (f u) (f v) = true) ∨
  (∀ u v : V, G.Adj u v → c (f u) (f v) = false)

/--
**Contains Monochromatic Copy:**
K_N contains a monochromatic copy of G under coloring c.
-/
def containsMonochromaticCopy (N : ℕ) (c : edgeColoring N) (G : SimpleGraph V) : Prop :=
  ∃ f : V → Fin N, Function.Injective f ∧ isMonochromatic N c f G

/--
**Ramsey Number (axiomatized):**
R(G) is the minimum N such that every 2-coloring of K_N contains
a monochromatic copy of G. Axiomatized since formalizing the existence
via the finite Ramsey theorem requires substantial infrastructure.
-/
axiom ramseyNumber (G : SimpleGraph V) : ℕ

/--
**Ramsey property:**
For any 2-coloring of K_{R(G)}, there exists a monochromatic copy of G.
-/
axiom ramseyNumber_spec (G : SimpleGraph V) :
    ∀ (c : edgeColoring (ramseyNumber G)),
      containsMonochromaticCopy (ramseyNumber G) c G

/--
**Linear Ramsey Number:**
A graph G has linear Ramsey number if R(G) = O(n) where n = |V(G)|.
-/
def hasLinearRamseyNumber (G : SimpleGraph V) (C : ℝ) : Prop :=
  (ramseyNumber G : ℝ) ≤ C * (Fintype.card V : ℝ)

/- ## Part IV: The Main Theorem
-/

/--
**Alon's Theorem (1994):**
If G is a graph on n vertices with no two adjacent vertices of degree ≥ 3,
then R(G) ≤ 12n.

This settles Erdős Problem #800 and shows that subdivided graphs have
linear Ramsey numbers with an explicit constant of 12.
-/
axiom alon_theorem (G : SimpleGraph V) (h : noAdjacentHighDegree G) :
    (ramseyNumber G : ℝ) ≤ 12 * (Fintype.card V : ℝ)

/--
**Corollary: Subdivided Graphs Have Linear Ramsey Numbers:**
Any graph obtained by subdividing each edge at least once has R(G) ≤ 12n.
-/
theorem subdivided_graphs_linear_ramsey (G : SimpleGraph V)
    (h : ∀ v : V, vertexDegree G v ≥ 3 → ∀ u : V, G.Adj v u → vertexDegree G u ≤ 2) :
    hasLinearRamseyNumber G 12 := by
  unfold hasLinearRamseyNumber
  exact alon_theorem G (subdivision_implies_no_adjacent_high_degree G h)

/- ## Part V: Degeneracy and the Burr-Erdős Conjecture
-/

/--
**Graph Degeneracy:**
A graph G is p-degenerate if every subgraph has a vertex of degree ≤ p.
-/
def isDegenerateAt (G : SimpleGraph V) (p : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    ∃ v ∈ S, (G.neighborFinset v ∩ S).card ≤ p

/--
**Key Observation:**
Graphs with no adjacent high-degree vertices are 2-degenerate.
Axiomatized since the proof requires careful induction on subgraph structure.
-/
axiom no_adjacent_high_degree_is_2_degenerate (G : SimpleGraph V)
    (h : noAdjacentHighDegree G) : isDegenerateAt G 2

/--
**Burr-Erdős Conjecture (Problem #163, now theorem):**
For every p ≥ 1, there exists c_p such that every p-degenerate n-vertex graph
has Ramsey number at most c_p · n.

Proved by Choongbum Lee (2016).
-/
axiom burr_erdos_theorem (p : ℕ) (hp : p ≥ 1) :
    ∃ c : ℝ, c > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      isDegenerateAt G p →
        (ramseyNumber G : ℝ) ≤ c * (Fintype.card V : ℝ)

/--
**Problem #800 as Special Case of #163:**
Erdős Problem #800 is a special case: graphs with no adjacent high-degree
vertices are 2-degenerate, so the Burr-Erdős theorem applies.
-/
theorem erdos_800_special_case_of_163 (G : SimpleGraph V)
    (h : noAdjacentHighDegree G) :
    ∃ C : ℝ, hasLinearRamseyNumber G C := by
  obtain ⟨c, hc_pos, hc_bound⟩ := burr_erdos_theorem 2 (by norm_num)
  use c
  unfold hasLinearRamseyNumber
  exact hc_bound V G (no_adjacent_high_degree_is_2_degenerate G h)

/- ## Part VI: Summary
-/

/--
**Erdős Problem #800: Statement**
If G is a graph on n vertices which has no two adjacent vertices of
degree ≥ 3, then R(G) ≪ n.
-/
def erdos800Problem : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    noAdjacentHighDegree G →
      ∃ C : ℝ, hasLinearRamseyNumber G C

/--
**Erdős Problem #800: Solution**
Proved by Noga Alon in 1994 with explicit bound R(G) ≤ 12n.
-/
theorem erdos_800 : erdos800Problem := by
  intro V _ _ G h
  use 12
  unfold hasLinearRamseyNumber
  exact alon_theorem G h

/--
**Erdős Problem #800: Summary**

Alon (1994) proved R(G) ≤ 12n for graphs with no adjacent high-degree vertices.
This includes all subdivided graphs. The result is a special case of the
Burr-Erdős conjecture (Problem #163), fully resolved by Lee (2016).
-/
theorem erdos_800_summary :
    -- Alon's explicit bound
    (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      noAdjacentHighDegree G → (ramseyNumber G : ℝ) ≤ 12 * (Fintype.card V : ℝ)) ∧
    -- General existence of linear bound
    erdos800Problem :=
  ⟨fun V _ _ G h => alon_theorem G h, erdos_800⟩

end Erdos800
