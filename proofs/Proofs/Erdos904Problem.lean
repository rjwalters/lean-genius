/-
Erdős Problem #904: Triangles with High Degree Sum

Source: https://erdosproblems.com/904
Status: SOLVED (Edwards, 1978)

Statement:
If G is a graph with n vertices and >n²/4 edges, then it contains a
triangle on vertices x, y, z such that
  d(x) + d(y) + d(z) ≥ (3/2)n.

History:
- Bollobás-Erdős: Conjectured this result
- Edwards (1978): Proved the conjecture

Context:
By Turán's theorem, >n²/4 edges guarantees a triangle exists.
This result strengthens that by showing we can find a triangle
where the three vertices have high combined degree.

The threshold n²/4 is sharp: the complete bipartite graph K_{n/2,n/2}
has exactly n²/4 edges and is triangle-free.

References:
- [Ed78] Edwards, C. S., "Complete subgraphs with largest sum of vertex degrees",
  Combinatorics (Proc. British Combinatorial Conf., 1977), 293-306, London Math.
  Soc. Lecture Note Ser. 26, Cambridge Univ. Press, 1978.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

namespace Erdos904

/-
## Part I: Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Degree of a Vertex:**
The number of edges incident to vertex v.
-/
def vertexDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  G.degree v

/--
**Edge Count:**
The number of edges in graph G.
-/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/--
**Triangle:**
Three vertices x, y, z form a triangle if all pairs are adjacent.
-/
def IsTriangle (G : SimpleGraph V) (x y z : V) : Prop :=
  x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ G.Adj x y ∧ G.Adj y z ∧ G.Adj x z

/--
**Degree Sum of a Triangle:**
The sum d(x) + d(y) + d(z) for vertices of a triangle.
-/
def triangleDegreeSum (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V) : ℕ :=
  G.degree x + G.degree y + G.degree z

/-
## Part II: Turán's Theorem Context
-/

/--
**Turán's Threshold:**
n²/4 edges (for even n, this is the Turán number T(n,2)).
-/
def turanThreshold (n : ℕ) : ℕ :=
  n * n / 4

/--
**Dense Graph:**
A graph with more than n²/4 edges.
-/
def IsDense (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeCount G > turanThreshold (Fintype.card V)

/--
**Turán's Theorem (Context):**
Any graph with >n²/4 edges must contain a triangle.
This is a special case of the general Turán theorem.
-/
/-
## Part III: The Bollobás-Erdős Conjecture
-/

/--
**High Degree Sum Triangle:**
A triangle where the sum of degrees is at least (3/2)n.
-/
def HasHighDegreeSum (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V) : Prop :=
  2 * triangleDegreeSum G x y z ≥ 3 * Fintype.card V

/--
**The Bollobás-Erdős Conjecture:**
Every dense graph contains a triangle with high degree sum.
-/
def BollobasErdosConjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsDense G → ∃ x y z : V, IsTriangle G x y z ∧ HasHighDegreeSum G x y z

/-
## Part IV: Edwards' Theorem (1978)
-/

/--
**Edwards' Theorem:**
The Bollobás-Erdős conjecture is true.

If G has n vertices and >n²/4 edges, then G contains a triangle
on vertices x, y, z with d(x) + d(y) + d(z) ≥ (3/2)n.
-/
axiom edwards_1978 : BollobasErdosConjecture

/--
**Main Result:**
Edwards proved that dense graphs contain high-degree-sum triangles.
-/
theorem erdos_904 : BollobasErdosConjecture := edwards_1978

/-
## Part V: Sharpness and Examples
-/

/-- **Complete Bipartite Sharpness:**
    The complete bipartite graph K_{n/2,n/2} has exactly ⌊n²/4⌋ edges
    and is triangle-free, showing the Turán threshold is tight. -/
/-- **Turán Graph Extremality:**
    The Turán graph T(n,2) maximizes edges among triangle-free graphs.
    No triangle-free graph on n vertices has more than ⌊n²/4⌋ edges. -/
/-
## Part VI: Stronger Results
-/

/-- **Degree Sum Tightness:**
    The constant 3/2 is best possible: for every ε > 0 and sufficiently
    large n, there exists a dense graph where every triangle has degree
    sum < (3/2 + ε)n. -/
/-- **Supersaturation:**
    Graphs with more than ⌊n²/4⌋ edges contain not just one triangle but
    at least Ω(n) triangles. Density above the Turán threshold forces many
    triangles. -/
/-
## Part VII: Summary
-/

/-- **The Main Theorem:**
    Dense graphs contain high-degree-sum triangles. -/
theorem erdos_904_main (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : IsDense G) :
    ∃ x y z : V, IsTriangle G x y z ∧ HasHighDegreeSum G x y z :=
  edwards_1978 V G h

end Erdos904
