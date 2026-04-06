/-
Erdős Problem #926: Turán Number of the Graph H_k

Source: https://erdosproblems.com/926
Status: SOLVED (Füredi 1991, Alon-Krivelevich-Sudakov 2003)

Statement:
Let k ≥ 4. Is it true that ex(n; H_k) ≪_k n^(3/2), where H_k is the graph on
vertices x, y_1, ..., y_k, z_1, ..., z_(k choose 2), where x is adjacent to all
y_i and each pair y_i, y_j is adjacent to a unique z_i?

Answer: YES

Füredi (1991) proved: ex(n; H_k) ≪ (kn)^(3/2)
Alon-Krivelevich-Sudakov (2003) improved to: ex(n; H_k) ≪ k·n^(3/2)

The lower bound ex(n; H_k) ≫ n^(3/2) is trivial since H_k contains C_4.

References:
- Füredi, "On a Turán type problem of Erdős", Combinatorica (1991), 75-79
- Alon, Krivelevich, Sudakov, "Turán numbers of bipartite graphs and related
  Ramsey-type questions", Combin. Probab. Comput. (2003), 477-494
- Erdős, "Some unsolved problems in graph theory and combinatorial analysis",
  Combinatorial Mathematics and its Applications (1971), 97-109
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card

open Finset SimpleGraph

namespace Erdos926

/-
## Part I: The Graph H_k

The forbidden subgraph has a specific structure:
- One central vertex x
- k vertices y_1, ..., y_k all adjacent to x
- (k choose 2) vertices z_ij, each adjacent to exactly one pair y_i, y_j
-/

/--
**Vertices of H_k:**
- One vertex x (represented as 0)
- k vertices y_i (represented as 1 to k)
- (k choose 2) vertices z_ij (represented as k+1 to k + (k choose 2))
-/
def hkVertexCount (k : ℕ) : ℕ := 1 + k + Nat.choose k 2

/--
Example: H_4 has 1 + 4 + 6 = 11 vertices.
-/
theorem h4_vertex_count : hkVertexCount 4 = 11 := by native_decide

/--
Example: H_5 has 1 + 5 + 10 = 16 vertices.
-/
theorem h5_vertex_count : hkVertexCount 5 = 16 := by native_decide

/--
**Edge count of H_k:**
- k edges from x to each y_i
- 2 · (k choose 2) edges from each z_ij to y_i and y_j
-/
def hkEdgeCount (k : ℕ) : ℕ := k + 2 * Nat.choose k 2

/--
Example: H_4 has 4 + 12 = 16 edges.
-/
theorem h4_edge_count : hkEdgeCount 4 = 16 := by native_decide

/-
## Part II: Properties of H_k
-/

/--
**H_k contains C_4:**
For k ≥ 3, H_k contains a 4-cycle: x - y_1 - z_12 - y_2 - x.
This gives the lower bound ex(n; H_k) ≫ n^(3/2).
-/

/--
**H_k is 2-degenerate:**
Every subgraph of H_k has a vertex of degree at most 2.
The z_ij vertices all have degree exactly 2.
-/

/--
**H_k is bipartite:**
One part: {x} ∪ {z_ij}
Other part: {y_1, ..., y_k}
-/

/-
## Part III: Extremal Numbers
-/

/--
**Extremal number:**
ex(n; H) is the maximum number of edges in an n-vertex graph containing no H.
-/

/--
**Kővári-Sós-Turán Theorem:**
For the complete bipartite graph K_{r,s}:
ex(n; K_{r,s}) ≤ (1/2)(s-1)^(1/r) n^(2-1/r) + (r-1)n/2

For C_4 = K_{2,2}: ex(n; C_4) ≤ (1/2)n^(3/2) + n/2 ~ (1/2)n^(3/2)
-/

/--
**C_4 extremal number:**
ex(n; C_4) ~ (1/2)n^(3/2) (tight up to constant).
-/

/-
## Part IV: Lower Bound
-/

/--
**Lower Bound:**
Since H_k contains C_4, we have ex(n; H_k) ≥ ex(n; C_4) ~ n^(3/2).

This is trivial: if a graph avoids H_k, it may still contain C_4.
But if it avoids C_4, it avoids H_k (since H_k ⊇ C_4).
So ex(n; H_k) ≥ ex(n; C_4).
-/

/-
## Part V: Füredi's Theorem (1991)
-/

/--
**Füredi's Theorem (1991):**
For k ≥ 3: ex(n; H_k) ≪ (kn)^(3/2).

The proof uses probabilistic methods and dependent random choice.
-/

/-
## Part VI: Alon-Krivelevich-Sudakov Improvement (2003)
-/

/--
**Alon-Krivelevich-Sudakov Theorem (2003):**
For k ≥ 3: ex(n; H_k) ≪ k · n^(3/2).

This improves Füredi's (kn)^(3/2) to k · n^(3/2).
-/
/- erdos_926: **Erdős Problem #926: SOLVED**
The answer is YES: ex(n; H_k) ≪_k n^(3/2). -/

/-
## Part VII: Connection to Degeneracy
-/

/--
**2-Degenerate Graphs Conjecture (Problem 146):**
For any 2-degenerate graph H: ex(n; H) ≪ n^(3/2).

Since H_k is 2-degenerate, this problem is a special case of [146].
-/

/--
**Degeneracy bounds:**
For d-degenerate graphs, ex(n; H) = O(n^(2-1/d)).
For d = 2: ex(n; H) = O(n^(3/2)).
-/

/-
## Part VIII: Related Problems
-/

/--
**Problem 1021:**
The extremal number of H_k with vertex x removed.
This is a separate Erdős problem with different behavior.
-/
def hkMinusX (k : ℕ) : Type := Unit  -- The graph H_k without x

/--
**Erdős's Original Claim (1971):**
Erdős claimed a proof for k = 3 in his 1971 paper.
The general case required the later work of Füredi.
-/

/-
## Part IX: Probabilistic Method Connection
-/

/--
**Dependent Random Choice:**
The proofs by Füredi and AKS use the dependent random choice method.

Key idea: Choose a random subset S of vertices by taking common neighbors
of a random tuple. This gives a set with:
- Controlled size
- High minimum degree (in a bipartite sense)
- Properties useful for embedding forbidden subgraphs
-/

/--
**Container Method:**
Alternative approach using hypergraph containers.
-/

/-
## Part X: Main Results Summary
-/

/-
**Erdős Problem #926: Summary (open formalization)**

Question: Is ex(n; H_k) ≪_k n^(3/2) for k ≥ 4?

Answer: YES (Füredi 1991, Alon-Krivelevich-Sudakov 2003)

Timeline:
- 1971: Erdős poses the problem, claims k = 3 case
- 1991: Füredi proves ex(n; H_k) ≪ (kn)^(3/2)
- 2003: Alon-Krivelevich-Sudakov improve to k · n^(3/2)

The lower bound n^(3/2) is trivial (H_k contains C_4).

Full formalization requires the probabilistic method and dependent random choice,
not yet available in Mathlib.
-/

/- erdos_926_order: The order of magnitude is n^(3/2) for all k ≥ 3. -/


end Erdos926
