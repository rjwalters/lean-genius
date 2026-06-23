/-
  Aristotle targets for Erdős Problem #715: Regular Subgraphs in Regular Graphs
  Routine supporting lemmas for automated proof search.
  See Erdos715Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (tashkinov_theorem, alon_friedland_kalai — deep research)
  - NOT the Petersen graph properties (complex adjacency definition)
  - NOT the threshold characterization (depends on main results)
  - Finite decidable instances: K4 regularity and minimality
  - Combinatorial parity argument: regularity implies even degree sum
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (3):
  - K4_is_3_regular_ari: every vertex of K4 has degree 3 (decidable on Fin 4)
  - K4_minimal_3_regular_ari: any 3-regular subgraph of K4 is K4 itself (finite check)
  - regular_parity_ari: r-regular graph on n vertices has even r*n (handshaking)
-/
import Proofs.Erdos715Problem
import Mathlib

namespace Erdos715Aristotle

open Erdos715 Finset

/-
## Section 1: K4 Regularity

K4 is the complete graph on 4 vertices: every vertex is adjacent to the other 3.
Hence its degree is exactly 3, making it 3-regular.
-/

/-- K4 is 3-regular: each of the 4 vertices has degree 3.
The K4 adjacency is u ≠ v, so each vertex has exactly 3 neighbors. -/
theorem K4_is_3_regular_ari : IsRegular K4 3 := by
  sorry

/-
## Section 2: K4 Minimality

The only 3-regular spanning subgraph of K4 is K4 itself.
In a 4-vertex graph, 3-regular means every pair is adjacent — so K4 is the unique
3-regular graph on these vertices.
-/

/-- Any 3-regular subgraph of K4 on Fin 4 must include all edges of K4.
A 3-regular graph on 4 vertices must have every pair adjacent (K4 is the unique one). -/
theorem K4_minimal_3_regular_ari :
    ∀ (H : SimpleGraph' (Fin 4)) [DecidableRel H.adj],
    IsSubgraph H K4 → IsRegular H 3 → ∀ u v, H.adj u v ↔ K4.adj u v := by
  sorry

/-
## Section 3: Parity of Regular Degree Sums

In any r-regular graph on n vertices, r*n = 2*(edge count), so r*n is even.
This is the handshaking lemma: the sum of all vertex degrees counts each edge twice.
-/

/-- Every r-regular finite graph satisfies: r * |V| is even (handshaking lemma).
The sum of degrees equals 2*(number of edges), so r * n = 2 * |E| is even. -/
theorem regular_parity_ari {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (r : ℕ) (hG : IsRegular G r) :
    Even (r * Fintype.card V) := by
  sorry

end Erdos715Aristotle
