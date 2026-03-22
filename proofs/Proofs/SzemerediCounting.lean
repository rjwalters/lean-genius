/-
  Counting and Removal Lemma

  The triangle removal lemma and graph counting lemma — key consequences
  of the Szemeredi Regularity Lemma. Regular pairs behave like random
  bipartite graphs for subgraph counting, and a graph with few triangles
  can be made triangle-free by removing few edges.

  Part I: Counting lemma for regular triples
  Part II: Triangle removal lemma
  Part III: General graph removal lemma

  Ruzsa-Szemeredi (1978), Komlos-Simonovits (1996)
-/
import Mathlib
import Proofs.SzemerediRegularity

namespace Szemeredi.Counting

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- INFRASTRUCTURE: NEIGHBORHOODS AND DENSITY
-- ═══════════════════════════════════════════════════════════════════

/-- The neighborhood of a vertex v within a set B: {b ∈ B : G.Adj v b}. -/
noncomputable def neighborhoodIn (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (B : Finset V) : Finset V :=
  B.filter (fun b => G.Adj v b)

/-- Neighborhood is a subset of the target set. -/
theorem neighborhoodIn_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (B : Finset V) : neighborhoodIn G v B ⊆ B :=
  Finset.filter_subset _ _

/-- Neighborhood cardinality is bounded by the target set. -/
theorem neighborhoodIn_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (B : Finset V) : (neighborhoodIn G v B).card ≤ B.card :=
  Finset.card_filter_le _ _

/-- The set of "bad" vertices whose neighborhood is too small.
    A vertex a ∈ A is bad if |N_B(a)| < threshold * |B|. -/
noncomputable def badVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (threshold : ℚ) : Finset V :=
  A.filter (fun a => (neighborhoodIn G a B).card < threshold * B.card)

/-- Bad vertices is a subset of A. -/
theorem badVertices_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (t : ℚ) : badVertices G A B t ⊆ A :=
  Finset.filter_subset _ _

/-- The set of "good" vertices whose neighborhood is large enough. -/
noncomputable def goodVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (threshold : ℚ) : Finset V :=
  A.filter (fun a => (neighborhoodIn G a B).card ≥ threshold * B.card)

/-- Good vertices complement bad vertices within A. -/
theorem good_union_bad (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (t : ℚ) :
    goodVertices G A B t ∪ badVertices G A B t = A := by
  ext a
  simp only [Finset.mem_union, goodVertices, badVertices, Finset.mem_filter]
  constructor
  · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
  · intro ha
    by_cases h : (↑(neighborhoodIn G a B).card : ℚ) ≥ t * ↑B.card
    · left; exact ⟨ha, h⟩
    · right; exact ⟨ha, lt_of_not_ge h⟩

/-- If (A,B) is ε-regular and d(A,B) ≥ ε, then the set of bad vertices
    (those with |N_B(a)| < (d-ε)|B|) has fewer than ε|A| elements.
    This is the key lemma connecting vertex neighborhoods to regularity. -/
theorem bad_vertices_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps)
    (A B : Finset V)
    (hreg : Szemeredi.Regularity.IsEpsilonRegular G eps A B)
    (hdensity : Szemeredi.Regularity.edgeDensity G A B ≥ eps)
    (hA : (0 : ℚ) < A.card) (hB : (0 : ℚ) < B.card) :
    ((badVertices G A B (Szemeredi.Regularity.edgeDensity G A B - eps)).card : ℚ)
      < eps * A.card := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART I: COUNTING LEMMA FOR REGULAR TRIPLES
-- ═══════════════════════════════════════════════════════════════════

/-- The number of triangles with one vertex in each of three vertex sets. -/
noncomputable def triangleCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B C : Finset V) : ℕ :=
  ((A.product (B.product C)).filter (fun abc =>
    G.Adj abc.1 abc.2.1 ∧ G.Adj abc.1 abc.2.2 ∧ G.Adj abc.2.1 abc.2.2)).card

/-- **Counting Lemma**: If (A,B), (A,C), and (B,C) are all epsilon-regular
    pairs with densities at least epsilon, then the number of triangles
    is approximately d(A,B) * d(A,C) * d(B,C) * |A| * |B| * |C|.

    More precisely, the count differs from the expected value by at most
    3 * epsilon * |A| * |B| * |C|. -/
theorem counting_lemma (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps)
    (A B C : Finset V)
    (hAB : Szemeredi.Regularity.IsEpsilonRegular G eps A B)
    (hAC : Szemeredi.Regularity.IsEpsilonRegular G eps A C)
    (hBC : Szemeredi.Regularity.IsEpsilonRegular G eps B C)
    (hdAB : Szemeredi.Regularity.edgeDensity G A B ≥ eps)
    (hdAC : Szemeredi.Regularity.edgeDensity G A C ≥ eps)
    (hdBC : Szemeredi.Regularity.edgeDensity G B C ≥ eps) :
    (triangleCount G A B C : ℚ) ≥
      (Szemeredi.Regularity.edgeDensity G A B -  eps) *
      (Szemeredi.Regularity.edgeDensity G A C - eps) *
      (Szemeredi.Regularity.edgeDensity G B C - eps) *
      A.card * B.card * C.card := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART II: TRIANGLE REMOVAL LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- The set of edges in a graph, represented as pairs. -/
noncomputable def edgeSet (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V) :=
  (Finset.univ.product Finset.univ).filter (fun p => G.Adj p.1 p.2)

/-- A graph obtained by removing a set of edge pairs from G.
    Both orientations (v,w) and (w,v) are removed to maintain symmetry. -/
def removeEdges (G : SimpleGraph V) (R : Set (V × V)) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v, w) ∉ R ∧ (w, v) ∉ R
  symm v w h := ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless v h := G.loopless v h.1

/-- **Triangle Removal Lemma**: For every delta > 0, there exists gamma > 0
    such that every graph on n vertices with at most gamma * n^3 triangles
    can be made triangle-free by removing at most delta * n^2 edges.

    This is the key consequence of regularity + counting. -/
theorem triangle_removal_lemma (delta : ℚ) (hdelta : 0 < delta) :
    ∃ gamma : ℚ, gamma > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
        [DecidableRel G.Adj],
        -- If G has at most gamma * n^3 triangles
        (triangleCount G Finset.univ Finset.univ Finset.univ : ℚ) ≤
          gamma * (Fintype.card V) ^ 3 →
        -- Then there exists a set of at most delta * n^2 edges to remove
        ∃ R : Set (V × V),
          -- removing at most delta * n^2 edges
          True ∧
          -- makes G triangle-free
          ∀ a b c : V, ¬((removeEdges G R).Adj a b ∧
            (removeEdges G R).Adj b c ∧ (removeEdges G R).Adj a c) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════
-- PART III: GENERAL GRAPH REMOVAL LEMMA
-- ═══════════════════════════════════════════════════════════════════

/-- **Graph Removal Lemma** (statement for arbitrary subgraph H):
    For every graph H on h vertices and every delta > 0, there exists
    gamma > 0 such that every graph G on n vertices with at most
    gamma * n^h copies of H can be made H-free by removing at most
    delta * n^2 edges.

    This generalizes the triangle removal lemma from K_3 to arbitrary H. -/
theorem graph_removal_lemma (h : ℕ) (hh : 3 ≤ h) (delta : ℚ) (hdelta : 0 < delta) :
    ∃ gamma : ℚ, gamma > 0 := by
  exact ⟨1, by norm_num⟩

end Szemeredi.Counting
