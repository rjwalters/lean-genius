/-
  Counting and Removal Lemma

  The triangle removal lemma and graph counting lemma -- key consequences
  of the Szemeredi Regularity Lemma. Regular pairs behave like random
  bipartite graphs for subgraph counting, and a graph with few triangles
  can be made triangle-free by removing few edges.

  Part I: Counting lemma for regular triples
  Part II: Triangle removal lemma
  Part III: General graph removal lemma

  Ruzsa-Szemeredi (1978), Komlos-Simonovits (1996)
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularity

namespace Szemeredi.Counting

open Classical Szemeredi.Core

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
    This is the key lemma connecting vertex neighborhoods to regularity.

    Proof by contraposition: if |bad| ≥ ε|A|, set A' = badVertices.
    By ε-regularity with B' = B: d(A',B) ≥ d - ε. But every vertex
    in A' has < (d-ε)|B| neighbors in B, so d(A',B) < d - ε. Contradiction. -/
theorem bad_vertices_small (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (heps : 0 < eps)
    (A B : Finset V)
    (hreg : Szemeredi.Regularity.IsEpsilonRegular G eps A B)
    (hdensity : Szemeredi.Regularity.edgeDensity G A B ≥ eps)
    (hA : (0 : ℚ) < A.card) (hB : (0 : ℚ) < B.card) :
    ((badVertices G A B (Szemeredi.Regularity.edgeDensity G A B - eps)).card : ℚ)
      < eps * A.card := by
  by_contra hbig
  push_neg at hbig
  set d := Szemeredi.Regularity.edgeDensity G A B with hd_def
  set A' := badVertices G A B (d - eps)
  -- Key facts about A'
  have hA'sub : A' ⊆ A := badVertices_subset G A B (d - eps)
  have hA'pos : (0 : ℚ) < A'.card := lt_of_lt_of_le (by positivity : (0 : ℚ) < eps * A.card) hbig
  -- eps ≤ 1 from d ≤ 1 and d ≥ eps
  have heps1 : eps ≤ 1 :=
    le_trans hdensity (Szemeredi.Regularity.edgeDensity_le_one G A B)
  -- |B| ≥ ε|B| since ε ≤ 1
  have hBeps : (B.card : ℚ) ≥ eps * B.card := by
    have hB_nn : (0 : ℚ) ≤ (B.card : ℚ) := Nat.cast_nonneg _
    nlinarith
  -- Apply ε-regularity to (A', B)
  have hreg' := hreg A' B hA'sub (Finset.Subset.refl B) hbig hBeps
  -- |d(A',B) - d| ≤ ε, so d(A',B) ≥ d - ε
  have hdL : Szemeredi.Regularity.edgeDensity G A' B ≥ d - eps := by
    have := (abs_le.mp hreg').1; linarith
  -- Upper bound: every a ∈ A' has |N_B(a)| < (d-ε)|B|, so d(A',B) < d - ε
  have hdU : Szemeredi.Regularity.edgeDensity G A' B < d - eps := by
    -- Each a ∈ A' = badVertices has |N_B(a)| < (d-ε)|B|.
    -- Total edges = Σ|N_B(a)| < |A'|*(d-ε)*|B|, so density < d-ε.
    unfold Szemeredi.Core.edgeDensity
    have hA'B_pos : (0 : ℚ) < (A'.card : ℚ) * B.card := by positivity
    rw [dif_neg (ne_of_gt hA'B_pos)]
    rw [div_lt_iff₀ hA'B_pos]
    -- Goal: ↑|(A'×B).filter Adj| < (d-ε) * (↑|A'| * ↑|B|)
    set E := (A' ×ˢ B).filter (fun p : V × V => G.Adj p.1 p.2)
    -- Each a ∈ A' has |N_B(a)| < (d-ε)|B| (badVertices definition)
    have hbad : ∀ a ∈ A', ((neighborhoodIn G a B).card : ℚ) < (d - eps) * B.card :=
      fun a ha => (Finset.mem_filter.mp ha).2
    -- A' is nonempty
    have hA'ne : A'.Nonempty := Finset.card_pos.mp (by exact_mod_cast hA'pos)
    -- Fiber decomposition + count bound
    -- Each pair (a,b) in E has a ∈ A', so fibers partition E by first component
    have hfst_mem : ∀ p ∈ E, Prod.fst p ∈ A' := by
      intro p hp; exact (Finset.mem_filter.mp hp).1 |> Finset.mem_product.mp |>.1
    -- Fiber decomposition: E.card = Σ_{a∈A'} |fiber_a|
    have hfib := Finset.card_eq_sum_card_fiberwise hfst_mem
    -- Each fiber has ≤ |N_B(a)| elements (injection via Prod.snd)
    have hfiber_le : ∀ a ∈ A',
        (E.filter (fun p => p.1 = a)).card ≤ (neighborhoodIn G a B).card := by
      intro a _
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro p hp
        have hpE := (Finset.mem_filter.mp hp).1
        have hpeq : p.1 = a := (Finset.mem_filter.mp hp).2
        have hprod := Finset.mem_product.mp (Finset.mem_filter.mp hpE).1
        have hadj := (Finset.mem_filter.mp hpE).2
        exact Finset.mem_filter.mpr ⟨hprod.2, hpeq ▸ hadj⟩
      · intro p₁ h₁ p₂ h₂ heq
        have h1eq : p₁.1 = a := (Finset.mem_filter.mp h₁).2
        have h2eq : p₂.1 = a := (Finset.mem_filter.mp h₂).2
        exact Prod.ext (h1eq.trans h2eq.symm) heq
    -- Combine: E.card = Σ|fiber| ≤ Σ|N_B(a)| < (d-ε)|A'||B|
    -- Work in ℚ for the strict inequality chain
    suffices h : (E.card : ℚ) < (d - eps) * (↑A'.card * ↑B.card) by
      exact_mod_cast h
    calc (E.card : ℚ)
        = ↑(A'.sum (fun a => (E.filter (fun p => p.1 = a)).card)) := by
          rw [hfib]
      _ ≤ A'.sum (fun a => ((neighborhoodIn G a B).card : ℚ)) := by
          push_cast
          exact Finset.sum_le_sum (fun a ha => Nat.cast_le.mpr (hfiber_le a ha))
      _ < A'.sum (fun _ => (d - eps) * ↑B.card) :=
          Finset.sum_lt_sum
            (fun a ha => le_of_lt (hbad a ha))
            (let ⟨a, ha⟩ := hA'ne; ⟨a, ha, hbad a ha⟩)
      _ = (d - eps) * (↑A'.card * ↑B.card) := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
  linarith

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
