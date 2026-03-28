/- Erdős Problem #719 — Hypergraph Decomposition into Cliques

Let ex_r(n; K_{r+1}^r) denote the Turán number for r-uniform
hypergraphs: the maximum number of r-edges on n vertices avoiding
a complete (r+1)-clique K_{r+1}^r.

Conjecture (Erdős–Sauer): Is every r-uniform hypergraph G on n
vertices the union of at most ex_r(n; K_{r+1}^r) copies of
K_r^r and K_{r+1}^r, no two of which share a K_r^r?

Status: OPEN
Reference: https://erdosproblems.com/719
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

-- ## r-Uniform Hypergraphs

/-- An r-uniform hypergraph on a finite vertex set V, represented by a family
    of r-element subsets. -/
structure RUniformHypergraph (V : Type*) [DecidableEq V] [Fintype V] (r : ℕ) where
  /-- The edge set: a family of Finsets of vertices -/
  edges : Finset (Finset V)
  /-- Every edge has exactly r vertices -/
  uniform : ∀ e ∈ edges, e.card = r

/-- The complete r-uniform clique on a vertex set S: all r-element subsets of S.
    When S has r+1 vertices, this is K_{r+1}^r. -/
def completeClique {V : Type*} [DecidableEq V] (r : ℕ) (S : Finset V) :
    Finset (Finset V) :=
  S.powerset.filter (fun e => e.card = r)

/-- An (r+1)-clique K_{r+1}^r consists of all r-subsets of an (r+1)-element set. -/
def IsFullClique {V : Type*} [DecidableEq V] (r : ℕ)
    (S : Finset V) (edges : Finset (Finset V)) : Prop :=
  S.card = r + 1 ∧ edges = completeClique r S

/-- An edge of the hypergraph viewed as a "trivial clique" K_r^r (a single r-edge). -/
def IsSingleEdge {V : Type*} [DecidableEq V] (r : ℕ)
    (e : Finset V) (edges : Finset (Finset V)) : Prop :=
  e.card = r ∧ edges = {e}

-- ## Decomposition

/-- A piece of the decomposition is either a single r-edge or a full (r+1)-clique. -/
def IsDecompPiece {V : Type*} [DecidableEq V] (r : ℕ)
    (piece : Finset (Finset V)) : Prop :=
  (∃ e : Finset V, IsSingleEdge r e piece) ∨
  (∃ S : Finset V, IsFullClique r S piece)

/-- Two pieces are r-edge-disjoint: they share no common r-element subset. -/
def PiecesEdgeDisjoint {V : Type*} [DecidableEq V]
    (piece₁ piece₂ : Finset (Finset V)) : Prop :=
  ∀ e : Finset V, ¬(e ∈ piece₁ ∧ e ∈ piece₂)

/-- A valid decomposition of an r-uniform hypergraph: a family of pieces that
    are edge-disjoint, each piece is a single edge or full clique, and they
    cover all edges. -/
structure IsValidDecomp {V : Type*} [DecidableEq V] [Fintype V] (r : ℕ)
    (H : RUniformHypergraph V r)
    (pieces : Finset (Finset (Finset V))) : Prop where
  /-- Each piece is a single edge or full clique -/
  pieces_valid : ∀ p ∈ pieces, IsDecompPiece r p
  /-- Pieces are pairwise edge-disjoint -/
  pairwise_disjoint : ∀ p₁ ∈ pieces, ∀ p₂ ∈ pieces, p₁ ≠ p₂ →
    PiecesEdgeDisjoint p₁ p₂
  /-- The pieces cover all edges of H -/
  covers : ∀ e ∈ H.edges, ∃ p ∈ pieces, e ∈ p

-- ## Turán Number

/-- Whether an r-uniform hypergraph on V is K_{r+1}^r-free:
    no (r+1)-element subset has all its r-subsets as edges. -/
def IsCliqueFree {V : Type*} [DecidableEq V] (r : ℕ)
    (H : RUniformHypergraph V r) : Prop :=
  ∀ S : Finset V, S.card = r + 1 →
    ¬(completeClique r S ⊆ H.edges)

/-- The Turán number ex_r(n; K_{r+1}^r): the maximum number of r-edges
    on n vertices avoiding a complete (r+1)-clique.

    For r = 2, this equals ⌊n²/4⌋ by Turán's theorem (1941).
    For r ≥ 3, computing this is itself a major open problem. -/
noncomputable def turanHypergraph (n r : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (H : RUniformHypergraph (Fin n) r),
    IsCliqueFree r H ∧ H.edges.card = m}

-- ## Main Conjecture (OPEN)

/-- **Erdős–Sauer Conjecture (1981)**: Every r-uniform hypergraph on n
    vertices can be decomposed into at most ex_r(n; K_{r+1}^r) pieces,
    where each piece is either a single r-edge (K_r^r) or a complete
    (r+1)-clique (K_{r+1}^r), and no two pieces share an r-edge.

    This is an OPEN problem. -/
axiom erdos_sauer_conjecture :
  ∀ (n r : ℕ), r ≥ 2 →
    ∀ (H : RUniformHypergraph (Fin n) r),
      ∃ (pieces : Finset (Finset (Finset (Fin n)))),
        IsValidDecomp r H pieces ∧
        pieces.card ≤ turanHypergraph n r

-- ## Graph Case (r = 2)

/-- For graphs (r = 2), the Turán number ex₂(n; K₃) equals ⌊n²/4⌋.
    This is Turán's theorem (1941), proved by showing the complete
    bipartite graph K_{⌊n/2⌋,⌈n/2⌉} achieves the maximum. -/
axiom turan_graph : ∀ n : ℕ, turanHypergraph n 2 = n ^ 2 / 4

/-- The graph case of the Erdős–Sauer conjecture specializes to:
    every graph on n vertices is decomposable into at most ⌊n²/4⌋
    edges and triangles with no two pieces sharing an edge. -/
theorem graph_case_bound (n : ℕ) (H : RUniformHypergraph (Fin n) 2)
    (hdecomp : ∃ pieces, IsValidDecomp 2 H pieces ∧
      pieces.card ≤ turanHypergraph n 2) :
    ∃ pieces, IsValidDecomp 2 H pieces ∧
      pieces.card ≤ n ^ 2 / 4 := by
  obtain ⟨pieces, hvalid, hbound⟩ := hdecomp
  exact ⟨pieces, hvalid, turan_graph n ▸ hbound⟩

-- ## Structural Results

/-- C(r+1, r) = r+1: a complete (r+1)-clique has exactly r+1 edges. -/
theorem choose_succ_self (r : ℕ) : Nat.choose (r + 1) r = r + 1 := by
  rw [Nat.choose_symm (Nat.le_succ r)]
  simp [Nat.choose]

/-- Edges in a complete clique are subsets of the vertex set. -/
theorem completeClique_subset {V : Type*} [DecidableEq V] (r : ℕ) (S : Finset V) :
    ∀ e ∈ completeClique r S, e ⊆ S := by
  intro e he
  simp [completeClique, Finset.mem_filter, Finset.mem_powerset] at he
  exact he.1

/-- Edges in a complete clique have exactly r elements. -/
theorem completeClique_uniform {V : Type*} [DecidableEq V] (r : ℕ) (S : Finset V) :
    ∀ e ∈ completeClique r S, e.card = r := by
  intro e he
  simp [completeClique, Finset.mem_filter] at he
  exact he.2

/-- PiecesEdgeDisjoint is symmetric. -/
theorem piecesEdgeDisjoint_comm {V : Type*} [DecidableEq V]
    (p₁ p₂ : Finset (Finset V)) :
    PiecesEdgeDisjoint p₁ p₂ ↔ PiecesEdgeDisjoint p₂ p₁ := by
  simp only [PiecesEdgeDisjoint, and_comm]

-- ## Clique Cardinality

/-- completeClique r S equals powersetCard r S: the family of all r-element
    subsets of S. This connects our definition to Mathlib's combinatorial API. -/
theorem completeClique_eq_powersetCard {V : Type*} [DecidableEq V] (r : ℕ) (S : Finset V) :
    completeClique r S = S.powersetCard r := by
  ext e
  simp [completeClique, Finset.mem_powersetCard, Finset.mem_filter, Finset.mem_powerset]

/-- The number of r-edges in a complete clique on S equals C(|S|, r). -/
theorem completeClique_card {V : Type*} [DecidableEq V] (r : ℕ) (S : Finset V) :
    (completeClique r S).card = Nat.choose S.card r := by
  rw [completeClique_eq_powersetCard, Finset.card_powersetCard]

/-- A complete (r+1)-clique K_{r+1}^r has exactly r+1 hyperedges. -/
theorem fullClique_edge_count {V : Type*} [DecidableEq V] (r : ℕ) (S : Finset V)
    (hS : S.card = r + 1) :
    (completeClique r S).card = r + 1 := by
  rw [completeClique_card, hS, Nat.choose_succ_self_right]

/-- completeClique is monotone: larger vertex sets yield more r-edges. -/
theorem completeClique_mono {V : Type*} [DecidableEq V] (r : ℕ) {S T : Finset V} (h : S ⊆ T) :
    completeClique r S ⊆ completeClique r T := by
  intro e he
  rw [completeClique_eq_powersetCard] at he ⊢
  exact Finset.powersetCard_mono h he

/-- Each piece in a valid decomposition has at most r + 1 edges:
    single edges contribute 1, full cliques contribute r + 1. -/
theorem decomp_piece_card_le {V : Type*} [DecidableEq V] [Fintype V] (r : ℕ)
    (H : RUniformHypergraph V r) (pieces : Finset (Finset (Finset V)))
    (hdecomp : IsValidDecomp r H pieces)
    (p : Finset (Finset V)) (hp : p ∈ pieces) :
    p.card ≤ r + 1 := by
  rcases hdecomp.pieces_valid p hp with ⟨e, he⟩ | ⟨S, hS⟩
  · -- p = {e}: a single r-edge
    have : p = {e} := he.2
    subst this; simp
  · -- p = completeClique r S with |S| = r+1
    have hcard : S.card = r + 1 := hS.1
    have : p = completeClique r S := hS.2
    subst this
    rw [completeClique_card, hcard, Nat.choose_succ_self_right]

-- ## Edge Counting and Turán Bound

/-- Any r-uniform hypergraph on Fin n has at most C(n, r) edges,
    since each edge is an r-element subset of an n-element set. -/
theorem edges_le_choose (n r : ℕ) (H : RUniformHypergraph (Fin n) r) :
    H.edges.card ≤ Nat.choose n r := by
  calc H.edges.card
      ≤ ((Finset.univ : Finset (Fin n)).powersetCard r).card := by
        apply Finset.card_le_card
        intro e he
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ e, H.uniform e he⟩
    _ = Nat.choose n r := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The set of edge counts of clique-free r-uniform hypergraphs on Fin n
    is bounded above by C(n, r). -/
theorem cliqueFree_edgeCounts_bddAbove (n r : ℕ) :
    BddAbove {m : ℕ | ∃ (H : RUniformHypergraph (Fin n) r),
      IsCliqueFree r H ∧ H.edges.card = m} := by
  refine ⟨Nat.choose n r, fun m hm => ?_⟩
  obtain ⟨G, -, rfl⟩ := hm
  exact edges_le_choose n r G

/-- Any clique-free r-uniform hypergraph has at most turanHypergraph n r edges.
    This is the fundamental property of the Turán number as a supremum. -/
theorem cliqueFree_le_turan (n r : ℕ) (H : RUniformHypergraph (Fin n) r)
    (hcf : IsCliqueFree r H) :
    H.edges.card ≤ turanHypergraph n r :=
  le_csSup (cliqueFree_edgeCounts_bddAbove n r) ⟨H, hcf, rfl⟩

-- ## Empty and Trivial Cases

/-- The empty hypergraph trivially satisfies the Erdős–Sauer conjecture. -/
theorem empty_case (n r : ℕ) (hr : r ≥ 2) :
    let H : RUniformHypergraph (Fin n) r :=
      ⟨∅, fun _ h => absurd h (Finset.not_mem_empty _)⟩
    ∃ pieces : Finset (Finset (Finset (Fin n))),
      IsValidDecomp r H pieces ∧
      pieces.card ≤ turanHypergraph n r := by
  refine ⟨∅, ?_, ?_⟩
  · exact {
      pieces_valid := fun p hp => absurd hp (Finset.not_mem_empty _)
      pairwise_disjoint := fun p₁ hp₁ => absurd hp₁ (Finset.not_mem_empty _)
      covers := fun e he => absurd he (Finset.not_mem_empty _)
    }
  · simp

/-- NOTE: A previous version claimed pieces.card ≤ H.edges.card for any
    valid decomposition. This is FALSE: the IsValidDecomp structure allows
    "phantom" pieces (valid single-edge or clique pieces whose edges are not
    in H). Counterexample: H with 1 edge e₁, pieces = {{e₁}, {e₂}} where
    e₂ ∉ H.edges. Both valid, disjoint, covers satisfied, but pieces.card = 2
    > 1 = H.edges.card. The correct statement would need an additional
    hypothesis: ∀ p ∈ pieces, ∀ e ∈ p, e ∈ H.edges. -/

/-- The trivial decomposition: every r-edge becomes its own piece (K_r^r).
    This always works but uses one piece per edge. -/
theorem trivial_decomp_exists (n r : ℕ) (H : RUniformHypergraph (Fin n) r) :
    ∃ pieces : Finset (Finset (Finset (Fin n))),
      IsValidDecomp r H pieces ∧
      pieces.card ≤ H.edges.card := by
  -- Construct: pieces = { {e} | e ∈ H.edges }
  refine ⟨H.edges.image (fun e => ({e} : Finset (Finset (Fin n)))), ?_, ?_⟩
  · exact {
      pieces_valid := by
        intro p hp
        simp only [Finset.mem_image] at hp
        obtain ⟨e, he, rfl⟩ := hp
        exact Or.inl ⟨e, H.uniform e he, rfl⟩
      pairwise_disjoint := by
        intro p₁ hp₁ p₂ hp₂ hne
        simp only [Finset.mem_image] at hp₁ hp₂
        obtain ⟨e₁, _, rfl⟩ := hp₁
        obtain ⟨e₂, _, rfl⟩ := hp₂
        intro e
        simp only [Finset.mem_singleton, not_and]
        intro h1 h2
        exact hne (by rw [h1, h2])
      covers := by
        intro e he
        exact ⟨{e}, Finset.mem_image.mpr ⟨e, he, rfl⟩, Finset.mem_singleton.mpr rfl⟩
    }
  · exact Finset.card_image_le

-- ## Relationship to Other Problems

/- The Erdős–Sauer conjecture relates to Turán-type extremal hypergraph
    theory. The graph case (r=2) connects to Erdős' result on edge-disjoint
    triangle decompositions.

    Related Erdős problems:
    - #718: Lower bounds on Turán numbers for hypergraphs
    - #720: Turán densities for higher uniformity
    - #83: Triangle decomposition problems for dense graphs -/

-- ## Turán's Theorem for Graphs — Axiom Elimination Path
-- Goal: prove `turanHypergraph n 2 = n ^ 2 / 4` to replace the `turan_graph` axiom.
-- Strategy: construct the bipartite hypergraph, prove clique-free, count edges.

/-- The complete bipartite hypergraph on Fin n: edges are 2-element subsets
    {v, w} where v and w have different parity (v % 2 ≠ w % 2).
    This is the hypergraph analogue of Mathlib's `turanGraph n 2`. -/
def completeBipartiteHypergraph (n : ℕ) : RUniformHypergraph (Fin n) 2 where
  edges := ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
    (fun e => ∃ v ∈ e, ∃ w ∈ e, v ≠ w ∧ (v : ℕ) % 2 ≠ (w : ℕ) % 2)
  uniform := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at he
    exact he.1.2

/-- The complete bipartite hypergraph is triangle-free (K₃²-free).
    Proof sketch: Among 3 vertices, two share parity mod 2 (pigeonhole).
    Their pair is not a bipartite edge, contradicting coverage. -/
theorem completeBipartiteHypergraph_cliqueFree (n : ℕ) :
    IsCliqueFree 2 (completeBipartiteHypergraph n) := by
  intro S hS hcontain
  -- S has 3 elements. The map (· : Fin n).val % 2 : S → {0, 1} is not injective.
  -- Two vertices v, w ∈ S satisfy v % 2 = w % 2.
  -- The edge {v, w} ∈ completeClique 2 S, so {v, w} ∈ (completeBipartiteHypergraph n).edges.
  -- But bipartite edges require v % 2 ≠ w % 2: contradiction.
  sorry

/-- The complete bipartite hypergraph has ⌊n²/4⌋ edges.
    This equals ⌊n/2⌋ * ⌈n/2⌉ = ⌊n/2⌋ * (n - ⌊n/2⌋). -/
theorem completeBipartiteHypergraph_card (n : ℕ) :
    (completeBipartiteHypergraph n).edges.card = n ^ 2 / 4 := by
  sorry

/-- Lower bound on the graph Turán number: turanHypergraph n 2 ≥ ⌊n²/4⌋.
    Follows from cliqueFree_le_turan applied to the bipartite construction. -/
theorem turanHypergraph_graph_ge (n : ℕ) :
    n ^ 2 / 4 ≤ turanHypergraph n 2 := by
  rw [← completeBipartiteHypergraph_card n]
  exact cliqueFree_le_turan n 2 _ (completeBipartiteHypergraph_cliqueFree n)

/-- Upper bound on the graph Turán number: turanHypergraph n 2 ≤ ⌊n²/4⌋.
    This is the hard direction of Turán's theorem for graphs.
    Can be proved via bridge to Mathlib's SimpleGraph.CliqueFree.card_edgeFinset_le
    (import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan). -/
theorem turanHypergraph_graph_le (n : ℕ) :
    turanHypergraph n 2 ≤ n ^ 2 / 4 := by
  sorry

/-- **Turán's theorem for graphs**: the 2-uniform Turán number equals ⌊n²/4⌋.
    Once the three sorries above are resolved, this replaces the `turan_graph` axiom. -/
theorem turan_graph_proved (n : ℕ) :
    turanHypergraph n 2 = n ^ 2 / 4 :=
  le_antisymm (turanHypergraph_graph_le n) (turanHypergraph_graph_ge n)
