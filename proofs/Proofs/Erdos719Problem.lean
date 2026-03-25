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

/-- Any valid decomposition has at most as many pieces as edges,
    since each piece covers at least one distinct edge by edge-disjointness. -/
theorem decomp_pieces_le_edges {V : Type*} [DecidableEq V] [Fintype V]
    (r : ℕ) (H : RUniformHypergraph V r)
    (pieces : Finset (Finset (Finset V)))
    (hdecomp : IsValidDecomp r H pieces) :
    pieces.card ≤ H.edges.card := by
  sorry

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
