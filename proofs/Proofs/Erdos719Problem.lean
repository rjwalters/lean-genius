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
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

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
def IsCliqueFree {V : Type*} [DecidableEq V] [Fintype V] (r : ℕ)
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
    This is Turán's theorem (1941), proved below via the bipartite
    construction (lower bound) and Mathlib's SimpleGraph Turán bound (upper bound).
    See turan_graph at the end of this file. -/

-- ## Structural Results

/-- C(r+1, r) = r+1: a complete (r+1)-clique has exactly r+1 edges. -/
theorem choose_succ_self (r : ℕ) : Nat.choose (r + 1) r = r + 1 := by
  simp [Nat.choose_succ_self_right]

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

/- NOTE: A previous version claimed pieces.card ≤ H.edges.card for any
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
        subst h1; subst h2
        exact absurd rfl hne
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
  -- S = {x, y, z} with x, y, z distinct
  rw [Finset.card_eq_three] at hS
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := hS
  -- Pigeonhole: among 3 elements, two share parity mod 2
  have hmod := fun (a : Fin n) => Nat.mod_two_eq_zero_or_one (a : ℕ)
  obtain ⟨a, b, hab, ha, hb, hparity⟩ :
      ∃ a b : Fin n, a ≠ b ∧ a ∈ ({x, y, z} : Finset _) ∧
        b ∈ ({x, y, z} : Finset _) ∧ (a : ℕ) % 2 = (b : ℕ) % 2 := by
    rcases hmod x with hx | hx <;> rcases hmod y with hy | hy <;>
      rcases hmod z with hz | hz <;>
    first
      | exact ⟨x, y, hxy, by simp, by simp, by omega⟩
      | exact ⟨x, z, hxz, by simp, by simp, by omega⟩
      | exact ⟨y, z, hyz, by simp, by simp, by omega⟩
  -- {a, b} ∈ completeClique 2 {x, y, z}
  have hedge : ({a, b} : Finset _) ∈ completeClique 2 ({x, y, z} : Finset (Fin n)) := by
    rw [completeClique_eq_powersetCard, Finset.mem_powersetCard]
    refine ⟨?_, Finset.card_pair hab⟩
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  -- {a, b} is in the bipartite edge set
  have hmem := hcontain hedge
  -- But bipartite edges require different parities
  simp only [completeBipartiteHypergraph, Finset.mem_filter] at hmem
  obtain ⟨_, v, hv, w, hw, hvw, hpvw⟩ := hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · exact absurd rfl hvw
  · exact hpvw hparity
  · exact hpvw hparity.symm
  · exact absurd rfl hvw

/-- The complete bipartite hypergraph has ⌊n²/4⌋ edges.
    Proof: edges biject with ordered pairs (even vertex, odd vertex),
    giving ⌈n/2⌉ * ⌊n/2⌋ = ⌊n²/4⌋. -/
theorem completeBipartiteHypergraph_card (n : ℕ) :
    (completeBipartiteHypergraph n).edges.card = n ^ 2 / 4 := by
  set evens := (Finset.univ : Finset (Fin n)).filter (fun v : Fin n => v.val % 2 = 0) with evens_def
  set odds := (Finset.univ : Finset (Fin n)).filter (fun v : Fin n => v.val % 2 = 1) with odds_def
  set f : Fin n × Fin n → Finset (Fin n) := fun p => {p.1, p.2} with f_def
  -- Step 1: edges = image of evens ×ˢ odds
  have h_eq : (completeBipartiteHypergraph n).edges = (evens ×ˢ odds).image f := by
    ext e; constructor
    · intro he
      simp only [completeBipartiteHypergraph, Finset.mem_filter,
        Finset.mem_powersetCard] at he
      obtain ⟨⟨_, hcard⟩, v, hv, w, hw, hne, hparity⟩ := he
      rw [Finset.card_eq_two] at hcard
      obtain ⟨a, b, hab, rfl⟩ := hcard
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      have hmod_v := Nat.mod_two_eq_zero_or_one v.val
      have hmod_w := Nat.mod_two_eq_zero_or_one w.val
      simp only [Finset.mem_image, Finset.mem_product, f_def]
      -- Determine which is even/odd and construct the pair
      rcases hmod_v with hve | hvo <;> rcases hmod_w with hwe | hwo
      · exfalso; exact hparity (by omega)
      · -- v even, w odd: map to (v, w), show {v, w} = {a, b}
        refine ⟨⟨v, w⟩, ⟨by simp [evens_def, hve], by simp [odds_def, hwo]⟩, ?_⟩
        -- {v, w} = {a, b} since v, w ∈ {a, b} are distinct
        rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
        · exact absurd rfl hne
        · rfl
        · exact Finset.pair_comm _ _
        · exact absurd rfl hne
      · -- v odd, w even: map to (w, v), show {w, v} = {a, b}
        refine ⟨⟨w, v⟩, ⟨by simp [evens_def, hwe], by simp [odds_def, hvo]⟩, ?_⟩
        rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
        · exact absurd rfl hne
        · exact Finset.pair_comm _ _
        · rfl
        · exact absurd rfl hne
      · exfalso; exact hparity (by omega)
    · intro he
      simp only [Finset.mem_image, Finset.mem_product, f_def] at he
      obtain ⟨⟨v, w⟩, ⟨hv_mem, hw_mem⟩, rfl⟩ := he
      simp only [evens_def, odds_def, Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem hw_mem
      simp only [completeBipartiteHypergraph, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, Finset.card_pair (by intro h; subst h; omega)⟩,
        v, Finset.mem_insert_self _ _, w,
        Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _)),
        by intro h; subst h; omega, by omega⟩
  -- Step 2: f is injective on evens ×ˢ odds
  have h_inj : Set.InjOn f ((evens ×ˢ odds : Finset _) : Set _) := by
    intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
    simp only [f_def] at heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, evens_def, odds_def,
      Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    have ha₁_mem : a₁ ∈ ({a₂, b₂} : Finset _) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha₁_mem
    have ha : a₁ = a₂ := by
      rcases ha₁_mem with rfl | rfl
      · rfl
      · exfalso; omega
    have hb₁_mem : b₁ ∈ ({a₂, b₂} : Finset _) := by
      rw [← heq]; exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb₁_mem
    have hb : b₁ = b₂ := by
      rcases hb₁_mem with rfl | rfl
      · exfalso; omega
      · rfl
    exact Prod.ext ha hb
  -- Step 3: Compute cardinality
  rw [h_eq, Finset.card_image_of_injOn h_inj, Finset.card_product]
  -- evens.card = ⌈n/2⌉, odds.card = ⌊n/2⌋
  -- Compute evens.card * odds.card = n²/4
  -- evens.card = ⌈n/2⌉ even elements in {0,...,n-1}
  -- odds.card = ⌊n/2⌋ odd elements in {0,...,n-1}
  have hevens : evens.card = (n + 1) / 2 := by
    simp only [evens_def]
    have h_eq : (Finset.univ : Finset (Fin n)).filter (fun v : Fin n => v.val % 2 = 0) =
        Finset.image (fun k : Fin ((n + 1) / 2) =>
          (⟨2 * k.val, by omega⟩ : Fin n)) Finset.univ := by
      ext ⟨v, hv⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.mk.injEq]
      constructor
      · intro hmod
        have hv_eq : v = 2 * (v / 2) := by omega
        have hbound : v / 2 < (n + 1) / 2 := by
          have := Nat.div_add_mod v 2
          have := Nat.div_add_mod (n + 1) 2
          omega
        exact ⟨⟨v / 2, hbound⟩, by simp only [Fin.val_mk]; omega⟩
      · rintro ⟨⟨k, hk⟩, heq⟩; omega
    rw [h_eq, Finset.card_image_of_injective _
      (fun a b h => by ext; simp only [Fin.mk.injEq] at h; omega)]
    simp
  have hodds : odds.card = n / 2 := by
    simp only [odds_def]
    have h_eq : (Finset.univ : Finset (Fin n)).filter (fun v : Fin n => v.val % 2 = 1) =
        Finset.image (fun k : Fin (n / 2) =>
          (⟨2 * k.val + 1, by omega⟩ : Fin n)) Finset.univ := by
      ext ⟨v, hv⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.mk.injEq]
      constructor
      · intro hmod
        have hv_eq : v = 2 * (v / 2) + 1 := by omega
        have hbound : v / 2 < n / 2 := by
          have := Nat.div_add_mod v 2
          have := Nat.div_add_mod n 2
          omega
        exact ⟨⟨v / 2, hbound⟩, by simp only [Fin.val_mk]; omega⟩
      · rintro ⟨⟨k, hk⟩, heq⟩; omega
    rw [h_eq, Finset.card_image_of_injective _
      (fun a b h => by ext; simp only [Fin.mk.injEq] at h; omega)]
    simp
  rw [hevens, hodds]
  -- ⌈n/2⌉ * ⌊n/2⌋ = n²/4 by parity case split
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- n = k + k (even)
    have h1 : (k + k) / 2 = k := by omega
    have h2 : (k + k + 1) / 2 = k := by omega
    have h3 : (k + k) ^ 2 / 4 = k * k := by
      have : (k + k) ^ 2 = 4 * (k * k) := by ring
      rw [this, Nat.mul_div_cancel_left _ (by omega : 0 < 4)]
    rw [h1, h2, h3]
  · -- n = 2 * k + 1 (odd)
    have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have h3 : (2 * k + 1) ^ 2 / 4 = k * k + k := by
      have : (2 * k + 1) ^ 2 = 4 * (k * k + k) + 1 := by ring
      rw [this]; omega
    rw [h1, h2, h3]; ring

/-- Lower bound on the graph Turán number: turanHypergraph n 2 ≥ ⌊n²/4⌋.
    Follows from cliqueFree_le_turan applied to the bipartite construction. -/
theorem turanHypergraph_graph_ge (n : ℕ) :
    n ^ 2 / 4 ≤ turanHypergraph n 2 := by
  rw [← completeBipartiteHypergraph_card n]
  exact cliqueFree_le_turan n 2 _ (completeBipartiteHypergraph_cliqueFree n)

/-- Upper bound on the graph Turán number: turanHypergraph n 2 ≤ ⌊n²/4⌋.
    This is the hard direction of Turán's theorem for graphs.
    The proof bridges to Mathlib's SimpleGraph.CliqueFree.card_edgeFinset_le:
    - Convert 2-uniform hypergraph H to SimpleGraph G (same edges)
    - IsCliqueFree 2 H implies G.CliqueFree 3 (triangle-free)
    - Apply Mathlib's Turán bound: #G.edgeFinset ≤ (n²-(n%2)²)/4 + (n%2).choose 2
    - The Mathlib formula equals n²/4 in ℕ for all n -/
theorem turanHypergraph_graph_le (n : ℕ) :
    turanHypergraph n 2 ≤ n ^ 2 / 4 := by
  -- The Turán number is a supremum; show every member ≤ n²/4
  unfold turanHypergraph
  apply csSup_le
  · -- Nonempty: the empty hypergraph has 0 edges
    refine ⟨0, ⟨⟨∅, fun _ h => absurd h (Finset.not_mem_empty _)⟩, ?_, rfl⟩⟩
    intro S hS hc
    have ⟨e, he⟩ : (completeClique 2 S).Nonempty := by
      rw [← Finset.card_pos, completeClique_card, hS]; norm_num
    exact absurd (hc he) (Finset.not_mem_empty _)
  · -- For each clique-free H, show H.edges.card ≤ n²/4
    rintro m ⟨H, hcf, rfl⟩
    -- Bridge: build a SimpleGraph with the same edge structure
    let G : SimpleGraph (Fin n) where
      Adj v w := ({v, w} : Finset (Fin n)) ∈ H.edges
      symm := fun h => by rwa [Finset.pair_comm]
      loopless v h := by have := H.uniform _ h; simp at this
    haveI : DecidableRel G.Adj := fun v w => Finset.decidableMem _ _
    -- G is triangle-free (CliqueFree 3)
    have hcf3 : G.CliqueFree 3 := by
      intro t ⟨hclique, hcard⟩
      apply hcf t hcard
      intro e he
      rw [completeClique_eq_powersetCard, Finset.mem_powersetCard] at he
      obtain ⟨hsub, hcard_e⟩ := he
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard_e
      exact hclique (hsub (Finset.mem_insert_self a _))
        (hsub (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self b)))) hab
    -- H.edges embeds into G.edgeFinset via Sym2.toFinset
    have h_sub : H.edges ⊆ G.edgeFinset.image Sym2.toFinset := by
      intro e he
      obtain ⟨v, w, _, rfl⟩ := Finset.card_eq_two.mp (H.uniform e he)
      exact Finset.mem_image.mpr ⟨s(v, w),
        SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_edgeSet.mpr he),
        Sym2.toFinset_mk_eq⟩
    -- Chain: |H.edges| ≤ |image| ≤ |G.edgeFinset| ≤ n²/4
    calc H.edges.card
        ≤ (G.edgeFinset.image Sym2.toFinset).card := Finset.card_le_card h_sub
      _ ≤ G.edgeFinset.card := Finset.card_image_le
      _ ≤ n ^ 2 / 4 := by
          -- Apply Mathlib's Turán bound for triangle-free graphs
          have hb := hcf3.card_edgeFinset_le
          simp only [Fintype.card_fin] at hb
          exact le_trans hb (by
            rcases Nat.mod_two_eq_zero_or_one n with h | h
            · simp [h]
            · simp [h, Nat.choose]
              exact Nat.div_le_div_right (Nat.sub_le _ _))

/-- **Turán's theorem for graphs**: the 2-uniform Turán number equals ⌊n²/4⌋.
    Proved by the bipartite lower bound and Mathlib's SimpleGraph upper bound. -/
theorem turan_graph (n : ℕ) :
    turanHypergraph n 2 = n ^ 2 / 4 :=
  le_antisymm (turanHypergraph_graph_le n) (turanHypergraph_graph_ge n)

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
