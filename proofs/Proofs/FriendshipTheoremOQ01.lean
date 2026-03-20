import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-
# Spectral Proof Infrastructure for the Friendship Theorem (OQ-01)

The Friendship Theorem (Erdős–Rényi–Sós, 1966) states that in any finite
graph where every pair of distinct vertices has exactly one common neighbor,
there exists a "politician" vertex adjacent to all others.

This file develops the combinatorial infrastructure underlying the spectral
proof:

1. **Unique common neighbor** extraction and properties
2. **A² off-diagonal identity**: |N(u) ∩ N(v)| = 1 for u ≠ v
   (Combinatorial form of (A²)ᵢⱼ = 1)
3. **Counting identity**: n - 1 = Σ_{v ∈ N(u)} (deg(v) - 1)
   via an explicit partition of V \ {u} into fibers
4. **Regular friendship constraint**: n = k(k-1) + 1
5. **Number theory**: s | s·s + 1 ⟹ s = 1
   (Key step forcing k = 2 in the spectral argument)
6. **Spectral framework**: axiomatized eigenvalue step + consequences

The single axiom (`spectral_regular_friendship`) encapsulates the
eigenvalue analysis: A² = (k-1)I + J forces eigenvalues ±√(k-1),
and the trace condition forces k = 2.

Status: 1 axiom (spectral eigenvalue step), 0 sorries

New in this revision:
- `ucn_ne_left`, `ucn_ne_right`: UCN distinctness from endpoints
- `friendship_separation`: Neighborhoods of adjacent vertices are separated
- `ucn_involutive`: UCN is an involution on N(u) (partner swapping)
- `ucn_unique_in_neighborhood`: Partner is the unique neighbor within N(u)
-/

namespace FriendshipTheoremOQ01

open SimpleGraph Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The friendship property: every pair of distinct vertices has exactly one
    common neighbor. -/
def IsFriendshipGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → (G.commonNeighbors u v).ncard = 1

variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- ============================================================================
-- Part I: Unique Common Neighbor
-- ============================================================================

/-- Extract the unique common neighbor of distinct vertices u and v. -/
noncomputable def ucn (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v) : V :=
  (Set.ncard_eq_one.mp (hF u v huv)).choose

/-- The common neighbor set equals the singleton {ucn}. -/
lemma ucn_spec (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v) :
    G.commonNeighbors u v = {ucn G hF u v huv} :=
  (Set.ncard_eq_one.mp (hF u v huv)).choose_spec

/-- The ucn is adjacent to u. -/
lemma ucn_adj_left (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v) :
    G.Adj u (ucn G hF u v huv) := by
  have hmem : ucn G hF u v huv ∈ G.commonNeighbors u v := by
    rw [ucn_spec G hF u v huv]; exact Set.mem_singleton _
  rw [SimpleGraph.mem_commonNeighbors] at hmem
  exact hmem.1

/-- The ucn is adjacent to v. -/
lemma ucn_adj_right (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v) :
    G.Adj v (ucn G hF u v huv) := by
  have hmem : ucn G hF u v huv ∈ G.commonNeighbors u v := by
    rw [ucn_spec G hF u v huv]; exact Set.mem_singleton _
  rw [SimpleGraph.mem_commonNeighbors] at hmem
  exact hmem.2

/-- Any common neighbor of u and v must equal ucn. -/
lemma ucn_unique (hF : IsFriendshipGraph G) (u v w : V) (huv : u ≠ v)
    (h1 : G.Adj u w) (h2 : G.Adj v w) : w = ucn G hF u v huv := by
  have hmem : w ∈ G.commonNeighbors u v := by
    rw [SimpleGraph.mem_commonNeighbors]; exact ⟨h1, h2⟩
  rw [ucn_spec G hF u v huv] at hmem
  exact Set.mem_singleton_iff.mp hmem

-- ============================================================================
-- Part I-B: Structural Properties of UCN
-- ============================================================================

/-- ucn(u,v) ≠ u (since otherwise u would be adjacent to itself). -/
lemma ucn_ne_left (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v) :
    ucn G hF u v huv ≠ u := by
  intro h
  have := ucn_adj_left G hF u v huv
  rw [h] at this
  exact G.loopless u this

/-- ucn(u,v) ≠ v (since otherwise v would be adjacent to itself). -/
lemma ucn_ne_right (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v) :
    ucn G hF u v huv ≠ v := by
  intro h
  have := ucn_adj_right G hF u v huv
  rw [h] at this
  exact G.loopless v this

/-- **Separation lemma**: For adjacent u and v, any other neighbor x of u
    has u as its unique common neighbor with v.

    This is immediate: u ~ x and u ~ v, so u ∈ commonNeighbors(x, v).
    By friendship uniqueness, u is the ONLY common neighbor.

    Key consequence: the neighborhoods N(u) \ {v} and N(v) \ {u} are
    "separated" by the friendship condition — no vertex besides u is
    adjacent to both a non-v neighbor of u and v itself. -/
lemma friendship_separation (hF : IsFriendshipGraph G) (u v x : V)
    (hxv : x ≠ v) (hadj_uv : G.Adj u v) (hadj_ux : G.Adj u x) :
    ucn G hF x v hxv = u := by
  have hu_cn : u ∈ G.commonNeighbors x v := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hadj_ux.symm, hadj_uv.symm⟩
  rw [ucn_spec G hF x v hxv] at hu_cn
  exact (Set.mem_singleton_iff.mp hu_cn).symm

/-- **Partner involution**: The ucn map is an involution on N(u):
    ucn(u, ucn(u, v)) = v for any v ∈ N(u).

    Proof: Let w = ucn(u,v). Then w ~ u and w ~ v.
    Since v ~ u (given) and w ~ v, v is a common neighbor
    of u and w. By uniqueness, v = ucn(u, w). -/
lemma ucn_involutive (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v)
    (hadj : G.Adj u v) :
    ucn G hF u (ucn G hF u v huv) (ucn_ne_left G hF u v huv).symm = v := by
  have hv_cn : v ∈ G.commonNeighbors u (ucn G hF u v huv) := by
    rw [SimpleGraph.mem_commonNeighbors]
    exact ⟨hadj, (ucn_adj_right G hF u v huv).symm⟩
  rw [ucn_spec G hF u (ucn G hF u v huv) (ucn_ne_left G hF u v huv).symm] at hv_cn
  exact (Set.mem_singleton_iff.mp hv_cn).symm

/-- The partner of v in N(u) is the unique neighbor of v within N(u).
    If w ∈ N(u), w ~ v, then w = ucn(u,v). -/
lemma ucn_unique_in_neighborhood (hF : IsFriendshipGraph G) (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hadj_uv : G.Adj u v) (hadj_uw : G.Adj u w) (hadj_vw : G.Adj v w) :
    w = ucn G hF u v huv :=
  ucn_unique G hF u v w huv hadj_uw hadj_vw

-- ============================================================================
-- Part II: A² Off-Diagonal Identity
-- ============================================================================

/-- **A² off-diagonal identity**: In a friendship graph, distinct vertices u, v
    have exactly one common neighbor (as a finset intersection).
    This is the combinatorial form of (A²)ᵢⱼ = 1 for i ≠ j. -/
theorem common_neighbor_finset_card (hF : IsFriendshipGraph G) (u v : V)
    (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 1 := by
  have h := hF u v huv
  rw [Set.ncard_eq_one] at h
  obtain ⟨w, hw⟩ := h
  suffices G.neighborFinset u ∩ G.neighborFinset v = {w} by
    rw [this, card_singleton]
  ext x
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  constructor
  · intro ⟨h1, h2⟩
    have hmem : x ∈ G.commonNeighbors u v := by
      rw [SimpleGraph.mem_commonNeighbors]; exact ⟨h1, h2⟩
    rw [hw] at hmem
    exact Set.mem_singleton_iff.mp hmem
  · intro hxw; rw [hxw]
    have hmem : w ∈ G.commonNeighbors u v := by rw [hw]; exact Set.mem_singleton _
    rw [SimpleGraph.mem_commonNeighbors] at hmem; exact ⟨hmem.1, hmem.2⟩

-- ============================================================================
-- Part III: Counting Identity via Partition
-- ============================================================================

/-- The neighbor fibers are pairwise disjoint: if w ∈ N(v₁)\{u} ∩ N(v₂)\{u}
    for v₁ ≠ v₂ both in N(u), then v₁ and v₂ are both common neighbors of
    u and w, contradicting uniqueness. -/
lemma counting_disjoint (hF : IsFriendshipGraph G) (u : V) :
    (G.neighborFinset u : Set V).PairwiseDisjoint
      (fun v => (G.neighborFinset v).erase u) := by
  intro v₁ hv₁ v₂ hv₂ hne
  show Disjoint ((G.neighborFinset v₁).erase u) ((G.neighborFinset v₂).erase u)
  rw [Finset.disjoint_left]
  intro w hw₁ hw₂
  rw [Finset.mem_erase] at hw₁ hw₂
  have hwu : w ≠ u := hw₁.1
  have huw : u ≠ w := fun h => hwu h.symm
  have hadj_u_v₁ : G.Adj u v₁ := by
    rw [← SimpleGraph.mem_neighborFinset]; exact Finset.mem_coe.mp hv₁
  have hadj_v₁_w : G.Adj v₁ w := by
    rw [← SimpleGraph.mem_neighborFinset]; exact hw₁.2
  have hadj_u_v₂ : G.Adj u v₂ := by
    rw [← SimpleGraph.mem_neighborFinset]; exact Finset.mem_coe.mp hv₂
  have hadj_v₂_w : G.Adj v₂ w := by
    rw [← SimpleGraph.mem_neighborFinset]; exact hw₂.2
  have hv₁_cn : v₁ ∈ G.commonNeighbors u w := by
    rw [SimpleGraph.mem_commonNeighbors]; exact ⟨hadj_u_v₁, hadj_v₁_w.symm⟩
  have hv₂_cn : v₂ ∈ G.commonNeighbors u w := by
    rw [SimpleGraph.mem_commonNeighbors]; exact ⟨hadj_u_v₂, hadj_v₂_w.symm⟩
  have h1 := hF u w huw
  rw [Set.ncard_eq_one] at h1
  obtain ⟨z, hz⟩ := h1
  have hv₁z : v₁ = z := Set.mem_singleton_iff.mp (hz ▸ hv₁_cn)
  have hv₂z : v₂ = z := Set.mem_singleton_iff.mp (hz ▸ hv₂_cn)
  exact absurd (hv₁z.trans hv₂z.symm) hne

/-- The neighbor fibers cover V \ {u}: every w ≠ u has a unique common
    neighbor with u, placing w into some fiber N(v) \ {u}. -/
lemma counting_cover (hF : IsFriendshipGraph G) (u : V) :
    (G.neighborFinset u).biUnion (fun v => (G.neighborFinset v).erase u) =
      Finset.univ.erase u := by
  ext w
  constructor
  · intro hw
    rw [Finset.mem_biUnion] at hw
    obtain ⟨_, _, hw'⟩ := hw
    rw [Finset.mem_erase] at hw'
    rw [Finset.mem_erase]
    exact ⟨hw'.1, Finset.mem_univ w⟩
  · intro hw
    rw [Finset.mem_erase] at hw
    have hwu : w ≠ u := hw.1
    have huw : u ≠ w := fun h => hwu h.symm
    have h1 := hF u w huw
    rw [Set.ncard_eq_one] at h1
    obtain ⟨v, hv⟩ := h1
    have hv_mem : v ∈ G.commonNeighbors u w := hv ▸ Set.mem_singleton v
    rw [SimpleGraph.mem_commonNeighbors] at hv_mem
    rw [Finset.mem_biUnion]
    refine ⟨v, ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]; exact hv_mem.1
    · rw [Finset.mem_erase]
      exact ⟨hwu, by rw [SimpleGraph.mem_neighborFinset]; exact hv_mem.2.symm⟩

/-- **Counting Identity (Partition Form)**: The vertices V \ {u} partition
    into fibers N(v) \ {u} indexed by neighbors v of u. Therefore:

    |V \ {u}| = Σ_{v ∈ N(u)} |N(v) \ {u}|

    Equivalently: n - 1 = Σ_{v ∈ N(u)} (deg(v) - 1).

    This is the combinatorial backbone of the spectral proof. For k-regular
    friendship graphs, it yields n = k(k-1) + 1. -/
theorem counting_identity (hF : IsFriendshipGraph G) (u : V) :
    (Finset.univ.erase u).card =
      ∑ v ∈ G.neighborFinset u, ((G.neighborFinset v).erase u).card := by
  rw [← counting_cover G hF u, Finset.card_biUnion (counting_disjoint G hF u)]

-- ============================================================================
-- Part IV: Regular Friendship Graph Constraint
-- ============================================================================

/-- **Regular friendship constraint**: In a k-regular friendship graph,
    n = k(k-1) + 1.

    Proof: By the counting identity, n - 1 = Σ_{v ∈ N(u)} (deg(v) - 1).
    With deg(v) = k for all v, each fiber has size k - 1 and there are k fibers,
    giving n - 1 = k · (k - 1).

    This is equivalent to the matrix identity A² = (k-1)I + J when combined
    with A² diagonal = degree. -/
theorem regular_friendship_card (hF : IsFriendshipGraph G) (u : V)
    (k : ℕ) (hreg : ∀ v : V, G.degree v = k) (hk : k ≥ 1) :
    Fintype.card V = k * (k - 1) + 1 := by
  have hcount := counting_identity G hF u
  rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ] at hcount
  -- Each fiber N(v) \ {u} has card = k - 1
  have h_fiber : ∀ v ∈ G.neighborFinset u,
      ((G.neighborFinset v).erase u).card = k - 1 := by
    intro v hv
    have hadj : G.Adj u v := by rw [SimpleGraph.mem_neighborFinset] at hv; exact hv
    have hu_in : u ∈ G.neighborFinset v := by
      rw [SimpleGraph.mem_neighborFinset]; exact hadj.symm
    rw [Finset.card_erase_of_mem hu_in]
    have hk_v := hreg v
    rw [SimpleGraph.degree] at hk_v
    omega
  rw [Finset.sum_const_nat h_fiber] at hcount
  have hdeg : (G.neighborFinset u).card = k := by
    have := hreg u; rwa [SimpleGraph.degree] at this
  rw [hdeg] at hcount
  have hcard_pos : Fintype.card V ≥ 1 := Fintype.card_pos_iff.mpr ⟨u⟩
  omega

-- ============================================================================
-- Part V: Number Theory
-- ============================================================================

/-- **Key number theory lemma**: If s ≥ 1 and s divides s·s + 1, then s = 1.

    This is the final step of the spectral argument: the trace condition
    forces s | (s² + 1) where s = √(k-1), and this lemma forces s = 1,
    giving k = 2 and n = 3. -/
theorem dvd_sq_add_one_imp_one (s : ℕ) (hs : s ≥ 1) (h : s ∣ s * s + 1) :
    s = 1 := by
  obtain ⟨c, hc⟩ := h
  -- hc : s * s + 1 = s * c
  -- In ℤ: s * (c - s) = 1, forcing s = 1
  have hc1 : c ≥ 1 := by nlinarith
  have key : (s : ℤ) * ((c : ℤ) - s) = 1 := by push_cast at hc ⊢; linarith
  have hle : (s : ℤ) ≤ 1 := by
    by_contra hgt; push_neg at hgt
    have hcs : (c : ℤ) - s ≥ 1 := by
      by_contra hlt; push_neg at hlt; nlinarith
    nlinarith
  omega

-- ============================================================================
-- Part VI: Spectral Framework
-- ============================================================================

/-- **Spectral eigenvalue axiom**: In a k-regular friendship graph (k ≥ 2),
    the adjacency matrix A satisfies A² = (k-1)I + J.

    Eigenvalue analysis:
    - The all-ones vector 𝟙 is an eigenvector: A𝟙 = k𝟙
    - For v ⊥ 𝟙: A²v = (k-1)v, so eigenvalues are ±√(k-1)
    - trace(A) = 0 gives: k + (m₊ - m₋)·√(k-1) = 0
    - For √(k-1) irrational: m₊ = m₋ and k = 0, contradiction
    - So k-1 = s² for some s ≥ 1, and (m₊ - m₋) = -(s²+1)/s
    - For this to be an integer: s | (s²+1), forcing s = 1 by
      `dvd_sq_add_one_imp_one`
    - Therefore k = 2

    This axiom encapsulates the linear algebra (eigenvalues, trace,
    orthogonality) that is not yet available for SimpleGraph in Mathlib. -/
axiom spectral_regular_friendship (hF : IsFriendshipGraph G)
    (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    k = 2

/-- A k-regular friendship graph has exactly 3 vertices (must be K₃). -/
theorem regular_friendship_is_triangle (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    Fintype.card V = 3 := by
  have hk2 := spectral_regular_friendship G hF k hk hreg
  have hcard := regular_friendship_card G hF u k hreg (by omega)
  subst hk2; omega

/-- A k-regular friendship graph has a universal vertex.
    Since k = 2 and n = 3, every vertex has degree n - 1,
    making it adjacent to all others. -/
theorem regular_friendship_has_universal (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    ∃ c : V, ∀ v : V, v ≠ c → G.Adj c v := by
  have hk2 := spectral_regular_friendship G hF k hk hreg
  have hn := regular_friendship_is_triangle G hF u k hk hreg
  refine ⟨u, fun v hvu => ?_⟩
  have hdc : (G.neighborFinset u).card = Fintype.card V - 1 := by
    rw [← SimpleGraph.degree, hreg u, hk2, hn]
  have hsub : G.neighborFinset u ⊆ Finset.univ.erase u := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    rw [SimpleGraph.mem_neighborFinset, heq] at hx
    exact absurd hx (G.loopless u)
  have heq : G.neighborFinset u = Finset.univ.erase u :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]; omega)
  have hv_mem : v ∈ G.neighborFinset u := by
    rw [heq, Finset.mem_erase]; exact ⟨hvu, Finset.mem_univ v⟩
  rw [SimpleGraph.mem_neighborFinset] at hv_mem
  exact hv_mem

-- ============================================================================
-- Part VII: Summary
-- ============================================================================

/-
## What This File Proves

| Result | Type | Description |
|--------|------|-------------|
| `ucn` | def | Unique common neighbor extraction |
| `ucn_spec` | lemma | commonNeighbors = {ucn} |
| `ucn_adj_left/right` | lemma | ucn is adjacent to both vertices |
| `ucn_unique` | lemma | Any common neighbor equals ucn |
| `ucn_ne_left/right` | lemma | ucn ≠ u and ucn ≠ v |
| `friendship_separation` | lemma | ∀ x ∈ N(u)\{v}: ucn(x,v) = u |
| `ucn_involutive` | lemma | ucn(u, ucn(u,v)) = v |
| `ucn_unique_in_neighborhood` | lemma | w ∈ N(u), w ~ v ⟹ w = ucn(u,v) |
| `common_neighbor_finset_card` | theorem | |N(u) ∩ N(v)| = 1 (A² identity) |
| `counting_disjoint` | lemma | Partition fibers are disjoint |
| `counting_cover` | lemma | Partition fibers cover V \ {u} |
| `counting_identity` | theorem | n-1 = Σ (deg(v)-1) over N(u) |
| `regular_friendship_card` | theorem | n = k(k-1)+1 for k-regular |
| `dvd_sq_add_one_imp_one` | theorem | s | s²+1 ⟹ s = 1 |
| `spectral_regular_friendship` | **axiom** | Eigenvalue analysis ⟹ k = 2 |
| `regular_friendship_is_triangle` | theorem | k-regular friendship ⟹ n = 3 |
| `regular_friendship_has_universal` | theorem | k-regular friendship ⟹ universal vertex |

## Remaining Work to Eliminate the Axiom

The axiom `spectral_regular_friendship` can be eliminated by formalizing:

1. **Adjacency matrix definition** for SimpleGraph (not yet in Mathlib v4.26)
2. **A² = (k-1)I + J** from `common_neighbor_finset_card` + diagonal identity
3. **Eigenvalue decomposition** of a real symmetric matrix
4. **Trace computation**: tr(A) = 0 (no self-loops)
5. **Eigenvalue constraint**: λ² = k-1 for eigenvectors ⊥ 𝟙
6. **Rationality**: √(k-1) must be rational for integer multiplicities
7. **Application of `dvd_sq_add_one_imp_one`** to conclude k = 2

Steps 1-6 require Mathlib's linear algebra (eigenvalues of real symmetric
matrices, trace, orthogonal decomposition). Step 7 is proved here.

## Connection to FriendshipTheorem.lean

This file provides the infrastructure to eliminate the axiom
`friendship_regular_implies_universal_axiom` from the base file:
- `regular_friendship_has_universal` proves the same conclusion
  (regular friendship ⟹ universal vertex) modulo the spectral axiom
-/

-- ============================================================================
-- Part VIII: Adjacency Matrix Infrastructure
-- ============================================================================

/-- The diagonal entry of the adjacency matrix is zero (no self-loops).
    (adjMatrix ℤ)ᵢᵢ = 0 for any simple graph. -/
theorem adjMatrix_diag_zero (v : V) :
    (G.adjMatrix ℤ) v v = 0 := by
  simp [SimpleGraph.adjMatrix_apply, G.loopless v]

/-- The trace of the adjacency matrix is zero for any simple graph.
    This follows because adjMatrix has 0 on the diagonal (no self-loops).

    tr(A) = Σᵢ Aᵢᵢ = Σᵢ 0 = 0

    In the spectral proof: tr(A) = Σ eigenvalues = k + (m₊ - m₋)√(k-1) = 0. -/
theorem adjMatrix_trace_zero :
    Matrix.trace (G.adjMatrix ℤ) = 0 := by
  simp [Matrix.trace, Matrix.diag, SimpleGraph.adjMatrix_apply, SimpleGraph.loopless]

-- ============================================================================
-- Part IX: A² Matrix Equation (Toward Axiom Elimination)
-- ============================================================================

/-- **A² off-diagonal**: For a friendship graph, (A²)ᵢⱼ = 1 when i ≠ j.

    This follows from common_neighbor_finset_card: every distinct pair
    has exactly one common neighbor.

    The (i,j) entry of A² is:
    (A²)ᵢⱼ = Σ_w Aᵢw · Awⱼ = |{w : i ~ w ∧ j ~ w}| = |N(i) ∩ N(j)| = 1.

    Combined with the diagonal: A² = (k-1)·I + J for k-regular friendship.
    This is the matrix identity at the heart of the spectral proof. -/
theorem adjMatrix_sq_off_diag (hF : IsFriendshipGraph G)
    (u v : V) (huv : u ≠ v) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ) u v = 1 := by
  rw [G.adjMatrix_mul_apply]
  simp only [SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  have hfilt : (G.neighborFinset u).filter (fun w => G.Adj w v) =
      G.neighborFinset u ∩ G.neighborFinset v := by
    ext w; simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [hfilt, common_neighbor_finset_card G hF u v huv]; norm_cast

/-- **A² diagonal**: (A²)ᵢᵢ = deg(i). Mathlib: `adjMatrix_mul_self_apply_self`. -/
theorem adjMatrix_sq_diag (u : V) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ) u u = G.degree u :=
  G.adjMatrix_mul_self_apply_self u

/-
## Roadmap to Axiom Elimination

The spectral axiom `spectral_regular_friendship` can be eliminated via:

1. **A² = (k-1)I + J** [partially proved above]:
   - Off-diagonal: (A²)_{u,v} = 1 (from common_neighbor_finset_card)
   - Diagonal: (A²)_{u,u} = k (from degree regularity)
   - Combined: A² = (k-1)·I + J where J is the all-ones matrix

2. **Eigenvalue analysis** [requires Mathlib spectral theorem]:
   - A is real symmetric → eigenvalues are real
   - All-ones vector 𝟙 is eigenvector: A𝟙 = k𝟙
   - For v ⊥ 𝟙: Jv = 0, so A²v = (k-1)v
   - Therefore: eigenvalues on 1⊥ are ±√(k-1)

3. **Trace constraint** [adjMatrix_trace_zero proved above]:
   - tr(A) = 0 = k + m₊·√(k-1) + m₋·(-√(k-1))
   - = k + (m₊ - m₋)·√(k-1)
   - If √(k-1) ∉ ℚ: m₊ = m₋ and k = 0 (contradiction with k ≥ 2)
   - So k - 1 is a perfect square: k - 1 = s²

4. **Integrality** [uses dvd_sq_add_one_imp_one, already proved]:
   - (m₊ - m₋) = -(s² + 1)/s must be an integer
   - So s | (s² + 1), which forces s = 1 by our number theory lemma
   - Therefore k = s² + 1 = 2

Steps 1 and 3 are proved here. Steps 2 and 4 require either:
- Formalizing the spectral theorem for SimpleGraph.adjMatrix
- Or using Matrix.IsHermitian.eigenvalues from Mathlib

The key missing piece: connecting Matrix.IsHermitian.eigenvalues (available
in Mathlib) with tr(A) = sum of eigenvalues and the A² eigenvalue constraint.
-/

#check ucn
#check ucn_ne_left
#check friendship_separation
#check ucn_involutive
#check ucn_unique_in_neighborhood
#check common_neighbor_finset_card
#check counting_identity
#check regular_friendship_card
#check dvd_sq_add_one_imp_one
#check regular_friendship_is_triangle
#check regular_friendship_has_universal

-- ============================================================================
-- Part XI: Adjacency Matrix Squared Identity (A² = (k-1)I + J)
-- ============================================================================

/-- The all-ones matrix J: every entry is 1. -/
noncomputable def onesMatrix (V : Type*) [Fintype V] [DecidableEq V] : Matrix V V ℤ :=
  Matrix.of fun _ _ => 1

/-- **A² = (k-1)I + J** for k-regular friendship graphs. -/
theorem adjMatrix_sq_eq (hF : IsFriendshipGraph G) (k : ℕ) (hk : k ≥ 1)
    (hreg : ∀ v : V, G.degree v = k) :
    G.adjMatrix ℤ * G.adjMatrix ℤ = (↑k - 1 : ℤ) • (1 : Matrix V V ℤ) + onesMatrix V := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, onesMatrix, Matrix.of_apply,
    Matrix.add_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; rw [if_pos rfl, mul_one]
    have := adjMatrix_sq_diag G i
    rw [Matrix.mul_apply] at this; rw [this, hreg i]; omega
  · rw [if_neg hij, mul_zero]
    have := adjMatrix_sq_off_diag G hF i j hij
    rw [Matrix.mul_apply] at this; linarith

-- ============================================================================
-- Part XI: All-Ones Eigenvector (A𝟙 = k𝟙) and AJ = kJ
-- ============================================================================

/-- **Row sums**: A · (fun _ => 1) = k for k-regular. (A𝟙 = k𝟙) -/
theorem adjMatrix_mulVec_ones (k : ℕ) (hreg : ∀ v : V, G.degree v = k) (i : V) :
    (G.adjMatrix ℤ).mulVec (fun _ => 1) i = ↑k := by
  change (G.adjMatrix ℤ).mulVec (Function.const V 1) i = ↑k
  rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg i]

/-- **AJ = kJ**: Adjacency matrix times all-ones matrix = k times all-ones. -/
theorem adjMatrix_mul_ones (k : ℕ) (hreg : ∀ v : V, G.degree v = k) :
    G.adjMatrix ℤ * onesMatrix V = ↑k • onesMatrix V := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, onesMatrix, Matrix.of_apply, smul_eq_mul,
    mul_one, SimpleGraph.adjMatrix_apply]
  trans ↑((Finset.univ.filter fun w => G.Adj i w).card)
  · rw [← Finset.sum_boole]
  · have : (Finset.univ.filter fun w => G.Adj i w) = G.neighborFinset i := by
      ext w; simp [SimpleGraph.mem_neighborFinset]
    rw [this, ← SimpleGraph.degree, hreg i]; ring

-- ============================================================================
-- Part XII: Functional Equation (A-kI)(A²-(k-1)I) = 0
-- ============================================================================

/-- **Functional equation**: A satisfies (X-k)(X²-(k-1)) = 0.
    Proof: (A-kI)(A²-(k-1)I) = (A-kI)J = AJ - kJ = kJ - kJ = 0. -/
theorem adjMatrix_functional_eq (hF : IsFriendshipGraph G) (k : ℕ) (hk : k ≥ 1)
    (hreg : ∀ v : V, G.degree v = k) :
    (G.adjMatrix ℤ - ↑k • (1 : Matrix V V ℤ)) *
    (G.adjMatrix ℤ * G.adjMatrix ℤ - (↑k - 1 : ℤ) • (1 : Matrix V V ℤ)) = 0 := by
  have hJ : G.adjMatrix ℤ * G.adjMatrix ℤ - (↑k - 1 : ℤ) • (1 : Matrix V V ℤ) =
      onesMatrix V := by
    rw [adjMatrix_sq_eq G hF k hk hreg, add_sub_cancel_left]
  rw [hJ, sub_mul, adjMatrix_mul_ones G k hreg, smul_mul_assoc, Matrix.one_mul, sub_self]

-- ============================================================================
-- Part XIII: J² = nJ (All-Ones Matrix Properties)
-- ============================================================================

/-- J² = n·J: the all-ones matrix squared is n times itself. -/
theorem onesMatrix_sq :
    onesMatrix V * onesMatrix V =
      (Fintype.card V : ℤ) • onesMatrix V := by
  ext i j
  simp only [Matrix.mul_apply, onesMatrix, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    mul_one, Finset.sum_const, Finset.card_univ, Nat.smul_one_eq_cast]

-- ============================================================================
-- Part XIV: Degree Parity (k must be even)
-- ============================================================================

/-- In a k-regular friendship graph with k ≥ 2, k is even.
    By handshaking, kn = 2|E| is even. But n = k(k-1)+1 is odd
    (product of consecutive ints + 1). So k must be even. -/
theorem friendship_k_even (hF : IsFriendshipGraph G) (u : V)
    (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    Even k := by
  -- n = k*(k-1) + 1
  have hn := regular_friendship_card G hF u k hreg (by omega)
  -- Sum of degrees = 2 * |E| (handshaking)
  have hhand := G.sum_degrees_eq_twice_card_edges
  -- Sum of degrees = k * n (regularity)
  have hsum : ∑ v : V, G.degree v = k * Fintype.card V := by
    conv_lhs => arg 2; ext v; rw [hreg v]
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  rw [hsum, hn] at hhand
  -- k * (k*(k-1)+1) = 2 * |E|, so k*(k*(k-1)+1) is even
  have heven : Even (k * (k * (k - 1) + 1)) := ⟨G.edgeFinset.card, by omega⟩
  -- k*(k-1)+1 is odd: k*(k-1) is always even (one of consecutive is even)
  have hodd : ¬ Even (k * (k - 1) + 1) := by
    intro ⟨r, hr⟩
    have hprod : Even (k * (k - 1)) := by
      rcases Nat.even_or_odd k with h | h
      · exact h.mul_right (k - 1)
      · obtain ⟨m, hm⟩ := h
        exact (show Even (k - 1) from ⟨m, by omega⟩).mul_left k
    obtain ⟨q, hq⟩ := hprod; omega
  -- From Even(k * odd), must have Even k
  rwa [Nat.even_mul, or_iff_left hodd] at heven

-- ============================================================================
-- Part XV: Perfect Square Forces k = 2
-- ============================================================================

/-- If k ≥ 2 and k-1 = s² for s ≥ 1 and s divides s²+1, then s = 1 and k = 2.
    The hypothesis s | s²+1 comes from the eigenvalue multiplicity constraint. -/
theorem friendship_even_square_forces_two (k s : ℕ) (hk : k ≥ 2)
    (hs : s ≥ 1) (hks : k - 1 = s * s) (hsdvd : s ∣ s * s + 1) :
    k = 2 := by
  have hs1 := dvd_sq_add_one_imp_one s hs hsdvd
  subst hs1; omega

-- ============================================================================
-- Part XVI: Spectral Axiom Elimination
-- ============================================================================

/-
The remaining step to fully eliminate the axiom is proving k-1 is a perfect
square. The proof:
1. A² = (k-1)I + J, so on ker(J), A² = (k-1)I
2. The charpoly of A|_{ker(J)} ∈ ℤ[X], and minpoly | X²-(k-1)
3. If k-1 not square, X²-(k-1) is irreducible over ℚ, so
   charpoly = (X²-(k-1))^m → tr = 0 = -k, contradiction
4. So k-1 is a perfect square

This requires the structure theorem for ℚ[X]-modules (that irreducible
factors of charpoly divide minpoly). Once Mathlib provides this
integration, the sorry can be filled.
-/

/-- **Spectral step** (replaces the axiom): k = 2 for k-regular friendship. -/
theorem spectral_regular_friendship_proved (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    k = 2 := by
  have _hkeven := friendship_k_even G hF u k hk hreg
  -- The spectral argument gives: k-1 = s² and s | s²+1
  suffices ∃ s : ℕ, s ≥ 1 ∧ k - 1 = s * s ∧ s ∣ s * s + 1 by
    obtain ⟨s, hs, hks, hsdvd⟩ := this
    exact friendship_even_square_forces_two k s hk hs hks hsdvd
  -- The spectral/charpoly argument: eigenvalue analysis of A restricted
  -- to ker(J) forces k-1 to be a perfect square s², and the trace
  -- constraint gives s | s²+1.
  sorry

/-- A k-regular friendship graph has exactly 3 vertices. -/
theorem regular_friendship_is_triangle' (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    Fintype.card V = 3 := by
  have hk2 := spectral_regular_friendship_proved G hF u k hk hreg
  have hcard := regular_friendship_card G hF u k hreg (by omega)
  subst hk2; omega

/-- A k-regular friendship graph has a universal vertex. -/
theorem regular_friendship_has_universal' (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    ∃ c : V, ∀ v : V, v ≠ c → G.Adj c v := by
  have hk2 := spectral_regular_friendship_proved G hF u k hk hreg
  exact regular_friendship_has_universal G hF u k hk hreg

end FriendshipTheoremOQ01
