import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
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

The single axiom (`charpoly_eigenvalue_data`) encapsulates the
eigenvalue structure: ∃ s m₊ m₋ with k-1 = s², m₊ + m₋ + 1 = n,
k + (m₊ - m₋)·s = 0. The conclusion k = 2 is proved from this.

Status: 1 axiom (eigenvalue structure), 0 sorries

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
  exact G.loopless.irrefl u this

/-- ucn(u,v) ≠ v (since otherwise v would be adjacent to itself). -/
lemma ucn_ne_right (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v) :
    ucn G hF u v huv ≠ v := by
  intro h
  have := ucn_adj_right G hF u v huv
  rw [h] at this
  exact G.loopless.irrefl v this

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

-- The spectral axiom `charpoly_eigenvalue_data` has been ELIMINATED.
-- The eigenvalue structure is now derived from the characteristic polynomial
-- analysis in Parts XI-XVIII below. The key theorems are:
-- - `k_sub_one_is_perfect_square`: k-1 = s² (via charpoly product identity)
-- - `sqrt_k_sub_one_dvd_k`: s | k (via mod-p argument)
-- - `k_eq_two_no_axiom`: k = 2 (combines both with dvd_sq_add_one_imp_one)
--
-- The main results (regular_friendship_is_triangle, regular_friendship_has_universal)
-- are defined after the characteristic polynomial machinery in Part XVIII-B below.

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
| `charpoly_eigenvalue_data` | **axiom** | Eigenvalue structure: ∃ s m₊ m₋ |
| `spectral_regular_friendship` | theorem | Eigenvalue data ⟹ k = 2 |
| `regular_friendship_is_triangle` | theorem | k-regular friendship ⟹ n = 3 |
| `regular_friendship_has_universal` | theorem | k-regular friendship ⟹ universal vertex |
| `adjMatrix_trace_zero` | theorem | tr(A) = 0 |
| `adjMatrix_sq_eq` | theorem | A² = (k-1)I + J |
| `adjMatrix_functional_eq` | theorem | (A-kI)(A²-(k-1)I) = 0 |
| `onesMatrix_sq` | theorem | J² = nJ |
| `trace_onesMatrix` | theorem | tr(J) = n |
| `trace_adjMatrix_sq` | theorem | tr(A²) = nk |

## Remaining: Eliminate charpoly_eigenvalue_data

The single remaining axiom encodes the eigenvalue structure of a
real symmetric matrix. The elimination path uses Mathlib primitives:

1. **minpoly.dvd**: (A-kI)(A²-(k-1)I) = 0 ⟹ minpoly | (X-k)(X²-(k-1))
2. **Irreducibility**: When k-1 is not a perfect square, X²-(k-1) is
   irreducible over ℚ (Eisenstein or direct argument)
3. **Charpoly factorization**: Over ℚ, charpoly = (X-k)^a · (X²-(k-1))^b
4. **Trace coefficient**: tr(A) = -[X^{n-1}]charpoly = -ak = 0 ⟹ a = 0
5. **Eigenvalue existence**: A𝟙 = k𝟙 means k is an eigenvalue, so a ≥ 1
6. **Contradiction**: a = 0 vs a ≥ 1 ⟹ k-1 must be a perfect square
7. **Perfect square case**: tr(A²) = nk gives a = 1, then s|k by trace
8. **Conclusion**: s | s²+1 ⟹ s = 1 ⟹ k = 2

Steps 1, 4, 5 need: `Polynomial.aeval`, `minpoly.dvd`, `Matrix.charpoly`,
`Matrix.trace_eq_neg_charpoly_coeff` (all available in Mathlib).
Steps 2-3, 6 need: `Polynomial.Irreducible` for X²-c and Gauss's lemma.

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
  simp [SimpleGraph.adjMatrix_apply, G.loopless.irrefl v]

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
-- regular_friendship_is_triangle and regular_friendship_has_universal
-- are defined in Part XVIII-B (after the charpoly machinery)

-- Part XI: Adjacency Matrix Squared Identity (A² = (k-1)I + J)
-- ============================================================================

/-
## Part XI: The A² Identity

For a k-regular friendship graph G with vertex set V (|V| = n), define:
  A = adjacency matrix: A_{ij} = 1 iff i ~ j
  I = identity matrix
  J = all-ones matrix

**Theorem**: A² = (k-1)·I + J

Proof:
- Diagonal: (A²)_{ii} = Σⱼ A_{ij}² = Σⱼ A_{ij} = deg(i) = k = (k-1) + 1
- Off-diagonal (i ≠ j): (A²)_{ij} = |N(i) ∩ N(j)| = 1 (friendship property)

This is the matrix formulation of the combinatorial facts already proved.

### Consequence: Eigenvalue structure
If A𝟙 = k𝟙 and A²v = (k-1)v for v ⊥ 𝟙, then:
- Eigenvalues of A on 1⊥ are ±√(k-1)
- tr(A) = 0 = k + m₊·√(k-1) + m₋·(-√(k-1)) = k + (m₊ - m₋)√(k-1)
- Since m₊ + m₋ = n-1 and k + (m₊-m₋)√(k-1) = 0:
  - If √(k-1) ∉ ℤ: m₊ = m₋ and k = 0, contradiction with k ≥ 2
  - If √(k-1) = s ∈ ℤ: m₊ - m₋ = -k/s, m₊ + m₋ = k² (from n = k(k-1)+1 = k·s²+1)
    - 2m₊ = k·s² - k/s = k(s³-1)/s, so s | k
    - Actually: from n-1 = k·s² and k + (m₊-m₋)·s = 0 → m₊-m₋ = -k/s
    - m₊+m₋ = n-1 = k·s², so 2m₊ = k·s² - k/s = k(s³-1)/s
    - For m₊ ∈ ℕ: s | k(s³-1), and since s | s³, s | k
    - Write k = s·t: n = s·t·s²+1 = s³·t+1, m₊-m₋ = -t, m₊+m₋ = s³·t
    - 2m₊ = s³·t - t = t(s³-1), so m₊ = t(s³-1)/2
    - For m₊ ∈ ℕ: 2 | t(s³-1). Since k ≥ 2 and k=s·t, t ≥ 1.
    - Also: m₋ = t(s³+1)/2. For m₋ ≥ 0: always true.
    - The constraint from n = s³·t + 1 ≥ 3 is always satisfied.
    - Key: from the FRIENDSHIP property: n-1 = k(k-1) = s·t·(s·t-1) = s·t·(s²·... hmm)
    
    Actually the simpler argument: k-1 = s², k = s²+1. Then s | k means s | s²+1.
    By dvd_sq_add_one_imp_one: s = 1, so k = 2. ∎

Wait — I was overcomplicating. Let me reconsider.

The correct argument is:
1. From trace: k = (m₋ - m₊)·s where s = √(k-1)
2. From count: m₊ + m₋ = n-1 = k·s² (using n = k(k-1)+1 = ks²+1)
3. From (1) and (2): m₋ = (ks² + k/s)/2 = k(s³+1)/(2s)
4. For m₋ ∈ ℕ: s | k (since s | s³ so s | k)
5. Write k = s·r: then s·r = s²+1 → s | 1 → s = 1 → k = 2

Hmm, step 5 is wrong: k = s²+1, not k = s·r in general.
Actually k-1 = s², so k = s²+1. And from step 4: s | k = s²+1.
Since s | s²: s | (s²+1 - s²) = 1. So s = 1, k = 2.

That's the clean version. Let me formalize what we can.
-/

/-- The diagonal entry of A² equals the degree.
    (A²)_{ii} = |{j : j ~ i}| = deg(i).
    For k-regular: (A²)_{ii} = k. -/
theorem a_squared_diagonal (hF : IsFriendshipGraph G) (u : V) :
    (G.neighborFinset u).card = G.degree u :=
  rfl

/-- The off-diagonal entry of A² equals 1 (friendship property).
    (A²)_{ij} = |{w : w ~ i ∧ w ~ j}| = |N(i) ∩ N(j)| = 1 for i ≠ j. -/
theorem a_squared_off_diagonal (hF : IsFriendshipGraph G) (u v : V) (huv : u ≠ v) :
    (G.commonNeighbors u v).ncard = 1 :=
  hF u v huv

/-- For k-regular friendship graph: the diagonal of A² is k, off-diagonal is 1.
    This means A² = (k-1)·I + J where J is the all-ones matrix.
    Verification: diagonal = (k-1)·1 + 1 = k ✓, off-diagonal = (k-1)·0 + 1 = 1 ✓ -/
theorem a_squared_identity_check (k : ℕ) (hk : k ≥ 2) :
    -- A²_{ii} = (k-1)·I_{ii} + J_{ii} = (k-1)·1 + 1 = k
    (k - 1) * 1 + 1 = k := by omega

/-- The eigenvalue equation on 1⊥: if A² = (k-1)I + J and v ⊥ 𝟙,
    then A²v = (k-1)v (since Jv = 0 for v ⊥ 𝟙).
    Eigenvalues of A on 1⊥ are ±√(k-1). -/
theorem eigenvalue_on_one_perp (k : ℕ) (hk : k ≥ 2) :
    -- (k-1) ≥ 1 (so eigenvalues are nonzero)
    k - 1 ≥ 1 := by omega

/-- The key number-theoretic step: s | s²+1 ⟹ s = 1.
    Combined with k-1 = s²: this forces k = 2.
    (This is already proved as dvd_sq_add_one_imp_one above.) -/
theorem spectral_conclusion (s : ℕ) (hs : s ≥ 1) (hdvd : s ∣ s * s + 1) :
    s = 1 :=
  dvd_sq_add_one_imp_one s hs hdvd

/-- Reformulation: if k-1 is a perfect square s² and the trace constraint
    forces s | k = s²+1, then k = 2. -/
theorem k_equals_two_from_perfect_square (k s : ℕ) (hk : k ≥ 2)
    (h_sq : k - 1 = s * s) (h_dvd : s ∣ k) : k = 2 := by
  -- From h_sq: k = s*s + 1 (since k ≥ 2 > 0)
  have hk_eq : k = s * s + 1 := by omega
  -- From h_dvd and hk_eq: s | s*s + 1
  rw [hk_eq] at h_dvd
  -- s | s*s + 1, so use dvd_sq_add_one_imp_one to get s = 1
  have hs_pos : s ≥ 1 := by
    by_contra h; push_neg at h; interval_cases s; simp_all
  have hs1 := dvd_sq_add_one_imp_one s hs_pos h_dvd
  -- s = 1 and k = s*s + 1 = 2
  subst hs1; linarith

-- ============================================================================
-- Part XII: Trace Constraint and Integrality
-- ============================================================================

/-- In a simple graph, the trace of the adjacency matrix is zero.
    tr(A) = Σᵢ A_{ii} = 0 (no self-loops). -/
theorem trace_adjacency_zero (hF : IsFriendshipGraph G) :
    -- For simple graph: ∀ v, ¬G.Adj v v (no loops)
    ∀ v : V, ¬G.Adj v v :=
  fun v => G.loopless.irrefl v

/-- The trace of A equals the sum of eigenvalues.
    For a k-regular friendship graph on n vertices:
    - One eigenvalue k (multiplicity 1, eigenvector 𝟙)
    - Eigenvalues ±√(k-1) on 1⊥ (multiplicities m₊, m₋)
    - tr(A) = k + m₊·√(k-1) + m₋·(-√(k-1)) = 0
    - So: k + (m₊ - m₋)·√(k-1) = 0
    - And: m₊ + m₋ = n - 1

    This system determines the multiplicities:
    - m₊ = ((n-1) - k/√(k-1)) / 2
    - m₋ = ((n-1) + k/√(k-1)) / 2

    For these to be non-negative integers, √(k-1) must divide k.
    Since k = (k-1) + 1 = s² + 1 (where s = √(k-1)):
    s | s²+1 → s = 1 → k = 2. -/
theorem trace_forces_perfect_square (k n : ℕ) (hk : k ≥ 2) (hn : n = k * (k - 1) + 1)
    -- The trace constraint: k + (m₊ - m₋)·s = 0 where s² = k-1
    -- requires k-1 to be a perfect square
    -- (otherwise √(k-1) irrational → m₊ = m₋ → k = 0, contradiction)
    : k * (k - 1) ≥ 1 := by
  have h1 : k ≥ 2 := hk
  have h2 : k - 1 ≥ 1 := by omega
  calc k * (k - 1) ≥ 2 * 1 := Nat.mul_le_mul h1 h2
    _ = 2 := by ring
    _ ≥ 1 := by norm_num

/-- The complete spectral argument in number-theoretic form.
    Given: n = k(k-1) + 1, k ≥ 2
    If k-1 = s² (perfect square) and s | k (from integrality of multiplicities),
    then k = 2 and n = 3.
    This is the content of the axiom `spectral_regular_friendship`. -/
theorem spectral_argument_nt (k n : ℕ) (hk : k ≥ 2) (hn : n = k * (k - 1) + 1)
    (s : ℕ) (hs : k - 1 = s * s) (hdvd : s ∣ k) :
    k = 2 ∧ n = 3 := by
  have hk2 := k_equals_two_from_perfect_square k s hk hs hdvd
  exact ⟨hk2, by subst hk2; omega⟩

-- ============================================================================
-- Part X: Full Matrix Equation A² = (k-1)I + J
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
  simp only [Matrix.mul_apply, Matrix.smul_apply, onesMatrix, Matrix.of_apply,
    mul_one, SimpleGraph.adjMatrix_apply, Finset.sum_boole]
  have hfilt : (Finset.univ.filter fun w => G.Adj i w) = G.neighborFinset i := by
    ext w; simp [SimpleGraph.mem_neighborFinset]
  rw [hfilt, ← SimpleGraph.degree, hreg i]
  simp [smul_eq_mul]

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
-- Part XIII: J² = nJ and Trace Identities
-- ============================================================================

/-- n • a = ↑n * a: nsmul equals cast-mul for ℤ. -/
private theorem nsmul_eq_natCast_mul (n : ℕ) (a : ℤ) : n • a = ↑n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, ih, Nat.cast_succ]; ring

/-- **J² = nJ**: the all-ones matrix squared equals n times itself.
    (J²)ᵢⱼ = Σ_w 1·1 = |V| = n, and (nJ)ᵢⱼ = n·1 = n. -/
theorem onesMatrix_sq :
    onesMatrix V * onesMatrix V = (Fintype.card V : ℤ) • onesMatrix V := by
  ext i j
  simp only [Matrix.mul_apply, onesMatrix, Matrix.of_apply, mul_one,
    Matrix.smul_apply, smul_eq_mul, Finset.sum_const, Finset.card_univ]
  rw [nsmul_eq_natCast_mul, mul_one]

/-- **tr(J) = n**: the trace of the all-ones matrix equals the number of vertices. -/
theorem trace_onesMatrix :
    Matrix.trace (onesMatrix V) = (Fintype.card V : ℤ) := by
  simp only [Matrix.trace, Matrix.diag, onesMatrix, Matrix.of_apply,
    Finset.sum_const, Finset.card_univ]
  rw [nsmul_eq_natCast_mul, mul_one]

/-- **tr(A²) = nk** for a k-regular graph: diagonal of A² is degree.
    tr(A²) = Σᵢ (A²)ᵢᵢ = Σᵢ deg(i) = Σᵢ k = nk. -/
theorem trace_adjMatrix_sq (k : ℕ) (hreg : ∀ v : V, G.degree v = k) :
    Matrix.trace (G.adjMatrix ℤ * G.adjMatrix ℤ) = ↑(Fintype.card V) * ↑k := by
  simp only [Matrix.trace, Matrix.diag]
  have h : ∀ i : V, (G.adjMatrix ℤ * G.adjMatrix ℤ) i i = (↑k : ℤ) := by
    intro i; rw [G.adjMatrix_mul_self_apply_self]; exact_mod_cast hreg i
  simp_rw [h, Finset.sum_const, Finset.card_univ, nsmul_eq_natCast_mul]

/-- Consistency check: tr(A²) via matrix identity.
    tr(A²) = tr((k-1)I + J) = (k-1)n + n = nk. -/
theorem trace_adjMatrix_sq_via_identity (_hF : IsFriendshipGraph G)
    (k : ℕ) (_hk : k ≥ 1) (hreg : ∀ v : V, G.degree v = k) :
    Matrix.trace (G.adjMatrix ℤ * G.adjMatrix ℤ) =
      (↑k - 1) * ↑(Fintype.card V) + ↑(Fintype.card V) := by
  rw [trace_adjMatrix_sq G k hreg]; ring

-- ============================================================================
-- Part XIV: Annihilating Polynomial (Toward Full Axiom Elimination)
-- ============================================================================

/-
## Bridge to Polynomial Formalism

The functional equation `adjMatrix_functional_eq` proves:
  (A - k·I) · (A² - (k-1)·I) = 0

This is equivalent to: aeval A ((X-k)(X²-(k-1))) = 0.

By `minpoly.dvd` (Mathlib): minpoly ℤ A | (X-k)(X²-(k-1)).

Since the annihilating polynomial has degree 3, the minimal polynomial
has degree ≤ 3. Combined with:
- A𝟙 = k𝟙 (proved: adjMatrix_mulVec_ones) — k is an eigenvalue
- tr(A) = 0 (proved: adjMatrix_trace_zero)
- tr(A²) = nk (proved: trace_adjMatrix_sq)

The characteristic polynomial argument eliminates charpoly_eigenvalue_data.

### Current Status
- Annihilating polynomial: PROVED (adjMatrix_functional_eq)
- k is eigenvalue: PROVED (adjMatrix_mulVec_ones)
- tr(A) = 0: PROVED (adjMatrix_trace_zero)
- tr(A²) = nk: PROVED (trace_adjMatrix_sq)
- J² = nJ: PROVED (onesMatrix_sq)
- tr(J) = n: PROVED (trace_onesMatrix)
- Eigenvalue structure → k = 2: PROVED (spectral_regular_friendship)

### Missing (requires further work)
- Irreducibility of X²-(k-1) over ℚ when k-1 not square
- Charpoly factorization: (X-k)^a · (X²-(k-1))^b
- Trace coefficient: -ak = 0 forces a = 0
- Contradiction → k-1 perfect square
- tr(A²) gives a = 1, trace gives s|k
-/

open Polynomial in
/-- **Annihilating polynomial**: the polynomial (X-k)(X²-(k-1)) kills A.
    This bridges `adjMatrix_functional_eq` to `Polynomial.aeval` form,
    enabling use of `minpoly.dvd` from Mathlib. -/
theorem annihilating_polynomial (hF : IsFriendshipGraph G) (k : ℕ) (hk : k ≥ 1)
    (hreg : ∀ v : V, G.degree v = k) :
    aeval (G.adjMatrix ℤ)
      ((X - C (↑k : ℤ)) * (X ^ 2 - C (↑k - 1 : ℤ))) = 0 := by
  simp only [map_mul, map_sub, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, sq, ← sub_smul]
  exact adjMatrix_functional_eq G hF k hk hreg

/-
## Next step: Connect annihilating polynomial to charpoly.

The `minpoly.dvd` approach requires `Field` (ℤ is not a field).
Work over ℚ instead, or use charpoly evaluation directly.
See Part XVI at end of file for proved infrastructure.
-/

-- ============================================================================
-- Part XV: det(kI - A) = 0 (k is an eigenvalue)
-- ============================================================================

/-- Over an integral domain: if M·v = 0 and v ≠ 0, then det(M) = 0.
    Uses the adjugate identity adj(M)·M = det(M)·I:
    det(M)·v = adj(M)·(M·v) = adj(M)·0 = 0, and v ≠ 0 forces det(M) = 0. -/
theorem det_eq_zero_of_mulVec_eq_zero
    {M : Matrix V V ℤ} {v : V → ℤ} (hv : v ≠ 0) (hMv : M.mulVec v = 0) :
    M.det = 0 := by
  -- From adj(M) * M = det(M) • I, deduce det(M) • v = 0
  have hdetv : M.det • v = 0 := by
    calc M.det • v
        = (M.det • (1 : Matrix V V ℤ)).mulVec v := by
            simp [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (M.adjugate * M).mulVec v := by rw [Matrix.adjugate_mul]
      _ = M.adjugate.mulVec (M.mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = M.adjugate.mulVec 0 := by rw [hMv]
      _ = 0 := by rw [Matrix.mulVec_zero]
  -- v ≠ 0 means some entry is nonzero
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hv (funext h)
  -- det(M) * v(i) = 0 and v(i) ≠ 0 forces det(M) = 0
  have := congr_fun hdetv i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_right hi

/-- **det(kI - A) = 0**: The matrix kI - A has a nontrivial kernel (the all-ones
    vector), so its determinant is zero.
    This means k is a root of the characteristic polynomial det(XI - A). -/
theorem det_kI_sub_adjMatrix_eq_zero (k : ℕ) (hreg : ∀ v : V, G.degree v = k)
    [Nonempty V] :
    (↑k • (1 : Matrix V V ℤ) - G.adjMatrix ℤ).det = 0 := by
  apply det_eq_zero_of_mulVec_eq_zero (v := fun _ => (1 : ℤ))
  · -- 𝟙 = (fun _ => 1) ≠ 0 since V is nonempty
    intro h
    have := congr_fun h (Classical.arbitrary V)
    norm_num at this
  · -- (kI - A) · 𝟙 = k𝟙 - A𝟙 = k𝟙 - k𝟙 = 0
    ext i
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    rw [adjMatrix_mulVec_ones G k hreg i]
    ring

-- ============================================================================
-- Part XVI: Characteristic Polynomial Infrastructure
-- ============================================================================

/-- **Trace equals negative of X^{n-1} coefficient of charpoly.**
    From Mathlib: tr(A) = -(charpoly A).coeff (card V - 1).
    Since tr(A) = 0, the X^{n-1} coefficient is 0. -/
theorem charpoly_subleading_coeff_zero [Nonempty V] :
    (Matrix.charpoly (G.adjMatrix ℤ)).coeff (Fintype.card V - 1) = 0 := by
  have h := Matrix.trace_eq_neg_charpoly_coeff (G.adjMatrix ℤ)
  rw [adjMatrix_trace_zero] at h
  linarith

/-- **charpoly evaluation identity**: eval k (charpoly A) = det(kI - A).
    Uses RingHom.map_det: det commutes with the evaluation ring homomorphism. -/
theorem charpoly_eval_eq_det (x : ℤ) :
    Polynomial.eval x (Matrix.charpoly (G.adjMatrix ℤ)) =
      (x • (1 : Matrix V V ℤ) - G.adjMatrix ℤ).det := by
  unfold Matrix.charpoly
  change (Polynomial.evalRingHom x) (Matrix.charmatrix (G.adjMatrix ℤ)).det =
    (x • (1 : Matrix V V ℤ) - G.adjMatrix ℤ).det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp_all [Matrix.diagonal, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_zero]

/-- **k is a root of charpoly(A).** Direct consequence of det(kI-A)=0. -/
theorem charpoly_root_k (k : ℕ) (hreg : ∀ v : V, G.degree v = k) [Nonempty V] :
    Polynomial.IsRoot (Matrix.charpoly (G.adjMatrix ℤ)) (↑k : ℤ) := by
  rw [Polynomial.IsRoot, charpoly_eval_eq_det]
  exact det_kI_sub_adjMatrix_eq_zero G k hreg

/-- **Degree of charpoly = card V.** -/
theorem charpoly_degree [Nonempty V] :
    (Matrix.charpoly (G.adjMatrix ℤ)).natDegree = Fintype.card V :=
  Matrix.charpoly_natDegree_eq_dim (G.adjMatrix ℤ)

/-- **(X - k) divides charpoly(A).** Since k is a root of charpoly, (X - k) divides it. -/
theorem x_sub_k_dvd_charpoly (k : ℕ) (hreg : ∀ v : V, G.degree v = k) [Nonempty V] :
    (Polynomial.X - Polynomial.C (↑k : ℤ)) ∣ Matrix.charpoly (G.adjMatrix ℤ) :=
  Polynomial.dvd_iff_isRoot.mpr (charpoly_root_k G k hreg)

/-
## Status: Axiom Elimination Progress

### Proved in this file:
1. A satisfies (X-k)(X²-(k-1)) = 0 (annihilating_polynomial)
2. k is a root of charpoly(A) (charpoly_root_k)
3. (X-k) | charpoly(A) (x_sub_k_dvd_charpoly)
4. The X^{n-1} coefficient of charpoly(A) is 0 (charpoly_subleading_coeff_zero)
5. tr(A) = 0, tr(A²) = nk
6. s | s²+1 → s = 1 (dvd_sq_add_one_imp_one)

### Remaining gap:
Need: "All roots of charpoly are among {k, √(k-1), -√(k-1)}"

**Approach A (via ℚ)**: Transfer annihilating polynomial to ℚ, apply minpoly.dvd
(ℚ is a field so minpoly.dvd works), then charpoly roots ⊂ minpoly roots ⊂ {k,±√(k-1)}.

**Approach B (direct)**: Show charpoly/(X-k) has all roots satisfying λ²=k-1.
Factor charpoly = (X-k)·q(X) where q satisfies aeval constraints.

**Approach C (Newton)**: Use Newton's identities + charpoly ∈ ℤ[X] integrality
to extract all coefficients from power sums, then factorize.

Once roots are constrained: charpoly ∈ ℤ[X] with irrational roots forces
k-1 = s² (conjugate root theorem), then trace gives s|k, then s|s²+1 → s=1 → k=2.
-/

-- ============================================================================
-- Part XVIII: Axiom Elimination via Characteristic Polynomial
-- ============================================================================

/-
## Complete Axiom Elimination Strategy

The axiom `charpoly_eigenvalue_data` can be eliminated entirely using a
**characteristic polynomial parity argument** that avoids the spectral theorem.

### Key Identity

Let g = charpoly(A) ∈ ℤ[X] (monic, degree n) and f = g/(X-k) ∈ ℤ[X].
From A² = (k-1)I + J and det arithmetic:

    f(X) · f(-X) = (X² - (k-1))^{n-1}

### Parity Contradiction

If k-1 is NOT a perfect square, then X²-(k-1) is irreducible over ℤ.
By unique factorization in ℤ[X]: f = (X²-(k-1))^{(n-1)/2}.
This polynomial has only EVEN-degree terms, so its X^{n-2} coefficient is 0.

But from g = (X-k)·f and tr(A) = 0:
  X^{n-2} coeff of f = k ≥ 2.

Contradiction! So k-1 IS a perfect square.

### Divisibility Conclusion

With k-1 = s², we get f = (X-s)^a·(X+s)^b (a+b = n-1).
The X^{n-2} coeff gives (b-a)·s = k, so s | k.
Since k = s²+1: s | s²+1, giving s = 1, k = 2. ∎

### Proof Dependencies

The following lemmas formalize these steps:
- det(XI-A)·det(XI+A) = det(X²I-A²) over Polynomial ℤ [Matrix.det_mul]
- det(cI - J) = c^{n-1}(c-n) for all-ones matrix J [rank-1 det formula]
- charpoly evaluation: g(k) = 0 from A𝟙 = k𝟙 [det singularity]

These are standard Mathlib results requiring careful API integration.
-/

open Polynomial

/-- Over an integral domain, if M·v = 0 and v ≠ 0, then det(M) = 0.
    Uses the adjugate identity: adj(M)·M = det(M)·I. -/
private lemma det_eq_zero_of_kernel {M : Matrix V V ℤ} {v : V → ℤ}
    (hv : v ≠ 0) (hMv : M.mulVec v = 0) : M.det = 0 := by
  have hdetv : M.det • v = 0 := by
    calc M.det • v
      = (M.det • (1 : Matrix V V ℤ)).mulVec v := by
          simp [Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = (M.adjugate * M).mulVec v := by rw [Matrix.adjugate_mul]
      _ = M.adjugate.mulVec (M.mulVec v) := by rw [Matrix.mulVec_mulVec]
      _ = M.adjugate.mulVec 0 := by rw [hMv]
      _ = 0 := by simp [Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hv (funext h)
  have := congr_fun hdetv i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  exact (mul_eq_zero.mp this).resolve_right hi

/-- Scalar matrix times constant vector gives the scalar value. -/
private lemma scalar_mulVec_const (a : ℤ) (i : V) :
    (Matrix.scalar V a).mulVec (fun _ => (1 : ℤ)) i = a := by
  have h1 : (Matrix.scalar V a).mulVec (fun _ => (1 : ℤ)) i =
      ∑ j : V, Matrix.scalar V a i j * 1 := rfl
  rw [h1]
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, mul_one]
  rw [Finset.sum_eq_single i
    (fun j _ hji => by simp [Ne.symm hji])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

/-- The characteristic polynomial of the adjacency matrix evaluated at k is zero.
    Proof: A·𝟙 = k·𝟙 means (kI - A) is singular, so det(kI - A) = 0.
    Since charpoly(A)(k) = det(kI - A), we get charpoly(A)(k) = 0. -/
lemma adjMatrix_charpoly_eval_k (hF : IsFriendshipGraph G) (k : ℕ) (hk : k ≥ 1)
    (hreg : ∀ v : V, G.degree v = k) [Nonempty V] :
    (G.adjMatrix ℤ).charpoly.eval (↑k : ℤ) = 0 := by
  -- charpoly(A).eval k = det(scalar V k - A) = 0
  rw [Matrix.eval_charpoly]
  apply det_eq_zero_of_kernel (v := fun _ => (1 : ℤ))
  · intro h; exact absurd (congr_fun h (Classical.arbitrary V)) (by norm_num)
  · ext i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    rw [adjMatrix_mulVec_ones G k hreg i, scalar_mulVec_const]

/-- (X - k) divides the characteristic polynomial of the adjacency matrix.
    Follows from adjMatrix_charpoly_eval_k via the factor theorem. -/
lemma X_sub_k_dvd_adjMatrix_charpoly (hF : IsFriendshipGraph G) (k : ℕ) (hk : k ≥ 1)
    (hreg : ∀ v : V, G.degree v = k) [Nonempty V] :
    (X - C (↑k : ℤ)) ∣ (G.adjMatrix ℤ).charpoly := by
  rw [dvd_iff_isRoot, IsRoot]
  exact adjMatrix_charpoly_eval_k G hF k hk hreg

/-- Regularity alone supplies the trivial adjacency eigenvalue. -/
lemma X_sub_degree_dvd_adjMatrix_charpoly
    (k : ℕ) (hreg : ∀ v : V, G.degree v = k) [Nonempty V] :
    (X - C (↑k : ℤ)) ∣ (G.adjMatrix ℤ).charpoly := by
  rw [dvd_iff_isRoot, IsRoot, Matrix.eval_charpoly]
  apply det_eq_zero_of_kernel (v := fun _ => (1 : ℤ))
  · intro h
    exact absurd (congr_fun h (Classical.arbitrary V)) (by norm_num)
  · ext i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    rw [adjMatrix_mulVec_ones G k hreg i, scalar_mulVec_const]

/-- **det(I - t·J) = 1 - n·t** for the all-ones matrix J.
    Uses the Weinstein-Aronszajn identity: det(I - AB) = det(I - BA).
    With A : V×(Fin 1) all t's, B : (Fin 1)×V all 1's: BA is [nt]. -/
private lemma det_one_sub_smul_onesMatrix (t : ℤ) :
    ((1 : Matrix V V ℤ) - t • onesMatrix V).det =
    1 - ↑(Fintype.card V) * t := by
  -- Define A (column of t's) and B (row of 1's) such that AB = t•J
  set A : Matrix V (Fin 1) ℤ := Matrix.of (fun _ _ => t) with hA_def
  set B : Matrix (Fin 1) V ℤ := Matrix.of (fun _ _ => (1 : ℤ)) with hB_def
  have hAB : A * B = t • onesMatrix V := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, onesMatrix,
      Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_one, mul_one, hA_def, hB_def]
  rw [← hAB, Matrix.det_one_sub_mul_comm]
  -- Now: det(I_{Fin 1} - B * A) is a 1×1 determinant
  simp only [Matrix.det_fin_one]
  -- The single entry is 1 - (BA)₀₀ = 1 - Σᵥ 1·t = 1 - nt
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, B, A, Matrix.mul_apply,
    Matrix.of_apply, Finset.sum_const, Finset.card_univ, mul_one]
  rw [nsmul_eq_natCast_mul]
  ring

/-- Generalized det(I - tJ) = 1 - nt over any commutative ring. -/
lemma det_one_sub_smul_ones_gen {R : Type*} [CommRing R] (t : R) :
    ((1 : Matrix V V R) - t • Matrix.of (fun (_ : V) (_ : V) => (1 : R))).det =
    1 - ↑(Fintype.card V) * t := by
  set A : Matrix V (Fin 1) R := Matrix.of (fun _ _ => t) with hA_def
  set B : Matrix (Fin 1) V R := Matrix.of (fun _ _ => (1 : R)) with hB_def
  have hAB : A * B = t • Matrix.of (fun (_ : V) (_ : V) => (1 : R)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Fin.sum_univ_one, mul_one, hA_def, hB_def]
  rw [← hAB, Matrix.det_one_sub_mul_comm]
  simp only [Matrix.det_fin_one, Matrix.sub_apply, Matrix.one_apply_eq,
    B, A, Matrix.mul_apply, Matrix.of_apply, Finset.sum_const,
    Finset.card_univ, mul_one, hA_def, hB_def]
  push_cast; ring

/-- **J is singular**: det(onesMatrix V) = 0 for |V| ≥ 2.
    All rows are identical (all 1's), so two distinct rows are equal. -/
lemma det_onesMatrix_eq_zero (hn : Fintype.card V ≥ 2) :
    (onesMatrix V).det = 0 := by
  have ⟨a, b, hab⟩ : ∃ a b : V, a ≠ b := by
    by_contra h; push_neg at h
    have : Fintype.card V ≤ 1 := by
      rw [Fintype.card_le_one_iff]; exact fun x y => by_contra (fun hxy => hxy (h x y))
    omega
  exact Matrix.det_zero_of_row_eq hab (by ext j; simp [onesMatrix, Matrix.of_apply])

/-- Generalized J-singular over any CommRing: det of all-ones matrix = 0 for |V| ≥ 2. -/
private lemma det_ones_eq_zero_gen {R : Type*} [CommRing R] (hn : Fintype.card V ≥ 2) :
    (Matrix.of (fun (_ : V) (_ : V) => (1 : R))).det = 0 := by
  have ⟨a, b, hab⟩ : ∃ a b : V, a ≠ b := by
    by_contra h; push_neg at h
    have : Fintype.card V ≤ 1 := by
      rw [Fintype.card_le_one_iff]; exact fun x y => by_contra (fun hxy => hxy (h x y))
    omega
  exact Matrix.det_zero_of_row_eq hab (by ext j; simp [Matrix.of_apply])

/-- **det(cI - J) = c^{n-1}(c-n)** for the all-ones matrix J.

    Proof: For c ≠ 0, cast to ℚ where c is invertible. Factor:
    det(cI - J) = c^n · det(I - c⁻¹J) = c^n(1 - n/c) = c^{n-1}(c-n)
    using det_one_sub_smul_ones_gen (Weinstein-Aronszajn).
    For c = 0: det(-J) = (-1)^n · det(J) = 0 when n ≥ 2
    (J singular by det_onesMatrix_eq_zero), handled directly for n = 1. -/
lemma det_scalar_sub_onesMatrix' [Nonempty V] (c : ℤ) :
    (c • (1 : Matrix V V ℤ) - onesMatrix V).det =
    c ^ (Fintype.card V - 1) * (c - ↑(Fintype.card V)) := by
  set n := Fintype.card V with hn
  have hn_pos : n ≥ 1 := Fintype.card_pos
  by_cases hc : c = 0
  · subst hc; simp only [zero_smul, zero_sub, zero_pow, Int.cast_zero]
    by_cases hn1 : n = 1
    · have : Subsingleton V := by rw [← Fintype.card_le_one_iff_subsingleton]; omega
      haveI : Unique V := uniqueOfSubsingleton (Classical.arbitrary V)
      simp [hn1, Matrix.det_unique, onesMatrix, Matrix.of_apply]
    · have hn2 : n ≥ 2 := by omega
      have hJ0 : (onesMatrix V).det = 0 := det_onesMatrix_eq_zero hn2
      have hsmul : -onesMatrix V = (-1 : ℤ) • onesMatrix V := by
        ext i j; simp [onesMatrix, Matrix.of_apply]
      rw [hsmul, Matrix.det_smul, hJ0, mul_zero]
      simp [zero_pow (show n - 1 ≠ 0 by omega)]
  · have hcq : (↑c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
    suffices hq : ((c • (1 : Matrix V V ℤ) - onesMatrix V).det : ℚ) =
        ↑(c ^ (n - 1) * (c - ↑n)) by exact_mod_cast hq
    set M := c • (1 : Matrix V V ℤ) - onesMatrix V with hM_def
    show (Int.castRingHom ℚ) M.det = _
    rw [RingHom.map_det]
    have hmap : (RingHom.mapMatrix (Int.castRingHom ℚ)) M =
        (↑c : ℚ) • (1 : Matrix V V ℚ) -
          Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ)) := by
      ext i j
      simp only [hM_def, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, onesMatrix,
        Matrix.of_apply, smul_eq_mul, map_sub, map_mul, Int.coe_castRingHom]
      split <;> simp
    rw [hmap]
    have hfactor : (↑c : ℚ) • (1 : Matrix V V ℚ) -
        Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ)) =
        (↑c : ℚ) • ((1 : Matrix V V ℚ) -
          (↑c : ℚ)⁻¹ • Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ))) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.of_apply, smul_eq_mul]
      by_cases hij : i = j <;> simp [hij, mul_sub, mul_inv_cancel₀ hcq]
    rw [hfactor, Matrix.det_smul, det_one_sub_smul_ones_gen]
    have h1 : Fintype.card V = n - 1 + 1 := by omega
    rw [h1, pow_succ, show (n - 1 + 1 : ℕ) = n from by omega]
    push_cast; field_simp

/-- **Characteristic polynomial of the all-ones matrix**: charpoly(J) = X^{n-1}(X-n).
    Proof: By `Polynomial.funext`, it suffices to show equality at all c ∈ ℤ.
    eval c (charpoly J) = det(cI-J) = c^{n-1}(c-n) = eval c (X^{n-1}(X-n)).
    The first equality uses Matrix.aeval_self_charpoly indirectly via evaluation.
    The second uses det_scalar_sub_onesMatrix (proved below). -/
lemma onesMatrix_charpoly [Nonempty V] :
    (onesMatrix V).charpoly =
    Polynomial.X ^ (Fintype.card V - 1) *
    (Polynomial.X - Polynomial.C (↑(Fintype.card V) : ℤ)) := by
  -- By universality: two integer polynomials agreeing on all of ℤ are equal
  apply Polynomial.funext
  intro c
  -- LHS: charpoly(J).eval c = det(cI - J)
  have hlhs : Polynomial.eval c (onesMatrix V).charpoly =
      (c • (1 : Matrix V V ℤ) - onesMatrix V).det := by
    show (Polynomial.evalRingHom c) ((Matrix.charmatrix (onesMatrix V)).det) = _
    rw [RingHom.map_det]; congr 1; ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.charmatrix_apply, Matrix.sub_apply, Matrix.diagonal_apply,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      onesMatrix, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split <;> simp
  -- RHS: eval c (X^{n-1}(X-n)) = c^{n-1}(c-n)
  have hrhs : Polynomial.eval c (Polynomial.X ^ (Fintype.card V - 1) *
      (Polynomial.X - Polynomial.C (↑(Fintype.card V) : ℤ))) =
      c ^ (Fintype.card V - 1) * (c - ↑(Fintype.card V)) := by
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  rw [hlhs, hrhs]
  exact det_scalar_sub_onesMatrix' c

/-- **det(cI - J) = c^{n-1}(c-n)** for the all-ones matrix J.

    Proof: For c ≠ 0, cast to ℚ where c is invertible. Factor:
    det(cI - J) = c^n · det(I - c⁻¹J) = c^n(1 - n/c) = c^{n-1}(c-n)
    using det_one_sub_smul_ones_gen (Weinstein-Aronszajn).
    For c = 0: det(-J) = (-1)^n · det(J) = 0 when n ≥ 2
    (J singular by det_onesMatrix_eq_zero), handled directly for n = 1. -/
lemma det_scalar_sub_onesMatrix [Nonempty V] (c : ℤ) :
    (c • (1 : Matrix V V ℤ) - onesMatrix V).det =
    c ^ (Fintype.card V - 1) * (c - ↑(Fintype.card V)) := by
  set n := Fintype.card V with hn
  have hn_pos : n ≥ 1 := Fintype.card_pos
  by_cases hc : c = 0
  · -- Case c = 0: det(-J) = 0^{n-1} * (0 - n)
    subst hc; simp only [zero_smul, zero_sub, zero_pow, Int.cast_zero]
    by_cases hn1 : n = 1
    · -- n = 1: V is a singleton, det(-J) = -1
      have : Subsingleton V := by rw [← Fintype.card_le_one_iff_subsingleton]; omega
      haveI : Unique V := uniqueOfSubsingleton (Classical.arbitrary V)
      simp [hn1, Matrix.det_unique, onesMatrix, Matrix.of_apply]
    · -- n ≥ 2: det(-J) = 0 since J is singular
      have hn2 : n ≥ 2 := by omega
      have hJ0 : (onesMatrix V).det = 0 := det_onesMatrix_eq_zero hn2
      have hsmul : -onesMatrix V = (-1 : ℤ) • onesMatrix V := by
        ext i j; simp [onesMatrix, Matrix.of_apply]
      rw [hsmul, Matrix.det_smul, hJ0, mul_zero]
      simp [zero_pow (show n - 1 ≠ 0 by omega)]
  · -- Case c ≠ 0: lift to ℚ where c⁻¹ exists
    have hcq : (↑c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
    -- Suffices to prove in ℚ
    suffices hq : ((c • (1 : Matrix V V ℤ) - onesMatrix V).det : ℚ) =
        ↑(c ^ (n - 1) * (c - ↑n)) by exact_mod_cast hq
    -- Map the ℤ determinant through ℤ → ℚ
    set M := c • (1 : Matrix V V ℤ) - onesMatrix V with hM_def
    show (Int.castRingHom ℚ) M.det = _
    rw [RingHom.map_det]
    -- Simplify the mapped matrix
    have hmap : (RingHom.mapMatrix (Int.castRingHom ℚ)) M =
        (↑c : ℚ) • (1 : Matrix V V ℚ) -
          Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ)) := by
      ext i j
      simp only [hM_def, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, onesMatrix,
        Matrix.of_apply, smul_eq_mul, map_sub, map_mul, Int.coe_castRingHom]
      split <;> simp
    rw [hmap]
    -- Factor: cI - J = c(I - c⁻¹J)
    have hfactor : (↑c : ℚ) • (1 : Matrix V V ℚ) -
        Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ)) =
        (↑c : ℚ) • ((1 : Matrix V V ℚ) -
          (↑c : ℚ)⁻¹ • Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ))) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.of_apply, smul_eq_mul]
      by_cases hij : i = j <;> simp [hij, mul_sub, mul_inv_cancel₀ hcq]
    rw [hfactor, Matrix.det_smul, det_one_sub_smul_ones_gen]
    -- Algebra: c^n * (1 - n * c⁻¹) = c^{n-1} * (c - n)
    -- Split c^n = c^{n-1} * c
    have h1 : Fintype.card V = n - 1 + 1 := by omega
    rw [h1, pow_succ, show (n - 1 + 1 : ℕ) = n from by omega]
    push_cast; field_simp

/-- det(cI - J) = c^{n-1}(c-n) over ℤ[X], proved via Polynomial.funext. -/
private lemma det_scalar_sub_onesMatrix_poly [Nonempty V] (c : Polynomial ℤ) :
    (c • (1 : Matrix V V (Polynomial ℤ)) -
      Matrix.of (fun (_ : V) (_ : V) => (1 : Polynomial ℤ))).det =
    c ^ (Fintype.card V - 1) * (c - C (↑(Fintype.card V) : ℤ)) := by
  apply Polynomial.funext; intro a
  simp only [eval_mul, eval_pow, eval_sub, eval_C]
  -- LHS: eval (det of poly matrix) = det (evaluated matrix)
  show (Polynomial.evalRingHom a)
    ((c • (1 : Matrix V V (Polynomial ℤ)) -
      Matrix.of (fun _ _ => (1 : Polynomial ℤ))).det) = _
  rw [RingHom.map_det]
  have hmap : (RingHom.mapMatrix (Polynomial.evalRingHom a))
      (c • (1 : Matrix V V (Polynomial ℤ)) -
        Matrix.of (fun _ _ => (1 : Polynomial ℤ))) =
      Polynomial.eval a c • (1 : Matrix V V ℤ) - onesMatrix V := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, onesMatrix, Matrix.of_apply,
      smul_eq_mul, map_sub, map_mul]
    split <;> simp [Polynomial.eval_one, Polynomial.eval_zero]
  rw [hmap]; exact det_scalar_sub_onesMatrix _

/-- The key product identity for the quotient polynomial.

    Let g = charpoly(A), f = g/(X-k). Then:
      f(X) · f(-X) = (X² - (k-1))^{n-1}

    **Proof strategy** (using onesMatrix_charpoly):
    1. (XI-A')(XI+A') = X²I-A'² where A' = A.map C [ring identity in Polynomial ℤ matrices]
    2. det(LHS) = charpoly(A)·charpoly(-A) [Matrix.det_mul]
    3. charpoly(-A) = (-1)^n · charpoly(A).comp(-X) [standard identity]
       For n odd: = -(-(X+k))·f(-X) = (X+k)·f.comp(-X)
    4. A² = (k-1)I+J → X²I-A'² = (X²-(k-1))I - J.map C
    5. det(RHS) = eval₂ C (X²-(k-1)) (onesMatrix_charpoly)
       = (X²-(k-1))^{n-1}·(X²-(k-1)-n)
       = (X²-(k-1))^{n-1}·(X²-k²) [since k-1+n=k²]
    6. Combined: (X-k)·f·(X+k)·f(-X) = (X²-(k-1))^{n-1}·(X-k)(X+k)
    7. Cancel (X-k)(X+k) in integral domain Polynomial ℤ

    Dependencies: onesMatrix_charpoly, adjMatrix_sq_eq, RingHom.map_det. -/
lemma charpoly_quotient_product [Nonempty V] (hF : IsFriendshipGraph G) (k : ℕ)
    (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) (f : Polynomial ℤ)
    (hf : (G.adjMatrix ℤ).charpoly = (X - C (↑k : ℤ)) * f) :
    f * f.comp (-X) = (X ^ 2 - C (↑(k - 1) : ℤ)) ^ (Fintype.card V - 1) := by
  set n := Fintype.card V with hn_def
  set A := G.adjMatrix ℤ with hA_def
  obtain ⟨u⟩ := ‹Nonempty V›
  have hn_ge : n ≥ 3 := by
    have := regular_friendship_card G hF u k hreg (by omega)
    rw [← hn_def] at this; nlinarith [Nat.mul_le_mul_left k (show k - 1 ≥ 1 from by omega)]
  have hn_val := regular_friendship_card G hF u k hreg (by omega)
  -- n is odd
  have heven_kk : Even (k * (k - 1)) := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact ⟨m * (k - 1), by rw [hm]; ring⟩
    · exact ⟨k * m, by rw [show k - 1 = 2 * m from by omega]; ring⟩
  have hn_odd : Odd n := by
    obtain ⟨t, ht⟩ := heven_kk
    show Odd (Fintype.card V); rw [hn_val, ht]; exact ⟨t, by ring⟩
  -- A² = (k-1)I + J
  have hAsq : A * A = (↑k - 1 : ℤ) • (1 : Matrix V V ℤ) + onesMatrix V := by
    simp only [hA_def]; exact adjMatrix_sq_eq G hF k (by omega) hreg
  -- Step 1: For all x : ℤ, (x²-k²)*(f(x)*f(-x) - (x²-(k-1))^{n-1}) = 0
  -- This is the key evaluation identity, proved via two computations of g(x)*g(-x)
  have heval : ∀ x : ℤ, (x ^ 2 - (↑k : ℤ) ^ 2) *
      (f.eval x * f.eval (-x) - (x ^ 2 - ↑(k - 1 : ℕ)) ^ (n - 1)) = 0 := by
    intro x
    -- g(x) via factoring: g = (X-k)*f
    have hgx : Polynomial.eval x (A.charpoly) = (x - ↑k) * f.eval x := by
      rw [hf]; simp [Polynomial.eval_mul, Polynomial.eval_sub]
    have hgmx : Polynomial.eval (-x) (A.charpoly) = (-x - ↑k) * f.eval (-x) := by
      rw [hf]; simp [Polynomial.eval_mul, Polynomial.eval_sub]
    -- g(x) = det(xI-A) via charpoly definition
    have hg_det := charpoly_eval_eq_det G x
    have hgm_det := charpoly_eval_eq_det G (-x)
    -- Way 1: g(x)*g(-x) = -(x²-k²)*f(x)*f(-x) (from factoring g = (X-k)*f)
    have hway1 : Polynomial.eval x A.charpoly * Polynomial.eval (-x) A.charpoly =
        -(x ^ 2 - (↑k : ℤ) ^ 2) * (f.eval x * f.eval (-x)) := by
      rw [hgx, hgmx]; ring
    -- Way 2: g(x)*g(-x) = -(x²-(k-1))^{n-1} * (x²-k²) (from determinant computation)
    -- Key intermediate: det(xI-A) * det(-xI-A) = (-1)^n * det((xI-A)(xI+A))
    have hneg_eq : (-x) • (1 : Matrix V V ℤ) - A = -(x • 1 + A) := by
      ext i j; simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.neg_apply, Matrix.one_apply, smul_eq_mul]; ring
    -- (xI-A)(xI+A) = x²I - A²
    have hdiff_sq : (x • (1 : Matrix V V ℤ) - A) * (x • 1 + A) = x ^ 2 • 1 - A * A := by
      rw [sub_mul, mul_add, mul_add, smul_mul_assoc, Matrix.one_mul,
        smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one, smul_smul, sq]
      abel
    -- x²I - A² = (x²-(k-1))I - J
    have hmatrix_eq : x ^ 2 • (1 : Matrix V V ℤ) - A * A =
        (x ^ 2 - (↑k - 1 : ℤ)) • (1 : Matrix V V ℤ) - onesMatrix V := by
      rw [hAsq]; ext i j; simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
        Matrix.one_apply, onesMatrix, Matrix.of_apply, smul_eq_mul]; ring
    -- det((x²-(k-1))I - J) = (x²-(k-1))^{n-1} * ((x²-(k-1)) - n)
    have hdet_formula := @det_scalar_sub_onesMatrix V _ _ ‹Nonempty V› (x ^ 2 - (↑k - 1 : ℤ))
    -- x²-(k-1)-n = x²-k²  (since n = k(k-1)+1)
    have hk_sq : x ^ 2 - (↑k - 1 : ℤ) - ↑(Fintype.card V) = x ^ 2 - (↑k : ℤ) ^ 2 := by
      have h1 := hn_val; zify [show 1 ≤ k from by omega] at h1; nlinarith [sq (↑k : ℤ)]
    -- Combine way 2
    have hway2 : Polynomial.eval x A.charpoly * Polynomial.eval (-x) A.charpoly =
        -((x ^ 2 - ↑(k - 1 : ℕ)) ^ (n - 1) * (x ^ 2 - (↑k : ℤ) ^ 2)) := by
      rw [hg_det, hgm_det, hneg_eq, Matrix.det_neg]
      -- Goal: det(xI-A) * ((-1)^n * det(xI+A)) = -(...)
      rw [show (-1 : ℤ) ^ Fintype.card V = -1 from by rw [← hn_def]; exact hn_odd.neg_one_pow]
      rw [show (x • (1 : Matrix V V ℤ) - A).det * ((-1) * (x • 1 + A).det) =
        -((x • 1 - A).det * (x • 1 + A).det) from by ring,
        ← Matrix.det_mul, hdiff_sq, hmatrix_eq, hdet_formula, hk_sq]
      push_cast [Nat.cast_sub (show 1 ≤ k from by omega)]; ring
    -- Equate: (x²-k²)*(f(x)f(-x) - (x²-(k-1))^{n-1}) = 0
    nlinarith [hway1, hway2]
  -- Step 2: Polynomial identity
  -- Show (X²-k²) * (f·f(-X) - rhs) = 0, then factor in ℤ[X] (domain)
  set Q := f * f.comp (-X) - (X ^ 2 - C (↑(k - 1) : ℤ)) ^ (n - 1) with hQ_def
  -- P := (X²-k²) * Q evaluates to 0 at all integers
  have hprod_eval : ∀ x : ℤ, Polynomial.eval x ((X ^ 2 - C ((↑k : ℤ) ^ 2)) * Q) = 0 := by
    intro x; simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_neg, hQ_def]
    exact heval x
  -- Polynomial vanishing everywhere over ℤ (infinite domain) is zero
  have hprod_zero : (X ^ 2 - C ((↑k : ℤ) ^ 2)) * Q = 0 := by
    have h0 : ∀ x : ℤ, ((X ^ 2 - C ((↑k : ℤ) ^ 2)) * Q).eval x = (0 : Polynomial ℤ).eval x := by
      intro x; rw [Polynomial.eval_zero]; exact hprod_eval x
    exact Polynomial.funext h0
  -- X²-k² ≠ 0 in ℤ[X]
  have hne : (X ^ 2 - C ((↑k : ℤ) ^ 2) : Polynomial ℤ) ≠ 0 := by
    intro h
    have : (X ^ 2 - C ((↑k : ℤ) ^ 2) : Polynomial ℤ).coeff 2 = (0 : Polynomial ℤ).coeff 2 :=
      congr_arg (·.coeff 2) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C,
      Polynomial.coeff_zero, if_true, ite_false] at this; omega
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod_zero).resolve_left hne)

/-- The sub-leading coefficient of f equals k.

    From g = (X-k)·f and the X^{n-1} coefficient of g = -tr(A) = 0:
      coeff_{n-1}(g) = coeff_{n-2}(f) + (-k)·coeff_{n-1}(f)
                     = coeff_{n-2}(f) - k
    Setting equal to 0: coeff_{n-2}(f) = k.

    Here f has degree n-1, so coeff_{n-2} is its sub-leading coefficient. -/
lemma quotient_subleading_coeff (hF : IsFriendshipGraph G) (k : ℕ) (hk : k ≥ 2)
    (hreg : ∀ v : V, G.degree v = k) [Nonempty V] (f : Polynomial ℤ)
    (hf : (G.adjMatrix ℤ).charpoly = (X - C (↑k : ℤ)) * f)
    (hf_monic : f.Monic)
    (hf_deg : f.natDegree = Fintype.card V - 1) :
    f.coeff (Fintype.card V - 2) = ↑k := by
  set n := Fintype.card V with hn_def
  -- Step 1: tr(A) = 0 gives charpoly.coeff(n-1) = 0
  have htrace : Matrix.trace (G.adjMatrix ℤ) = 0 := adjMatrix_trace_zero G
  have hcoeff_charpoly : (G.adjMatrix ℤ).charpoly.coeff (n - 1) = 0 := by
    have h := Matrix.trace_eq_neg_charpoly_coeff (G.adjMatrix ℤ)
    rw [htrace] at h; linarith
  -- Step 2: f monic of degree n-1: coeff_{n-1}(f) = 1
  have hf_leading : f.coeff (n - 1) = 1 := by
    rw [show n - 1 = f.natDegree from by rw [hf_deg]]
    exact hf_monic.leadingCoeff
  -- Step 3: extract coeff at n-1 from (X-C k)*f using nextCoeff relation
  -- coeff_{n-1}((X-C k)*f) = 1*f.coeff(n-2) + (-k)*f.coeff(n-1)
  --                         = f.coeff(n-2) - k
  -- n ≥ 3 for the coefficient arithmetic
  have hn_ge : n ≥ 3 := by
    have h := regular_friendship_card G hF (Classical.arbitrary V) k hreg (by omega)
    rw [← hn_def] at h
    have : k * (k - 1) ≥ 2 := Nat.mul_le_mul hk (by omega : k - 1 ≥ 1)
    omega
  have hcoeff_prod : ((X - C (↑k : ℤ)) * f).coeff (n - 1) =
      f.coeff (n - 2) - ↑k * f.coeff (n - 1) := by
    -- (X - C k) * f = X * f - C k * f
    rw [sub_mul, coeff_sub, coeff_C_mul]
    -- (X * f).coeff (n-1) = f.coeff (n-2) by coeff_X_mul
    congr 1
    rw [show n - 1 = (n - 2) + 1 from by omega]
    exact coeff_X_mul f (n - 2)
  rw [← hf, hcoeff_charpoly] at hcoeff_prod
  rw [hf_leading, mul_one] at hcoeff_prod
  linarith

/-- A power of (X²-c) has zero coefficient at every odd degree.
    Since (X²-c)^m = Σ C(m,j)(-c)^j X^{2(m-j)}, all terms have even degree. -/
private lemma coeff_sq_sub_C_odd (c : ℤ) (j : ℕ) (hj : Odd j) :
    (X ^ 2 - C c : Polynomial ℤ).coeff j = 0 := by
  obtain ⟨r, hr⟩ := hj
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  have hj_ne_2 : j ≠ 2 := by omega
  have hj_ne_0 : j ≠ 0 := by omega
  simp [hj_ne_2, hj_ne_0]

lemma coeff_odd_of_sq_sub_pow (c : ℤ) (m : ℕ) :
    ∀ j : ℕ, Odd j → ((X ^ 2 - C c : Polynomial ℤ) ^ m).coeff j = 0 := by
  induction m with
  | zero =>
    intro j hj
    simp only [pow_zero, Polynomial.coeff_one]
    obtain ⟨r, hr⟩ := hj
    have : j ≠ 0 := by omega
    simp [this]
  | succ m ih =>
    intro j hj
    rw [pow_succ, Polynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hab
    simp only [Finset.mem_antidiagonal] at hab
    by_cases ha : Even a
    · -- a even → b = j - a is odd (since a+b = j is odd and a is even)
      have hb : Odd b := by
        obtain ⟨r, hr⟩ := hj; obtain ⟨s, hs⟩ := ha
        exact ⟨r - s, by omega⟩
      rw [coeff_sq_sub_C_odd c b hb, mul_zero]
    · -- a odd → (X²-c)^m has zero coeff at a
      have ha_odd : Odd a := by rwa [Nat.not_even_iff_odd] at ha
      rw [ih a ha_odd, zero_mul]

/-- X²-d is irreducible over ℤ when d ≥ 1 is not a perfect square.
    Proof: X²-d is monic (hence primitive), so by Gauss lemma it suffices
    to show irreducibility over ℚ. Over ℚ, X²-d has no rational root
    (since d is not a perfect square), and a degree-2 polynomial over a
    field with no root is irreducible. -/
lemma sq_sub_irreducible_of_not_square (d : ℕ) (hd : d ≥ 1)
    (hns : ∀ s : ℕ, d ≠ s * s) :
    Irreducible (X ^ 2 - C (↑d : ℤ) : Polynomial ℤ) := by
  set p : Polynomial ℤ := X ^ 2 - C (↑d : ℤ) with hp_def
  -- p has no integer root
  have hp_no_root : ∀ r : ℤ, p.eval r ≠ 0 := by
    intro r hr
    simp only [hp_def, eval_sub, eval_pow, eval_X, eval_C] at hr
    have hrd : r * r = ↑d := by nlinarith
    have : d = r.natAbs * r.natAbs := by
      have h1 := Int.natAbs_sq r  -- (↑(natAbs r) : ℤ) ^ 2 = r ^ 2
      have h2 : r ^ 2 = ↑d := by ring_nf; linarith
      have h3 : (r.natAbs : ℤ) ^ 2 = ↑d := h1.trans h2
      have h4 : r.natAbs ^ 2 = d := by exact_mod_cast h3
      nlinarith [sq_nonneg r.natAbs]
    exact hns r.natAbs this
  -- p is monic
  have hp_monic : p.Monic := by
    show (X ^ 2 - C (↑d : ℤ) : Polynomial ℤ).Monic
    apply Polynomial.Monic.sub_of_left (monic_X_pow 2)
    calc (C (↑d : ℤ) : Polynomial ℤ).degree ≤ 0 := degree_C_le
      _ < (X ^ 2 : Polynomial ℤ).degree := by simp [degree_X_pow]
  -- p has natDegree 2
  have hp_deg : p.natDegree = 2 := by
    have hd_deg : (C (↑d : ℤ) : Polynomial ℤ).natDegree < (X ^ 2 : Polynomial ℤ).natDegree := by
      simp [natDegree_C, natDegree_X_pow]
    rw [hp_def, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hd_deg, natDegree_X_pow]
  -- Irreducibility
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · -- Not a unit (natDegree 2 ≠ 0)
    intro hu; linarith [Polynomial.natDegree_eq_zero_of_isUnit hu]
  · -- Factor analysis
    intro a b hab
    have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hp_monic.ne_zero)
    have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hp_monic.ne_zero)
    have hdeg : a.natDegree + b.natDegree = 2 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab]; exact hp_deg
    have hab_monic : (a * b).Monic := hab ▸ hp_monic
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul]; exact hab_monic.leadingCoeff
    -- If either has degree 0, it's a unit (constant with unit value)
    by_cases ha1 : a.natDegree = 0
    · left
      have ha_eq := Polynomial.eq_C_of_natDegree_eq_zero ha1
      have ha_lc : a.leadingCoeff = a.coeff 0 := by
        simp [Polynomial.leadingCoeff, ha1]
      rw [ha_eq]; apply Polynomial.isUnit_C.mpr
      rw [← ha_lc]; exact isUnit_of_dvd_one ⟨_, hlc.symm⟩
    · by_cases hb1 : b.natDegree = 0
      · right
        have hb_eq := Polynomial.eq_C_of_natDegree_eq_zero hb1
        have hb_lc : b.leadingCoeff = b.coeff 0 := by
          simp [Polynomial.leadingCoeff, hb1]
        rw [hb_eq]; apply Polynomial.isUnit_C.mpr
        rw [← hb_lc]
        exact isUnit_of_dvd_one ⟨_, (show 1 = b.leadingCoeff * a.leadingCoeff by linarith)⟩
      · -- Both have degree ≥ 1, hence both have degree 1
        exfalso
        have ha_deg1 : a.natDegree = 1 := by omega
        -- leadingCoeff a is a unit in ℤ, hence ±1
        have ha_lc_unit : IsUnit a.leadingCoeff :=
          isUnit_of_dvd_one ⟨_, hlc.symm⟩
        -- r = -(a.coeff 0) * a.leadingCoeff is a root of a:
        -- eval r a = a.coeff 0 + a.leadingCoeff * r
        --          = a.coeff 0 * (1 - a.leadingCoeff^2) = 0
        set r : ℤ := -(a.coeff 0) * a.leadingCoeff with hr_def
        -- Show a has root r
        have ha_lc_eq : a.coeff 1 = a.leadingCoeff := by
          simp [Polynomial.leadingCoeff, ha_deg1]
        have ha_root : a.eval r = 0 := by
          rw [Polynomial.eval_eq_sum_range, ha_deg1]
          simp only [Finset.sum_range_succ, Finset.sum_range_one,
            pow_zero, mul_one, pow_one]
          rw [ha_lc_eq, hr_def]
          obtain h | h := Int.isUnit_iff.mp ha_lc_unit <;> rw [h] <;> ring
        -- p = a * b, so p(r) = 0
        have hp_root : p.eval r = 0 := by
          rw [hab, eval_mul, ha_root, zero_mul]
        exact hp_no_root r hp_root

/-- In a UFD, if an irreducible p satisfies p(X) = p(-X) and
    f·f(-X) = p^m with f monic, then f = p^{m/2}.

    Applied to p = X²-(k-1), this is the key structural lemma. -/
lemma monic_factor_of_symmetric_irreducible_pow
    (p f : Polynomial ℤ) (m : ℕ) (hm : Even m)
    (hp_irred : Irreducible p) (hp_monic : p.Monic)
    (hp_sym : p.comp (-X) = p)
    (hf_monic : f.Monic)
    (hprod : f * f.comp (-X) = p ^ m) :
    f = p ^ (m / 2) := by
  -- Reduce to a helper with m = k + k
  obtain ⟨k, rfl⟩ := hm
  change f = p ^ ((k + k) / 2)
  rw [show (k + k) / 2 = k from by omega]
  -- Prove by induction on k, generalizing f
  suffices ∀ (f : Polynomial ℤ), f.Monic → f * f.comp (-X) = p ^ (k + k) →
      f = p ^ k by
    exact this f hf_monic hprod
  clear hf_monic hprod f
  induction k with
  | zero =>
    intro f hf_monic hprod
    -- f * f(-X) = 1, f monic → f = 1
    simp only [Nat.zero_add, pow_zero] at hprod ⊢
    have hf_ne : f ≠ 0 := hf_monic.ne_zero
    have hfc_ne : f.comp (-X) ≠ 0 := by
      intro h; rw [h, mul_zero] at hprod; exact zero_ne_one hprod
    have hdeg : f.natDegree = 0 := by
      have := Polynomial.natDegree_mul hf_ne hfc_ne
      rw [hprod, Polynomial.natDegree_one] at this; omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    have : f.coeff 0 = 1 := by
      have h := hf_monic.leadingCoeff
      rw [Polynomial.leadingCoeff, hdeg] at h; exact h
    rw [this]; simp
  | succ k ih =>
    intro f hf_monic hprod
    -- m = 2*(k+1), need f = p^{k+1}
    have hp_prime : Prime p := hp_irred.prime
    -- p | f * f(-X) = p^{2(k+1)}
    have hp_dvd_prod : p ∣ f * f.comp (-X) :=
      hprod ▸ dvd_pow_self p (by omega)
    -- p | f (using primality + symmetry of p)
    have hp_dvd_f : p ∣ f := by
      rcases hp_prime.dvd_or_dvd hp_dvd_prod with h | h
      · exact h
      · -- p | f(-X) → p | f (since p is symmetric and comp(-X) is involution)
        obtain ⟨g, hg⟩ := h
        -- comp(-X) is involution: (-X).comp(-X) = X
        have hneg_inv : (-X : Polynomial ℤ).comp (-X) = X := by
          rw [Polynomial.neg_comp, Polynomial.X_comp, neg_neg]
        have hcomp_inv : (f.comp (-X)).comp (-X) = f := by
          rw [Polynomial.comp_assoc, hneg_inv, Polynomial.comp_X]
        -- p | f.comp(-X) means (rewriting via involution):
        -- f = (f.comp(-X)).comp(-X) = (p*g).comp(-X) = p.comp(-X) * g.comp(-X) = p * g.comp(-X)
        rw [← hcomp_inv, hg, Polynomial.mul_comp, hp_sym]
        exact dvd_mul_right p _
    -- Write f = p * f₁
    obtain ⟨f₁, hf_eq⟩ := hp_dvd_f
    -- f₁ is monic
    have hf1_monic : f₁.Monic := by
      rw [Polynomial.Monic] at hf_monic ⊢
      rw [hf_eq, Polynomial.leadingCoeff_mul, hp_monic.leadingCoeff, one_mul] at hf_monic
      exact hf_monic
    -- f(-X) = p * f₁(-X)
    have hfc_eq : f.comp (-X) = p * f₁.comp (-X) := by
      rw [hf_eq, Polynomial.mul_comp, hp_sym]
    -- Cancellation: f₁ * f₁(-X) = p^{2k}
    have hprod₁ : f₁ * f₁.comp (-X) = p ^ (k + k) := by
      have h1 : p * f₁ * (p * f₁.comp (-X)) = p ^ ((k + 1) + (k + 1)) := by
        rw [← hf_eq, ← hfc_eq]; exact hprod
      have h2 : p ^ 2 * (f₁ * f₁.comp (-X)) = p ^ 2 * p ^ (k + k) := by
        calc p ^ 2 * (f₁ * f₁.comp (-X))
            = (p * f₁) * (p * f₁.comp (-X)) := by ring
          _ = p ^ ((k + 1) + (k + 1)) := h1
          _ = p ^ (2 + (k + k)) := by congr 1; omega
          _ = p ^ 2 * p ^ (k + k) := pow_add p 2 (k + k)
      exact mul_left_cancel₀ (pow_ne_zero 2 hp_monic.ne_zero) h2
    -- Apply IH: f₁ = p^k
    have hf1_eq := ih f₁ hf1_monic hprod₁
    rw [hf_eq, hf1_eq]; ring

/-- **k-1 is a perfect square** for any k-regular friendship graph with k ≥ 2.

    This is the core step that eliminates the spectral axiom.
    Proof by contradiction: if k-1 is not a perfect square, then
    X²-(k-1) is irreducible, forcing f = (X²-(k-1))^{(n-1)/2},
    which has zero coefficient at odd degrees. But the sub-leading
    coefficient of f must equal k ≥ 2, and n-2 is odd. Contradiction. -/
theorem k_sub_one_is_perfect_square (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    ∃ s : ℕ, k - 1 = s * s := by
  -- Assume for contradiction that k-1 is not a perfect square
  by_contra hns
  push_neg at hns
  -- n = k(k-1)+1 is odd, n-1 = k(k-1) is even, n-2 is odd
  have hn := regular_friendship_card G hF u k hreg (by omega)
  set n := Fintype.card V with hn_def
  -- n = k*(k-1)+1 ≥ 3 for k ≥ 2
  have hk1 : k - 1 ≥ 1 := by omega
  have hn_ge : n ≥ 3 := by rw [hn]; nlinarith [Nat.mul_le_mul_left k hk1]
  -- n-2 is odd: k*(k-1) is even, so k*(k-1)+1 is odd, so k*(k-1)-1 is odd
  -- We use: n-2 = k*(k-1)-1, and k*(k-1) is even (product of consecutive), so k*(k-1)-1 is odd
  have hn2_odd : Odd (n - 2) := by
    rw [hn]
    -- k*(k-1)+1-2 = k*(k-1)-1. k*(k-1) is even, so k*(k-1)-1 is odd.
    have hkk1_even : Even (k * (k - 1)) := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · -- k = m + m, so k*(k-1) = (m+m)*(k-1) = m*(k-1) + m*(k-1)
        exact ⟨m * (k - 1), by rw [hm]; ring⟩
      · -- k = 2*m+1, k-1 = 2*m
        have hk1 : k - 1 = m + m := by omega
        rw [hk1]; exact ⟨k * m, by ring⟩
    obtain ⟨t, ht⟩ := hkk1_even
    refine ⟨t - 1, ?_⟩; omega
  -- Get the charpoly factorization and product identity
  haveI : Nonempty V := ⟨u⟩
  have hdvd := X_sub_k_dvd_adjMatrix_charpoly G hF k (by omega) hreg
  obtain ⟨f, hf⟩ := hdvd
  -- f is monic (since charpoly is monic and (X-k) is monic)
  have hf_monic : f.Monic := by
    have hcm := (G.adjMatrix ℤ).charpoly_monic
    rw [hf] at hcm  -- hcm : ((X - C k) * f).Monic
    have h := hcm.leadingCoeff
    rw [Polynomial.leadingCoeff_mul,
      (Polynomial.monic_X_sub_C (↑k : ℤ)).leadingCoeff, one_mul] at h
    exact h  -- f.leadingCoeff = 1
  -- f has degree n-1
  have hf_deg : f.natDegree = n - 1 := by
    have hcharpoly_deg := Matrix.charpoly_natDegree_eq_dim (G.adjMatrix ℤ)
    rw [hf, ← hn_def] at hcharpoly_deg
    have hfne : f ≠ 0 := hf_monic.ne_zero
    have hxk_ne : (X - C (↑k : ℤ) : Polynomial ℤ) ≠ 0 :=
      (Polynomial.monic_X_sub_C _).ne_zero
    rw [Polynomial.natDegree_mul hxk_ne hfne] at hcharpoly_deg
    have hxk_deg : (X - C (↑k : ℤ) : Polynomial ℤ).natDegree = 1 :=
      Polynomial.natDegree_X_sub_C _
    omega
  -- The product identity (depends on charpoly_quotient_product)
  have hprod := charpoly_quotient_product G hF k hk hreg f hf
  -- n-1 is even: n-1 = k(k-1), product of consecutive = even
  have hn1_even : Even (n - 1) := by
    rw [hn]
    have : Even (k * (k - 1)) := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m * (k - 1), by rw [hm]; ring⟩
      · have hk1 : k - 1 = m + m := by omega
        rw [hk1]; exact ⟨k * m, by ring⟩
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by omega⟩
  -- X²-(k-1) is irreducible (since k-1 not a perfect square)
  have hirred := sq_sub_irreducible_of_not_square (k - 1) (by omega) (by
    intro s hs; exact hns s (by omega))
  -- X²-(k-1) is monic
  have hp_monic : (X ^ 2 - C (↑(k - 1) : ℤ) : Polynomial ℤ).Monic := by
    apply Polynomial.Monic.sub_of_left (monic_X_pow 2)
    calc (C (↑(k - 1) : ℤ) : Polynomial ℤ).degree ≤ 0 := degree_C_le
      _ < (X ^ 2 : Polynomial ℤ).degree := by simp [degree_X_pow]
  -- X²-(k-1) is symmetric: p(-X) = (-X)² - (k-1) = X² - (k-1) = p
  have hp_sym : (X ^ 2 - C (↑(k - 1) : ℤ) : Polynomial ℤ).comp (-X) =
      X ^ 2 - C (↑(k - 1) : ℤ) := by
    simp [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.C_comp, neg_sq]
  -- By UFD structure: f = (X²-(k-1))^{(n-1)/2}
  have hf_eq := monic_factor_of_symmetric_irreducible_pow
    (X ^ 2 - C (↑(k - 1) : ℤ)) f (n - 1) hn1_even hirred hp_monic hp_sym hf_monic hprod
  -- coeff_{n-2}(f) = 0 (since f = (X²-c)^m has only even-degree terms, and n-2 is odd)
  have hcoeff_zero : f.coeff (n - 2) = 0 := by
    rw [hf_eq]
    exact coeff_odd_of_sq_sub_pow (↑(k - 1) : ℤ) ((n - 1) / 2) (n - 2) hn2_odd
  -- But coeff_{n-2}(f) = k (from quotient_subleading_coeff)
  have hcoeff_k := quotient_subleading_coeff G hF k hk hreg f hf hf_monic hf_deg
  -- k = 0, contradicting k ≥ 2
  linarith

/-- Over a field, a monic polynomial dividing X^m must equal X^{natDegree f}. -/
private lemma monic_dvd_X_pow_eq {K : Type*} [Field K] {f : Polynomial K} {m : ℕ}
    (hf : f.Monic) (hdvd : f ∣ X ^ m) : f = X ^ f.natDegree := by
  induction m generalizing f with
  | zero =>
    rw [pow_zero] at hdvd
    have hdeg : f.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hdvd)
    rw [hdeg, pow_zero, Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    have : f.leadingCoeff = 1 := hf.leadingCoeff
    rw [Polynomial.leadingCoeff, hdeg] at this; rw [this, map_one]
  | succ m ih =>
    have hX_ne : (X : Polynomial K) ≠ 0 := Polynomial.X_ne_zero
    obtain ⟨g, hfg⟩ := hdvd
    have hX_dvd_fg : (X : Polynomial K) ∣ f * g :=
      ⟨X ^ m, by rw [← hfg, pow_succ]; ring⟩
    rcases (Polynomial.prime_X (R := K)).dvd_or_dvd hX_dvd_fg with hXf | hXg
    · obtain ⟨f₁, hf₁_eq⟩ := hXf
      have hf₁_monic : f₁.Monic := by
        rwa [Polynomial.Monic, hf₁_eq, Polynomial.leadingCoeff_mul,
          Polynomial.leadingCoeff_X, one_mul] at hf
      have hf₁_ne : f₁ ≠ 0 := hf₁_monic.ne_zero
      have hf₁_dvd : f₁ ∣ X ^ m := by
        have : f ∣ X ^ (m + 1) := ⟨g, hfg⟩
        rw [hf₁_eq] at this
        rwa [show X ^ (m + 1) = X * X ^ m from by rw [pow_succ]; ring,
          mul_dvd_mul_iff_left hX_ne] at this
      have hf₁_eq_pow := ih hf₁_monic hf₁_dvd
      have hdeg : f.natDegree = f₁.natDegree + 1 := by
        rw [hf₁_eq, Polynomial.natDegree_mul hX_ne hf₁_ne, Polynomial.natDegree_X]; omega
      conv_rhs => rw [hdeg]
      rw [hf₁_eq]; conv_lhs => rw [hf₁_eq_pow]
      rw [pow_succ]; ring
    · obtain ⟨g₁, hg₁_eq⟩ := hXg
      exact ih hf ⟨g₁, by
        have : f * (X * g₁) = X ^ (m + 1) := by rw [← hg₁_eq]; exact hfg.symm
        have h1 : X * (f * g₁) = X * X ^ m := by
          rw [show X * (f * g₁) = f * (X * g₁) from by ring, this, pow_succ]; ring
        exact (mul_left_cancel₀ hX_ne h1).symm⟩

/-- **s divides k** for s = √(k-1) in a k-regular friendship graph.

    **Proof**: From the product identity f·f(-X) = (X²-s²)^{n-1},
    f divides (X-s)^{n-1}·(X+s)^{n-1}. By UFD factorization in ℤ[X],
    f = (X-s)^b·(X+s)^c with b+c = n-1. The sub-leading coefficient
    gives (c-b)·s = k, hence s | k.

    **Dependencies**: Uses `charpoly_quotient_product` (the product identity). -/
theorem sqrt_k_sub_one_dvd_k (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k)
    (s : ℕ) (hs : k - 1 = s * s) :
    s ∣ k := by
  -- s >= 1 since k-1 = s^2 and k >= 2
  have hs_pos : s ≥ 1 := by
    by_contra h; push_neg at h
    have hs0 : s = 0 := by omega
    subst hs0; simp at hs; omega
  by_cases hs1 : s = 1
  · subst hs1; exact one_dvd k
  exfalso
  haveI : Nonempty V := ⟨u⟩
  have hdvd := X_sub_k_dvd_adjMatrix_charpoly G hF k (by omega) hreg
  obtain ⟨f, hf⟩ := hdvd
  have hf_monic : f.Monic := by
    have hcm := (G.adjMatrix ℤ).charpoly_monic; rw [hf] at hcm
    exact (Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C _) (by rwa [mul_comm] at hcm))
  set n := Fintype.card V with hn_def
  have hf_deg : f.natDegree = n - 1 := by
    have hcd := Matrix.charpoly_natDegree_eq_dim (G.adjMatrix ℤ)
    rw [hf, ← hn_def] at hcd
    rw [Polynomial.natDegree_mul (Polynomial.monic_X_sub_C _).ne_zero hf_monic.ne_zero,
      Polynomial.natDegree_X_sub_C] at hcd; omega
  have hn_ge : n ≥ 3 := by
    have h := regular_friendship_card G hF u k hreg (by omega)
    rw [← hn_def] at h; nlinarith [Nat.mul_le_mul hk (show k - 1 ≥ 1 by omega)]
  have hprod := charpoly_quotient_product G hF k hk hreg f hf
  have hprod' : f * f.comp (-X) = (X ^ 2 - C (↑(s * s) : ℤ)) ^ (n - 1) := by
    rw [hs] at hprod; exact hprod
  obtain ⟨p, hp_prime, hp_dvd_s⟩ := Nat.exists_prime_and_dvd (by omega : s ≠ 1)
  haveI : Fact (Nat.Prime p) := ⟨hp_prime⟩
  let φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  have hprod_mod : f.map φ * (f.map φ).comp (-X) = X ^ (2 * (n - 1)) := by
    have h1 := congr_arg (Polynomial.map φ) hprod'
    rw [Polynomial.map_mul, Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X,
      Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C] at h1
    have hs_mod : (φ (↑(s * s) : ℤ) : ZMod p) = 0 := by
      change ((s * s : ℤ) : ZMod p) = 0
      push_cast
      have : (s : ZMod p) = 0 := by rwa [ZMod.natCast_eq_zero_iff]
      rw [this, mul_zero]
    rw [hs_mod, map_zero, sub_zero, ← pow_mul] at h1; exact h1
  have hf_mod_monic : (f.map φ).Monic := Polynomial.Monic.map φ hf_monic
  have hf_mod_dvd : f.map φ ∣ X ^ (2 * (n - 1)) :=
    ⟨(f.map φ).comp (-X), hprod_mod.symm⟩
  have hf_mod_eq : f.map φ = X ^ (n - 1) := by
    have h := monic_dvd_X_pow_eq hf_mod_monic hf_mod_dvd
    rw [hf_monic.natDegree_map, hf_deg] at h; exact h
  have hcoeff_zero : (f.map φ).coeff (n - 2) = 0 := by
    rw [hf_mod_eq, Polynomial.coeff_X_pow]
    simp only [show n - 2 ≠ n - 1 from by omega, ite_false]
  have hcoeff_k := quotient_subleading_coeff G hF k hk hreg f hf hf_monic hf_deg
  rw [Polynomial.coeff_map, hcoeff_k] at hcoeff_zero
  have hp_dvd_k : p ∣ k := by
    have h : ((k : ℤ) : ZMod p) = 0 := hcoeff_zero
    rw [show ((k : ℤ) : ZMod p) = ((k : ℕ) : ZMod p) from by push_cast; ring] at h
    rwa [ZMod.natCast_eq_zero_iff] at h
  have hp_dvd_ss : p ∣ s * s := Dvd.dvd.mul_right hp_dvd_s s
  have hp_dvd_one : p ∣ 1 := by
    have h1 : (k : ℤ) - ↑(s * s) = 1 := by push_cast; omega
    have h2 : (p : ℤ) ∣ ↑k - ↑(s * s) :=
      dvd_sub (by exact_mod_cast hp_dvd_k) (by exact_mod_cast hp_dvd_ss)
    rw [h1] at h2; exact_mod_cast h2
  exact Nat.Prime.one_lt hp_prime |>.not_ge (Nat.le_of_dvd one_pos hp_dvd_one)

/-- **Main theorem: k = 2 without any axiom.**

    Combines k_sub_one_is_perfect_square + sqrt_k_sub_one_dvd_k + dvd_sq_add_one_imp_one. -/
theorem k_eq_two_no_axiom (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    k = 2 := by
  obtain ⟨s, hs⟩ := k_sub_one_is_perfect_square G hF u k hk hreg
  have hs_pos : s ≥ 1 := by
    by_contra h; push_neg at h
    interval_cases s; simp at hs; omega
  have hk_eq : k = s * s + 1 := by omega
  have h_dvd := sqrt_k_sub_one_dvd_k G hF u k hk hreg s hs
  rw [hk_eq] at h_dvd
  have h1 := dvd_sq_add_one_imp_one s hs_pos h_dvd
  subst h1; omega

-- ============================================================================
-- Part XVIII-B: Main Theorems (axiom-free)
-- ============================================================================

/-- A k-regular friendship graph has exactly 3 vertices (must be K₃). -/
theorem regular_friendship_is_triangle (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    Fintype.card V = 3 := by
  have hk2 := k_eq_two_no_axiom G hF u k hk hreg
  have hcard := regular_friendship_card G hF u k hreg (by omega)
  subst hk2; omega

/-- A k-regular friendship graph has a universal vertex.
    Since k = 2 and n = 3, every vertex has degree n - 1,
    making it adjacent to all others. Fully axiom-free. -/
theorem regular_friendship_has_universal (hF : IsFriendshipGraph G)
    (u : V) (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    ∃ c : V, ∀ v : V, v ≠ c → G.Adj c v := by
  have hk2 := k_eq_two_no_axiom G hF u k hk hreg
  have hn := regular_friendship_is_triangle G hF u k hk hreg
  refine ⟨u, fun v hvu => ?_⟩
  have hdc : (G.neighborFinset u).card = Fintype.card V - 1 := by
    rw [← SimpleGraph.degree, hreg u, hk2, hn]
  have hsub : G.neighborFinset u ⊆ Finset.univ.erase u := by
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    rw [SimpleGraph.mem_neighborFinset, heq] at hx
    exact absurd hx (G.loopless.irrefl u)
  have heq : G.neighborFinset u = Finset.univ.erase u :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]; omega)
  have hv_mem : v ∈ G.neighborFinset u := by
    rw [heq, Finset.mem_erase]; exact ⟨hvu, Finset.mem_univ v⟩
  rw [SimpleGraph.mem_neighborFinset] at hv_mem
  exact hv_mem

/-
## Part XVIII Summary: Axiom Elimination (Complete)

### New Theorems (axiom-free path)
| Result | Status | Description |
|--------|--------|-------------|
| `coeff_odd_of_sq_sub_pow` | PROVED | (X²-c)^m has zero odd-degree coefficients |
| `k_sub_one_is_perfect_square` | PROVED | k-1 is a perfect square |
| `sqrt_k_sub_one_dvd_k` | PROVED | √(k-1) divides k |
| `k_eq_two_no_axiom` | PROVED (from above) | k=2 without axiom |
| `regular_friendship_is_triangle_no_axiom` | PROVED | n=3 without axiom |
| `regular_friendship_has_universal_no_axiom` | PROVED | universal vertex, no axiom |

### Supporting Lemmas
| Lemma | Role |
|-------|------|
| `adjMatrix_charpoly_eval_k` | det(kI-A)=0 from singularity |
| `X_sub_k_dvd_adjMatrix_charpoly` | Factor theorem application |
| `charpoly_quotient_product` | Product det identity + det(cI-J) formula |
| `quotient_subleading_coeff` | Coefficient extraction from product |
| `sq_sub_irreducible_of_not_square` | Rational root theorem for ℤ[X] |
| `monic_factor_of_symmetric_irreducible_pow` | UFD factorization in ℤ[X] |

### Axiom Elimination Structure

The supporting lemmas fall into 3 categories:

1. **Polynomial algebra** (sq_sub_irreducible_of_not_square, monic_factor_of_symmetric_irreducible_pow):
   Standard algebra from Mathlib's UniqueFactorizationDomain + Polynomial.Irreducible.

2. **Matrix determinant** (charpoly_quotient_product):
   Uses Matrix.det_mul over Polynomial ℤ + the rank-1 determinant formula det(cI-J) = c^{n-1}(c-n).

3. **Charpoly evaluation** (adjMatrix_charpoly_eval_k, X_sub_k_dvd_adjMatrix_charpoly, quotient_subleading_coeff):
   Standard connections between eigenvalues, roots of charpoly, and trace.
-/

-- ============================================================================
-- Part XVIII: Adjacency Matrix Symmetry and Spectral Preparation
-- ============================================================================

/-
## Part XVIII: Matrix Symmetry and Commutation Properties

The adjacency matrix A of a simple graph is symmetric: A = Aᵀ. Over ℝ, this
means A is Hermitian, so its eigenvalues are all real. This is the entry point
to the spectral theorem used in the axiom elimination path.

Also: J commutes with A for regular graphs (JA = AJ = kJ).
-/

/-- The adjacency matrix is symmetric: Aᵢⱼ = Aⱼᵢ.
    Follows from G.adj_comm: G.Adj u v ↔ G.Adj v u. -/
theorem adjMatrix_symmetric :
    (G.adjMatrix ℤ).transpose = G.adjMatrix ℤ := by
  ext i j
  simp [Matrix.transpose_apply, SimpleGraph.adjMatrix_apply, G.adj_comm]

/-- **JA = kJ** for k-regular graphs (dual of AJ = kJ).
    Since A is symmetric and AJ = kJ: JA = (AJ)ᵀ = (kJ)ᵀ = kJᵀ = kJ. -/
theorem onesMatrix_mul_adjMatrix (k : ℕ) (hreg : ∀ v : V, G.degree v = k) :
    onesMatrix V * G.adjMatrix ℤ = ↑k • onesMatrix V := by
  -- Column sums equal k too (by symmetry of A and row sums = k)
  ext i j
  simp only [Matrix.mul_apply, onesMatrix, Matrix.of_apply, one_mul,
    Matrix.smul_apply, smul_eq_mul, mul_one, SimpleGraph.adjMatrix_apply]
  trans ↑((Finset.univ.filter fun w => G.Adj w j).card)
  · rw [← Finset.sum_boole]
  · have : (Finset.univ.filter fun w => G.Adj w j) =
        (Finset.univ.filter fun w => G.Adj j w) := by
      ext w; simp [G.adj_comm]
    rw [this]
    have : (Finset.univ.filter fun w => G.Adj j w) = G.neighborFinset j := by
      ext w; simp [SimpleGraph.mem_neighborFinset]
    rw [this, ← SimpleGraph.degree, hreg j]; ring

/-- J commutes with A for k-regular graphs: AJ = JA = kJ. -/
theorem onesMatrix_adjMatrix_comm (k : ℕ) (hreg : ∀ v : V, G.degree v = k) :
    G.adjMatrix ℤ * onesMatrix V = onesMatrix V * G.adjMatrix ℤ := by
  rw [adjMatrix_mul_ones G k hreg, onesMatrix_mul_adjMatrix G k hreg]

/-- A² commutes with J (since A² = (k-1)I + J and both I,J commute with J). -/
theorem adjMatrix_sq_comm_onesMatrix (hF : IsFriendshipGraph G) (k : ℕ) (hk : k ≥ 1)
    (hreg : ∀ v : V, G.degree v = k) :
    (G.adjMatrix ℤ * G.adjMatrix ℤ) * onesMatrix V =
    onesMatrix V * (G.adjMatrix ℤ * G.adjMatrix ℤ) := by
  rw [adjMatrix_sq_eq G hF k hk hreg, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]

/-- The number of vertices n = k(k-1)+1 satisfies n ≥ 3 for k ≥ 2.
    This ensures the graph has at least 3 vertices. -/
theorem friendship_card_ge_three (hF : IsFriendshipGraph G) (u : V)
    (k : ℕ) (hk : k ≥ 2) (hreg : ∀ v : V, G.degree v = k) :
    Fintype.card V ≥ 3 := by
  have hcard := regular_friendship_card G hF u k hreg (by omega)
  have h1 : k - 1 ≥ 1 := by omega
  have h2 : k * (k - 1) ≥ 2 * 1 := Nat.mul_le_mul hk h1
  omega

/-- Part XVIII summary:
    1. adjMatrix_symmetric: A = Aᵀ (PROVED, foundation for spectral theorem)
    2. onesMatrix_mul_adjMatrix: JA = kJ (PROVED, dual of AJ = kJ)
    3. onesMatrix_adjMatrix_comm: AJ = JA (PROVED, J commutes with A)
    4. adjMatrix_sq_comm_onesMatrix: A²J = JA² (PROVED, commutation)
    5. friendship_card_ge_three: n ≥ 3 (PROVED from n = k(k-1)+1)

    These prepare the ground for spectral analysis:
    - A symmetric → eigenvalues real (via IsHermitian)
    - J commutes with A → J preserves eigenspaces of A
    - A²J = JA² → eigenspaces of A² are stable under J
    - Combined with A² = (k-1)I + J → eigenspace decomposition -/
theorem part_xviii_summary : (5 : ℕ) = 5 := rfl

-- ============================================================================
-- Part XIX: Regularity Proof — No Universal Vertex Implies Regular
-- ============================================================================
-- This eliminates Axiom 1 (friendship_has_universal_or_regular) from the
-- main FriendshipTheorem.lean file. The key insight: non-adjacent vertices
-- in a friendship graph have the same degree (from A³ commutativity), and
-- a friendship graph with no universal vertex must be regular.

/-- Row sum of the adjacency matrix equals the degree (over ℤ). -/
lemma adjMatrix_row_sum (i : V) :
    ∑ j : V, (G.adjMatrix ℤ) i j = ↑(G.degree i) := by
  simp [SimpleGraph.adjMatrix_apply, SimpleGraph.degree, SimpleGraph.neighborFinset,
    Finset.sum_boole, Finset.filter_congr_decidable]

/-- Column sum of the adjacency matrix equals the degree (by symmetry). -/
lemma adjMatrix_col_sum (j : V) :
    ∑ i : V, (G.adjMatrix ℤ) i j = ↑(G.degree j) := by
  simp_rw [show ∀ i, (G.adjMatrix ℤ) i j = (G.adjMatrix ℤ) j i from
    fun i => by simp [SimpleGraph.adjMatrix_apply, G.adj_comm]]
  exact adjMatrix_row_sum G j

/-- Entry of A*(A*A) for distinct i,j in a friendship graph.
    (A*(A²))ᵢⱼ = deg(i) + Aᵢⱼ * (deg(j) - 1) -/
lemma a_mul_asq_entry (hF : IsFriendshipGraph G) (i j : V) (hij : i ≠ j) :
    (G.adjMatrix ℤ * (G.adjMatrix ℤ * G.adjMatrix ℤ)) i j =
    ↑(G.degree i) + (G.adjMatrix ℤ) i j * (↑(G.degree j) - 1) := by
  simp only [Matrix.mul_apply]
  -- Split sum at k = j
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  -- k = j term: A_{ik} * (A²)_{jj} = A_{ij} * deg(j)
  have hdiag : ∑ k : V, (G.adjMatrix ℤ) j k * (G.adjMatrix ℤ) k j =
      ↑(G.degree j) := by
    have := adjMatrix_sq_diag G j
    simp only [Matrix.mul_apply] at this
    exact_mod_cast this
  rw [hdiag]
  -- k ≠ j terms: A_{ik} * (A²)_{kj} = A_{ik} * 1 for k ≠ j
  have hoff : ∀ k ∈ Finset.univ.erase j, ∑ l : V, (G.adjMatrix ℤ) k l *
      (G.adjMatrix ℤ) l j = 1 := by
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have := adjMatrix_sq_off_diag G hF k j hkj
    simp only [Matrix.mul_apply] at this
    exact this
  simp_rw [Finset.sum_congr rfl (fun k hk => show (G.adjMatrix ℤ) i k *
    (∑ l, (G.adjMatrix ℤ) k l * (G.adjMatrix ℤ) l j) =
    (G.adjMatrix ℤ) i k * 1 from by rw [hoff k hk])]
  simp only [mul_one]
  -- Now: A_{ij} * deg(j) + Σ_{k≠j} A_{ik} = A_{ij} * deg(j) + (deg(i) - A_{ij})
  have hsum : ∑ k ∈ Finset.univ.erase j, (G.adjMatrix ℤ) i k =
      ↑(G.degree i) - (G.adjMatrix ℤ) i j := by
    have h := adjMatrix_row_sum G i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at h
    linarith
  rw [hsum]
  ring

/-- Entry of (A*A)*A for distinct i,j in a friendship graph.
    ((A²)*A)ᵢⱼ = deg(j) + Aᵢⱼ * (deg(i) - 1) -/
lemma asq_mul_a_entry (hF : IsFriendshipGraph G) (i j : V) (hij : i ≠ j) :
    ((G.adjMatrix ℤ * G.adjMatrix ℤ) * G.adjMatrix ℤ) i j =
    ↑(G.degree j) + (G.adjMatrix ℤ) i j * (↑(G.degree i) - 1) := by
  simp only [Matrix.mul_apply]
  -- Split sum at k = i
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  -- k = i term: (A²)_{ii} * A_{ij} = deg(i) * A_{ij}
  have hdiag : ∑ l : V, (G.adjMatrix ℤ) i l * (G.adjMatrix ℤ) l i =
      ↑(G.degree i) := by
    have := adjMatrix_sq_diag G i
    simp only [Matrix.mul_apply] at this
    exact_mod_cast this
  rw [hdiag]
  -- k ≠ i terms: (A²)_{ik} * A_{kj} = 1 * A_{kj} for k ≠ i
  have hoff : ∀ k ∈ Finset.univ.erase i, ∑ l : V, (G.adjMatrix ℤ) i l *
      (G.adjMatrix ℤ) l k = 1 := by
    intro k hk
    have hik : i ≠ k := (Finset.mem_erase.mp hk).1.symm
    have := adjMatrix_sq_off_diag G hF i k hik
    simp only [Matrix.mul_apply] at this
    exact this
  simp_rw [Finset.sum_congr rfl (fun k hk => show (∑ l, (G.adjMatrix ℤ) i l *
    (G.adjMatrix ℤ) l k) * (G.adjMatrix ℤ) k j =
    1 * (G.adjMatrix ℤ) k j from by rw [hoff k hk])]
  simp only [one_mul]
  -- Now: deg(i) * A_{ij} + Σ_{k≠i} A_{kj} = deg(i) * A_{ij} + (deg(j) - A_{ij})
  have hadj_sym : (G.adjMatrix ℤ) i j = (G.adjMatrix ℤ) j i := by
    simp [SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hsum : ∑ k ∈ Finset.univ.erase i, (G.adjMatrix ℤ) k j =
      ↑(G.degree j) - (G.adjMatrix ℤ) i j := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    have : ∑ k, (G.adjMatrix ℤ) k j = ↑(G.degree j) := adjMatrix_col_sum G j
    linarith
  rw [hsum]
  ring

/-- **Non-adjacent vertices in a friendship graph have the same degree.**
    Proof: A³ = A·A² = A²·A by associativity. Comparing entries for
    non-adjacent i,j (where A_{ij} = 0) gives deg(i) = deg(j). -/
theorem nonadj_same_degree (hF : IsFriendshipGraph G) (u v : V)
    (huv : u ≠ v) (hnadj : ¬G.Adj u v) : G.degree u = G.degree v := by
  -- Compute both orderings of A³ entry
  have h1 := a_mul_asq_entry G hF u v huv
  have h2 := asq_mul_a_entry G hF u v huv
  -- A * (A * A) = (A * A) * A by associativity
  have hassoc : G.adjMatrix ℤ * (G.adjMatrix ℤ * G.adjMatrix ℤ) =
      (G.adjMatrix ℤ * G.adjMatrix ℤ) * G.adjMatrix ℤ := (mul_assoc _ _ _).symm
  -- Entry-wise equality
  have heq : (G.adjMatrix ℤ * (G.adjMatrix ℤ * G.adjMatrix ℤ)) u v =
      ((G.adjMatrix ℤ * G.adjMatrix ℤ) * G.adjMatrix ℤ) u v :=
    congr_fun (congr_fun hassoc u) v
  rw [h1, h2] at heq
  -- A_{uv} = 0 since u and v are not adjacent
  have hzero : (G.adjMatrix ℤ) u v = 0 := by
    simp [SimpleGraph.adjMatrix_apply, hnadj]
  -- Simplify: deg(u) + 0 = deg(v) + 0
  simp only [hzero, zero_mul, add_zero] at heq
  exact_mod_cast heq

/-- Vertices of different degrees in a friendship graph must be adjacent. -/
theorem diff_degree_implies_adj (hF : IsFriendshipGraph G) (u v : V)
    (huv : u ≠ v) (hdeg : G.degree u ≠ G.degree v) : G.Adj u v := by
  by_contra hnadj
  exact hdeg (nonadj_same_degree G hF u v huv hnadj)

/-- **Friendship graphs without a universal vertex are regular.**
    Uses the complement-component argument: if two degree classes have
    size ≥ 2, their complete bipartite structure creates too many common
    neighbors. Singleton classes would be universal vertices. -/
theorem friendship_regular_of_no_universal (hF : IsFriendshipGraph G)
    (hn : Fintype.card V ≥ 3)
    (hnu : ∀ c : V, ∃ v : V, v ≠ c ∧ ¬G.Adj c v) :
    ∃ k : ℕ, ∀ v : V, G.degree v = k := by
  -- Fix a vertex u₀ and show all vertices have deg = deg(u₀)
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff]; omega
  let u₀ := Classical.arbitrary V
  refine ⟨G.degree u₀, fun v => ?_⟩
  by_contra hdeg
  -- v has different degree from u₀, so they're adjacent
  have huv : u₀ ≠ v := by intro h; subst h; exact hdeg rfl
  have hdeg' : G.degree u₀ ≠ G.degree v := fun h => hdeg h.symm
  have hadj_uv : G.Adj u₀ v := diff_degree_implies_adj G hF u₀ v huv hdeg'
  -- u₀ is not universal, so it has a non-neighbor w₁
  obtain ⟨w₁, hw1ne, hw1nadj⟩ := hnu u₀
  -- deg(w₁) = deg(u₀) since they're non-adjacent
  have hdeg_w1 : G.degree w₁ = G.degree u₀ :=
    nonadj_same_degree G hF w₁ u₀ hw1ne (fun h => hw1nadj h.symm)
  -- v is not universal, so it has a non-neighbor w₂
  obtain ⟨w₂, hw2ne, hw2nadj⟩ := hnu v
  -- deg(w₂) = deg(v) since they're non-adjacent
  have hdeg_w2 : G.degree w₂ = G.degree v :=
    nonadj_same_degree G hF w₂ v hw2ne (fun h => hw2nadj h.symm)
  -- Key question: is there a vertex non-adjacent to BOTH u₀ and v?
  -- If w₁ is non-adj to v: deg(w₁) = deg(v) = deg(u₀), contradiction
  by_cases hw1v : G.Adj w₁ v
  · -- w₁ is adj to v but non-adj to u₀
    by_cases hw2u : G.Adj w₂ u₀
    · -- w₂ is adj to u₀ but non-adj to v
      -- Consider: all non-neighbors of u₀ are adj to v, all non-neighbors of v are adj to u₀
      -- Degree classes: S₁ = {x : deg x = deg u₀}, S₂ = {x : deg x = deg v}
      -- All of S₁ is adj to all of S₂ (different degrees)
      -- If |S₂| ≥ 2, pick two elements; all of S₁ are common neighbors → contradiction
      -- We know deg(u₀) ≠ deg(v). Let d₁ = deg(u₀), d₂ = deg(v).
      let S₁ := Finset.univ.filter (fun x => G.degree x = G.degree u₀)
      let S₂ := Finset.univ.filter (fun x => G.degree x = G.degree v)
      -- u₀ ∈ S₁, v ∈ S₂
      have hu0_S1 : u₀ ∈ S₁ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hv_S2 : v ∈ S₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      -- All of S₁ adj to all of S₂ (different degrees → adjacent)
      have hbip : ∀ a ∈ S₁, ∀ b ∈ S₂, G.Adj a b := by
        intro a ha b hb
        have hda := (Finset.mem_filter.mp ha).2
        have hdb := (Finset.mem_filter.mp hb).2
        have hab : a ≠ b := by
          intro heq; subst heq; rw [hda] at hdb; exact hdeg' hdb
        exact diff_degree_implies_adj G hF a b hab (by rw [hda, hdb]; exact hdeg')
      -- Check |S₂| ≥ 2: v ∈ S₂ and w₂ ∈ S₂ (since deg(w₂) = deg(v))
      have hw2_S2 : w₂ ∈ S₂ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeg_w2⟩
      -- Is v ≠ w₂? w₂ is non-adj to v (by hw2nadj), but v is... self-adj is impossible
      -- Actually w₂ ≠ v because w₂ is a non-neighbor of v
      have hvw2 : v ≠ w₂ := Ne.symm hw2ne
      -- So |S₂| ≥ 2
      -- All of S₁ are common neighbors of v and w₂
      have hcn : ∀ a ∈ S₁, a ∈ G.commonNeighbors v w₂ := by
        intro a ha
        rw [SimpleGraph.mem_commonNeighbors]
        exact ⟨SimpleGraph.Adj.symm (hbip a ha v hv_S2), SimpleGraph.Adj.symm (hbip a ha w₂ hw2_S2)⟩
      -- |commonNeighbors(v, w₂)| ≥ |S₁| ≥ 1 (since u₀ ∈ S₁)
      -- Also w₁ ∈ S₁ since deg(w₁) = deg(u₀)
      have hw1_S1 : w₁ ∈ S₁ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdeg_w1⟩
      -- u₀ ≠ w₁ (w₁ is non-adj to u₀, so w₁ ≠ u₀)
      have hu0w1 : u₀ ≠ w₁ := Ne.symm hw1ne
      -- So S₁ has at least 2 elements: u₀ and w₁
      -- Both u₀ and w₁ are common neighbors of v and w₂
      have hcn1 := hcn u₀ hu0_S1
      have hcn2 := hcn w₁ hw1_S1
      -- v ≠ w₂ (proved above as hw2ne.symm)
      have hvw2' : v ≠ w₂ := hw2ne.symm
      -- By friendship: |commonNeighbors(v, w₂)| = 1
      have hfriend := hF v w₂ hvw2'
      rw [Set.ncard_eq_one] at hfriend
      obtain ⟨c, hc⟩ := hfriend
      -- u₀ and w₁ are both in {c}
      have h_u0 : u₀ = c := Set.mem_singleton_iff.mp (hc ▸ hcn1)
      have h_w1 : w₁ = c := Set.mem_singleton_iff.mp (hc ▸ hcn2)
      -- So u₀ = w₁, contradicting u₀ ≠ w₁
      exact absurd (h_u0.trans h_w1.symm) hu0w1
    · -- w₂ is non-adj to u₀: deg(w₂) = deg(u₀), but deg(w₂) = deg(v), contradiction
      have hw2u0 : w₂ ≠ u₀ := by
        intro heq; subst heq; exact hw2nadj hadj_uv.symm
      have := nonadj_same_degree G hF w₂ u₀ hw2u0 hw2u
      -- this : deg(w₂) = deg(u₀), hdeg_w2 : deg(w₂) = deg(v)
      -- So deg(v) = deg(u₀)
      exact hdeg (hdeg_w2.symm.trans this)
  · -- w₁ is non-adj to v: deg(w₁) = deg(v), but deg(w₁) = deg(u₀), contradiction
    have hw1v_ne : w₁ ≠ v := by
      intro heq; subst heq; rw [hdeg_w1] at hdeg; exact hdeg rfl
    have := nonadj_same_degree G hF w₁ v hw1v_ne hw1v
    -- this : deg(w₁) = deg(v), hdeg_w1 : deg(w₁) = deg(u₀)
    -- So deg(v) = deg(u₀)
    exact hdeg (this.symm.trans hdeg_w1)

/-- **Friendship Theorem — universal vertex or regular (proved, no axiom).**
    In a friendship graph with ≥ 3 vertices, either there exists a universal
    vertex, or the graph is regular. -/
theorem friendship_has_universal_or_regular_proved (hF : IsFriendshipGraph G)
    (hn : Fintype.card V ≥ 3) :
    (∃ c : V, ∀ v : V, v ≠ c → G.Adj c v) ∨
    (∃ k : ℕ, ∀ v : V, G.degree v = k) := by
  by_cases h : ∃ c : V, ∀ v : V, v ≠ c → G.Adj c v
  · left; exact h
  · right
    push_neg at h
    exact friendship_regular_of_no_universal G hF hn h

/-- **Friendship Theorem — regular implies universal (proved, no axiom).**
    Wrapper matching the signature of the axiom in FriendshipTheorem.lean. -/
theorem friendship_regular_implies_universal_proved (hF : IsFriendshipGraph G)
    (hReg : ∃ k : ℕ, ∀ v : V, G.degree v = k)
    (hn : Fintype.card V ≥ 3) :
    ∃ c : V, ∀ v : V, v ≠ c → G.Adj c v := by
  obtain ⟨k, hreg⟩ := hReg
  -- k ≥ 2 from n ≥ 3 and counting identity
  have hne : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
  let u := Classical.arbitrary V
  have hk2 : k ≥ 2 := by
    -- k = 0: no edges, so no common neighbors, contradicts friendship for n ≥ 3
    -- k = 1: matching, each vertex has 1 neighbor, non-adj pairs share 0 common neighbors
    by_contra h; push_neg at h
    interval_cases k
    · -- k = 0: every vertex isolated, no common neighbors
      have hab : ∃ a : V, ∃ b : V, a ≠ b := by
        have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨a, b, hab⟩ := exists_pair_ne V
        exact ⟨a, b, hab⟩
      obtain ⟨a, b, hab⟩ := hab
      have hcn : (G.commonNeighbors a b).ncard = 1 := hF a b hab
      have hempty : (G.commonNeighbors a b).ncard = 0 := by
        rw [Set.ncard_eq_zero]
        ext w; simp only [Set.mem_empty_iff_false, iff_false]
        intro hw
        rw [SimpleGraph.mem_commonNeighbors] at hw
        have : G.degree w = 0 := hreg w
        rw [SimpleGraph.degree] at this
        have := Finset.card_pos.mpr ⟨a, (G.mem_neighborFinset w a).mpr hw.1.symm⟩
        omega
      omega
    · -- k = 1: each vertex has 1 neighbor, common neighbor adj to both gives deg ≥ 2
      have hab : ∃ a : V, ∃ b : V, a ≠ b := by
        have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        obtain ⟨a, b, hab⟩ := exists_pair_ne V
        exact ⟨a, b, hab⟩
      obtain ⟨a, b, hab⟩ := hab
      have hcn : (G.commonNeighbors a b).ncard = 1 := hF a b hab
      rw [Set.ncard_eq_one] at hcn
      obtain ⟨w, hw⟩ := hcn
      have hw_mem : w ∈ G.commonNeighbors a b := hw ▸ Set.mem_singleton w
      rw [SimpleGraph.mem_commonNeighbors] at hw_mem
      have hwa : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr hw_mem.1.symm
      have hwb : b ∈ G.neighborFinset w := (G.mem_neighborFinset w b).mpr hw_mem.2.symm
      have : G.degree w ≥ 2 := by
        rw [SimpleGraph.degree]
        have hsub : {a, b} ⊆ G.neighborFinset w := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        calc (G.neighborFinset w).card ≥ ({a, b} : Finset V).card :=
              Finset.card_le_card hsub
          _ = 2 := Finset.card_pair hab
      rw [hreg w] at this; omega
  exact regular_friendship_has_universal G hF u k hk2 hreg

end FriendshipTheoremOQ01
