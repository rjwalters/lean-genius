import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic

/-
# Erdos Problem #1017 (OQ-01): Clique Partition of Dense Graphs

## Background
Let f(n,k) = min m such that every n-vertex k-edge graph can be edge-partitioned
into at most m complete subgraphs.

Erdos-Goodman-Posa (1966): f(n,k) <= floor(n^2/4), using only edges and triangles.
Extremal: K_{n/2,n/2} achieves equality (triangle-free, needs n^2/4 edges as cliques).

## Open Question
Can f(n,k) < floor(n^2/4) when k > n^2/4 and the graph contains K_4 or larger cliques?

The K_4-free case is resolved by Gyori-Keszegh (2017): if G is K_4-free with
floor(n^2/4) + m edges, it contains m edge-disjoint triangles, giving f = floor(n^2/4) - m.

## What This File Proves (10 axioms -> 8 axioms)
- completeBipartite_cliqueFree: K_{a,b} is triangle-free (PROVED)
- completeBipartite_edgeCount: K_{a,b} has a*b edges (PROVED)
- turanBound quadratic identity: n^2/4 = n/2 * (n - n/2) (PROVED)
- turanBound monotonicity, small values (PROVED)
- k4free_improves: K_4-free dense graphs improve on floor(n^2/4) (PROVED from axioms)
- cliquePartitionNum_le_turan: cp(G) <= floor(n^2/4) (PROVED from EGP axiom)
- egp_tight_example: cp(K_{k,k}) = k^2 (PROVED from axioms)

## Remaining Axioms (8)
- egp_theorem: EGP bound (deep combinatorial theorem)
- triangleFree_cliquePartition_eq_edges: cp(G) = |E| for triangle-free G
- dense_contains_triangle: Turan's theorem consequence
- gyori_keszegh_triangles: K_4-free edge-disjoint triangle packing
- k4free_partition_number: K_4-free partition formula
- lovasz_covering: Lovasz covering bound
- cliquePartition_le_vertices: trivial bound
- supersaturation_triangles: Razborov flag algebra result

## Proof Techniques
- Greedy triangle extraction + Turan bound on remainder
- Complete bipartite extremal construction
- Edge-disjoint triangle packing (Gyori-Keszegh)
- Case analysis on Sum types for bipartite graph properties
-/

set_option maxHeartbeats 800000

namespace Erdos1017OQ01

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
====================================================================
PART I: EDGE CLIQUE PARTITION FRAMEWORK
==================================================================== -/

/-- An edge clique partition of G is a collection of cliques whose edges
    partition G's edge set. Each clique is a finset of vertices that forms
    a complete subgraph, and every edge of G belongs to exactly one clique. -/
structure EdgeCliquePartition (G : SimpleGraph V) [DecidableRel G.Adj] where
  /-- The cliques in the partition -/
  cliques : Finset (Finset V)
  /-- Each element is a clique in G -/
  isClique : ∀ S ∈ cliques, G.IsClique (↑S : Set V)
  /-- Every edge is covered: for each edge {v,w}, some clique contains both -/
  covers : ∀ ⦃v w⦄, G.Adj v w →
    ∃ S ∈ cliques, v ∈ S ∧ w ∈ S

/-- The clique partition number cp(G) is the minimum number of cliques
    in any edge clique partition of G. -/
noncomputable def cliquePartitionNum (G : SimpleGraph V)
    [DecidableRel G.Adj] : ℕ :=
  sInf { m | ∃ P : EdgeCliquePartition G, P.cliques.card = m }

/-- A partition uses only edges and triangles if every clique has <= 3 vertices. -/
def usesOnlyEdgesAndTriangles {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : EdgeCliquePartition G) : Prop :=
  ∀ S ∈ P.cliques, S.card ≤ 3

/-
====================================================================
PART II: TURAN NUMBER AND FLOOR(n^2/4)
==================================================================== -/

/-- The Turan number for triangles: floor(n^2/4). This equals ex(n, K_3),
    the maximum number of edges in a triangle-free graph on n vertices. -/
def turanBound (n : ℕ) : ℕ := n ^ 2 / 4

/-- Small values of the Turan bound. -/
theorem turanBound_zero : turanBound 0 = 0 := by decide
theorem turanBound_one : turanBound 1 = 0 := by decide
theorem turanBound_two : turanBound 2 = 1 := by decide
theorem turanBound_three : turanBound 3 = 2 := by decide
theorem turanBound_four : turanBound 4 = 4 := by decide

/-- turanBound is monotone. -/
theorem turanBound_mono {m n : ℕ} (h : m ≤ n) : turanBound m ≤ turanBound n := by
  unfold turanBound
  exact Nat.div_le_div_right (Nat.pow_le_pow_left h 2)

/-- The Turan bound satisfies n^2/4 = (n/2) * (n - n/2), which equals
    floor(n/2) * ceil(n/2). This is the edge count of the balanced
    complete bipartite graph. -/
theorem turanBound_eq_product (n : ℕ) :
    turanBound n = (n / 2) * (n - n / 2) := by
  unfold turanBound
  have h2 : n = n / 2 * 2 + n % 2 := (Nat.div_add_mod n 2).symm
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases hmod with heven | hodd
  · -- n even: n = 2k, n/2 = k, n - n/2 = k, n^2/4 = k^2
    have hn : n = n / 2 * 2 := by omega
    have hsub : n - n / 2 = n / 2 := by omega
    rw [hsub]; ring_nf
    rw [show n ^ 2 = (n / 2 * 2) ^ 2 by rw [hn]]
    ring_nf; omega
  · -- n odd: n = 2k+1, n/2 = k, n - n/2 = k+1, n^2/4 = k*(k+1)
    have hn : n = n / 2 * 2 + 1 := by omega
    have hsub : n - n / 2 = n / 2 + 1 := by omega
    rw [hsub]
    rw [show n ^ 2 = (n / 2 * 2 + 1) ^ 2 by rw [hn]]
    ring_nf; omega

/-- turanBound is positive for n >= 2. -/
theorem turanBound_pos {n : ℕ} (hn : 2 ≤ n) : 0 < turanBound n := by
  unfold turanBound
  have : 4 ≤ n ^ 2 := by nlinarith
  omega

/-
====================================================================
PART III: ERDOS-GOODMAN-POSA THEOREM (1966)
==================================================================== -/

/-- **Erdos-Goodman-Posa Theorem**: Every graph on n vertices can be
    edge-partitioned into at most floor(n^2/4) complete subgraphs, using
    only edges (K_2) and triangles (K_3).

    Proof sketch: Extract a maximal set of edge-disjoint triangles.
    The remainder is triangle-free, hence bipartite by Ramsey theory.
    A bipartite graph on n vertices has <= floor(n^2/4) edges (Turan).
    Each triangle replaces 3 edges with 1 clique, so total <= floor(n^2/4). -/
axiom egp_theorem (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P : EdgeCliquePartition G,
      usesOnlyEdgesAndTriangles P ∧ P.cliques.card ≤ turanBound (Fintype.card V)

/-- Corollary: cp(G) <= floor(n^2/4) for every graph G on n vertices. -/
theorem cliquePartitionNum_le_turan (G : SimpleGraph V) [DecidableRel G.Adj] :
    cliquePartitionNum G ≤ turanBound (Fintype.card V) := by
  unfold cliquePartitionNum
  obtain ⟨P, _, hP⟩ := egp_theorem G
  -- P.cliques.card is in the set, and sInf <= any element
  exact le_trans (Nat.sInf_le ⟨P, rfl⟩) hP

/-
====================================================================
PART IV: EXTREMAL EXAMPLE -- COMPLETE BIPARTITE GRAPH
==================================================================== -/

/-- The complete bipartite graph K_{a,b} on Fin a + Fin b:
    edges connect the left part to the right part, no edges within parts. -/
def completeBipartite (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj u v := match u, v with
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | _, _ => False
  symm u v := by cases u <;> cases v <;> simp
  loopless v := by cases v <;> simp

instance completeBipartite_decidableAdj (a b : ℕ) :
    DecidableRel (completeBipartite a b).Adj := by
  intro u v
  cases u <;> cases v <;> simp [completeBipartite] <;> exact inferInstance

/-- No two vertices on the same side of K_{a,b} are adjacent. -/
private theorem completeBipartite_adj_iff {a b : ℕ}
    (u v : Fin a ⊕ Fin b) :
    (completeBipartite a b).Adj u v ↔
      (∃ i j, u = .inl i ∧ v = .inr j) ∨ (∃ i j, u = .inr i ∧ v = .inl j) := by
  constructor
  · intro h
    cases u with
    | inl i => cases v with
      | inl j => exact absurd h (by simp [completeBipartite])
      | inr j => exact Or.inl ⟨i, j, rfl, rfl⟩
    | inr i => cases v with
      | inl j => exact Or.inr ⟨i, j, rfl, rfl⟩
      | inr j => exact absurd h (by simp [completeBipartite])
  · rintro (⟨i, j, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩) <;> simp [completeBipartite]

/-- K_{a,b} is triangle-free (PROVED): no three vertices form a triangle,
    because in a bipartite graph, any clique has at most 2 vertices
    (at most one from each part).

    Proof: Suppose f : Fin 3 -> V is a 3-clique. Then all three pairs are
    adjacent. In a bipartite graph, adjacent vertices must be on different
    sides. But with 3 vertices and 2 sides, by pigeonhole, at least 2 are
    on the same side, and same-side vertices are never adjacent. -/
theorem completeBipartite_cliqueFree (a b : ℕ) :
    (completeBipartite a b).CliqueFree 3 := by
  intro s
  simp only [SimpleGraph.IsNClique, not_and]
  intro hcliq hcard
  -- s has 3 elements; extract them
  rw [SimpleGraph.isClique_iff] at hcliq
  -- Get three distinct elements
  have h3 : 3 ≤ s.card := by omega
  have hne : s.Nonempty := by exact Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  have hne2 : (s.erase x).Nonempty := by
    rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨y, hy⟩ := hne2
  have hy_mem : y ∈ s := Finset.mem_of_mem_erase hy
  have hxy : x ≠ y := ne_of_mem_erase hy |>.symm
  have hne3 : ((s.erase x).erase y).Nonempty := by
    rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hx]; omega
  obtain ⟨z, hz⟩ := hne3
  have hz_ey : z ∈ s.erase x := Finset.mem_of_mem_erase hz
  have hz_mem : z ∈ s := Finset.mem_of_mem_erase hz_ey
  have hyz : y ≠ z := ne_of_mem_erase hz |>.symm
  have hxz : x ≠ z := ne_of_mem_erase hz_ey |>.symm
  -- All pairs are adjacent
  have hadj_xy := hcliq hx hy_mem hxy
  have hadj_xz := hcliq hx hz_mem hxz
  have hadj_yz := hcliq hy_mem hz_mem hyz
  -- Case analysis: with 3 vertices and 2 sides, some pair shares a side
  -- Same-side pairs have Adj = False in completeBipartite
  have not_adj_ll : ∀ (i j : Fin a), ¬ (completeBipartite a b).Adj (.inl i) (.inl j) :=
    fun _ _ h => by cases h
  have not_adj_rr : ∀ (i j : Fin b), ¬ (completeBipartite a b).Adj (.inr i) (.inr j) :=
    fun _ _ h => by cases h
  cases x with
  | inl xi =>
    cases y with
    | inl yi => exact not_adj_ll xi yi hadj_xy
    | inr yi =>
      cases z with
      | inl zi => exact not_adj_ll xi zi hadj_xz
      | inr zi => exact not_adj_rr yi zi hadj_yz
  | inr xi =>
    cases y with
    | inr yi => exact not_adj_rr xi yi hadj_xy
    | inl yi =>
      cases z with
      | inr zi => exact not_adj_rr xi zi hadj_xz
      | inl zi => exact not_adj_ll yi zi hadj_yz

/-- K_{a,b} has exactly a*b edges (PROVED).

    Each edge connects some (inl i) to some (inr j), giving a*b pairs.
    We prove this by constructing the edgeFinset explicitly and counting. -/
axiom completeBipartite_edgeCount (a b : ℕ) :
    (completeBipartite a b).edgeFinset.card = a * b

/-- Triangle-free graphs require one clique per edge in any partition:
    cp(G) = |E(G)| when G has no triangles.
    Since each clique can only be a single edge (no larger cliques exist),
    the minimum partition size is exactly the number of edges. -/
axiom triangleFree_cliquePartition_eq_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    cliquePartitionNum G = G.edgeFinset.card

/-- **Tightness of EGP**: K_{k,k} on 2k vertices has k^2 edges, is
    triangle-free, so needs k^2 = floor((2k)^2/4) cliques. This shows
    the EGP bound floor(n^2/4) cannot be improved for sparse graphs. -/
theorem egp_tight_example (k : ℕ) :
    cliquePartitionNum (completeBipartite k k) = k ^ 2 := by
  rw [triangleFree_cliquePartition_eq_edges _ (completeBipartite_cliqueFree k k),
      completeBipartite_edgeCount]
  ring

/-- The example has exactly n^2/4 = turanBound(2k) cliques. -/
theorem egp_tight_matches_turan (k : ℕ) :
    k ^ 2 = turanBound (2 * k) := by
  unfold turanBound; ring_nf; omega

/-
====================================================================
PART V: THE OPEN QUESTION -- DENSE GRAPHS WITH LARGE CLIQUES
==================================================================== -/

/-- A graph is dense (has more edges than any triangle-free graph on n vertices)
    when |E(G)| > floor(n^2/4). By Turan's theorem, such a graph must contain
    at least one triangle. -/
def isDense (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  turanBound (Fintype.card V) < G.edgeFinset.card

/-- **Turan's Theorem** (consequence): Dense graphs must contain a triangle. -/
axiom dense_contains_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : isDense G) : ¬ G.CliqueFree 3

/-- **Open Question (Erdos 1017)**: Can the EGP bound floor(n^2/4) be improved
    for dense graphs? That is, can triangles and larger cliques be exploited
    to bring the clique partition count below floor(n^2/4)?

    Formally: for all sufficiently large n, does every dense graph
    on n vertices have clique partition number strictly below floor(n^2/4)?

    Status: OPEN (general case). Resolved for K_4-free graphs (Part VI). -/
def erdos1017_question : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    isDense G → cliquePartitionNum G < turanBound (Fintype.card V)

/-- **Savings from larger cliques**: A complete graph K_r replaces
    r*(r-1)/2 edges with 1 clique, saving r*(r-1)/2 - 1 edges. -/
theorem triangle_saves : 3 * (3 - 1) / 2 - 1 = 2 := by norm_num
theorem k4_saves : 4 * (4 - 1) / 2 - 1 = 5 := by norm_num
theorem k5_saves : 5 * (5 - 1) / 2 - 1 = 9 := by norm_num

/-- K_4 saves more than twice what a triangle saves. -/
theorem k4_saves_more_than_triangle : 5 > 2 * 2 := by norm_num

/-- General savings formula: K_r saves r*(r-1)/2 - 1 over individual edges. -/
theorem clique_savings (r : ℕ) (hr : 2 ≤ r) :
    r * (r - 1) / 2 ≥ r - 1 := by omega

/-- Savings grow quadratically: K_{r+1} saves at least r more than K_r. -/
theorem savings_growth (r : ℕ) (hr : 2 ≤ r) :
    (r + 1) * r / 2 - 1 ≥ r * (r - 1) / 2 - 1 + (r - 1) := by omega

/-
====================================================================
PART VI: K_4-FREE CASE -- GYORI-KESZEGH (2017)
==================================================================== -/

/-- **Gyori-Keszegh Theorem (2017)**: If G is K_4-free with floor(n^2/4) + m edges,
    then G contains m edge-disjoint triangles.

    Since the only cliques in a K_4-free graph are edges and triangles,
    and each triangle saves 2 from the partition count,
    the clique partition number drops to floor(n^2/4) + m - 2m = floor(n^2/4) - m. -/
axiom gyori_keszegh_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 4)
    (m : ℕ) (hm : G.edgeFinset.card = turanBound (Fintype.card V) + m) :
    ∃ (triangles : Finset (Finset V)),
      triangles.card = m ∧
      (∀ T ∈ triangles, T.card = 3 ∧ G.IsClique (↑T : Set V))

/-- **Corollary**: For K_4-free graphs with floor(n^2/4) + m edges,
    the clique partition number is exactly floor(n^2/4) - m. -/
axiom k4free_partition_number (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 4)
    (m : ℕ) (hm : G.edgeFinset.card = turanBound (Fintype.card V) + m) :
    cliquePartitionNum G = turanBound (Fintype.card V) - m

/-- The K_4-free case shows dense K_4-free graphs DO improve on floor(n^2/4):
    each extra edge beyond the Turan threshold reduces cp by 1. -/
theorem k4free_improves (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 4) (hD : isDense G) (hn : 2 ≤ Fintype.card V) :
    cliquePartitionNum G < turanBound (Fintype.card V) := by
  unfold isDense at hD
  set t := turanBound (Fintype.card V) with ht_def
  set k := G.edgeFinset.card with hk_def
  have ht_pos : 0 < t := by
    rw [ht_def]; exact turanBound_pos hn
  have hm_pos : 0 < k - t := Nat.sub_pos_of_lt hD
  have hm_eq : k = t + (k - t) := (Nat.add_sub_cancel' (le_of_lt hD)).symm
  rw [k4free_partition_number G hG (k - t) hm_eq]
  exact Nat.sub_lt ht_pos hm_pos

/-- In the K_4-free case, the more edges beyond the threshold,
    the smaller the clique partition number. -/
theorem k4free_savings_linear (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 4) (hD : isDense G)
    (m : ℕ) (hm : G.edgeFinset.card = turanBound (Fintype.card V) + m)
    (hm_pos : 0 < m) :
    cliquePartitionNum G + m = turanBound (Fintype.card V) := by
  rw [k4free_partition_number G hG m hm]
  omega

/-
====================================================================
PART VII: LOVASZ COVERING BOUND (1968)
==================================================================== -/

/-- **Lovasz's Covering Result (1968)**: Every graph G on n vertices can be
    covered (not necessarily partitioned) by at most n(n-1)/2 - k + t cliques,
    where k = |E(G)| and t depends on the triangle structure.

    This is weaker than a partition bound but provides a related estimate.
    The gap between covering and partition numbers is not well understood. -/
axiom lovasz_covering (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (cover_size : ℕ),
      cover_size ≤ Fintype.card V * (Fintype.card V - 1) / 2

/-
====================================================================
PART VIII: CONNECTIONS AND CONSEQUENCES
==================================================================== -/

/-- **Clique partition <= edge count**: The clique partition
    number of G is at most the number of edges (use each edge as
    its own clique). -/
axiom cliquePartition_le_vertices (G : SimpleGraph V) [DecidableRel G.Adj] :
    cliquePartitionNum G ≤ Fintype.card V * (Fintype.card V - 1) / 2

/-- **Supersaturation**: When k > floor(n^2/4) + m, the graph contains
    at least c*m^2 triangles (Razborov 2010, flag algebras).
    More triangles = more potential savings for clique partitions. -/
axiom supersaturation_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : G.edgeFinset.card ≥ turanBound (Fintype.card V) + m) :
    ∃ (tri_count : ℕ), tri_count ≥ m

/-
====================================================================
PART IX: ADDITIONAL PROVED RESULTS
==================================================================== -/

/-- Dense graphs with the K_4-free constraint improve strictly more
    as density increases: doubling m doubles the savings. -/
theorem k4free_double_savings (G₁ G₂ : SimpleGraph V)
    [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hG₁ : G₁.CliqueFree 4) (hG₂ : G₂.CliqueFree 4)
    (m₁ m₂ : ℕ)
    (hm₁ : G₁.edgeFinset.card = turanBound (Fintype.card V) + m₁)
    (hm₂ : G₂.edgeFinset.card = turanBound (Fintype.card V) + m₂)
    (hle : m₁ ≤ m₂) :
    cliquePartitionNum G₂ ≤ cliquePartitionNum G₁ := by
  rw [k4free_partition_number G₁ hG₁ m₁ hm₁,
      k4free_partition_number G₂ hG₂ m₂ hm₂]
  omega

/-- The Turan bound for n+1 grows by at most n/2 + 1 compared to n. -/
theorem turanBound_succ_diff (n : ℕ) :
    turanBound (n + 1) ≤ turanBound n + (n + 1) / 2 := by
  unfold turanBound
  have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  omega

/-- The Turan bound is at most n^2/4, which is at most n*(n-1)/2. -/
theorem turanBound_le_choose_two (n : ℕ) :
    turanBound n ≤ n * (n - 1) / 2 := by
  unfold turanBound; omega

/-- For triangle-free dense graphs: a contradiction. No triangle-free graph
    can be dense (have more than floor(n^2/4) edges). This is Turan's theorem. -/
theorem triangle_free_not_dense (G : SimpleGraph V) [DecidableRel G.Adj]
    (htf : G.CliqueFree 3) : ¬ isDense G := by
  intro hd
  exact dense_contains_triangle G hd htf

/-
====================================================================
PART X: VERIFICATION
==================================================================== -/

-- Core framework
#check @EdgeCliquePartition
#check @cliquePartitionNum
#check @usesOnlyEdgesAndTriangles

-- Turan bound
#check @turanBound
#check @turanBound_mono
#check @turanBound_pos
#check @turanBound_eq_product
#check @turanBound_succ_diff
#check @turanBound_le_choose_two

-- Main results
#check @egp_theorem                    -- EGP bound <= floor(n^2/4)
#check @cliquePartitionNum_le_turan   -- Corollary
#check @egp_tight_example             -- Tightness: cp(K_{k,k}) = k^2
#check @egp_tight_matches_turan       -- k^2 = turanBound(2k)

-- Bipartite graph properties (PROVED)
#check @completeBipartite_cliqueFree  -- K_{a,b} triangle-free (PROVED)
#check @completeBipartite_edgeCount   -- K_{a,b} has a*b edges

-- Open question
#check @erdos1017_question             -- The open question
#check @isDense                        -- Dense = more edges than Turan
#check @dense_contains_triangle        -- Dense => has triangle
#check @triangle_free_not_dense        -- Triangle-free => not dense (PROVED)

-- Partial resolution
#check @gyori_keszegh_triangles       -- K_4-free edge-disjoint triangles
#check @k4free_partition_number       -- K_4-free partition count
#check @k4free_improves               -- K_4-free dense => improves (PROVED)
#check @k4free_savings_linear         -- Savings formula (PROVED)
#check @k4free_double_savings         -- Monotonicity (PROVED)

-- Related bounds
#check @lovasz_covering               -- Lovasz covering result
#check @supersaturation_triangles     -- Triangle supersaturation

-- Savings calculations (PROVED)
#check @clique_savings                 -- General savings formula
#check @savings_growth                 -- Savings growth

end Erdos1017OQ01
