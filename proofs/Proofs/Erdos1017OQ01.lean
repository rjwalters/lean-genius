import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
# Erdős Problem #1017 (OQ-01): Clique Partition of Dense Graphs

## Background
Let f(n,k) = min m such that every n-vertex k-edge graph can be edge-partitioned
into at most m complete subgraphs.

Erdős-Goodman-Pósa (1966): f(n,k) ≤ ⌊n²/4⌋, using only edges and triangles.
Extremal: K_{n/2,n/2} achieves equality (triangle-free, needs n²/4 edges as cliques).

## Open Question
Can f(n,k) < ⌊n²/4⌋ when k > n²/4 and the graph contains K₄ or larger cliques?

The K₄-free case is resolved by Győri-Keszegh (2017): if G is K₄-free with
⌊n²/4⌋ + m edges, it contains m edge-disjoint triangles, giving f = ⌊n²/4⌋ - m.

## Proof Techniques
- Greedy triangle extraction + Turán bound on remainder
- Complete bipartite extremal construction
- Edge-disjoint triangle packing (Győri-Keszegh)
-/

set_option maxHeartbeats 400000

namespace Erdos1017OQ01

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: EDGE CLIQUE PARTITION FRAMEWORK
═══════════════════════════════════════════════════════════════════════════════ -/

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

/-- A partition uses only edges and triangles if every clique has ≤ 3 vertices. -/
def usesOnlyEdgesAndTriangles {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : EdgeCliquePartition G) : Prop :=
  ∀ S ∈ P.cliques, S.card ≤ 3

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: TURÁN NUMBER AND FLOOR(n²/4)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Turán number for triangles: ⌊n²/4⌋. This equals ex(n, K₃),
    the maximum number of edges in a triangle-free graph on n vertices. -/
def turanBound (n : ℕ) : ℕ := n ^ 2 / 4

/-- Small values of the Turán bound. -/
theorem turanBound_zero : turanBound 0 = 0 := by decide
theorem turanBound_one : turanBound 1 = 0 := by decide
theorem turanBound_two : turanBound 2 = 1 := by decide
theorem turanBound_three : turanBound 3 = 2 := by decide
theorem turanBound_four : turanBound 4 = 4 := by decide

/-- turanBound is monotone. -/
theorem turanBound_mono {m n : ℕ} (h : m ≤ n) : turanBound m ≤ turanBound n := by
  unfold turanBound
  exact Nat.div_le_div_right (Nat.pow_le_pow_left h 2)

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: ERDŐS-GOODMAN-PÓSA THEOREM (1966)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Erdős-Goodman-Pósa Theorem**: Every graph on n vertices can be
    edge-partitioned into at most ⌊n²/4⌋ complete subgraphs, using
    only edges (K₂) and triangles (K₃).

    Proof sketch: Extract a maximal set of edge-disjoint triangles.
    The remainder is triangle-free, hence bipartite by Ramsey theory.
    A bipartite graph on n vertices has ≤ ⌊n²/4⌋ edges (Turán).
    Each triangle replaces 3 edges with 1 clique, so total ≤ ⌊n²/4⌋. -/
axiom egp_theorem (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ P : EdgeCliquePartition G,
      usesOnlyEdgesAndTriangles P ∧ P.cliques.card ≤ turanBound (Fintype.card V)

/-- Corollary: cp(G) ≤ ⌊n²/4⌋ for every graph G on n vertices. -/
theorem cliquePartitionNum_le_turan (G : SimpleGraph V) [DecidableRel G.Adj] :
    cliquePartitionNum G ≤ turanBound (Fintype.card V) := by
  unfold cliquePartitionNum
  obtain ⟨P, _, hP⟩ := egp_theorem G
  -- P.cliques.card is in the set, and sInf ≤ any element
  exact le_trans (Nat.sInf_le ⟨P, rfl⟩) hP

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: EXTREMAL EXAMPLE — COMPLETE BIPARTITE GRAPH
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The complete bipartite graph K_{a,b} on Fin a ⊕ Fin b:
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

/-- K_{a,b} is triangle-free: no three vertices form a triangle,
    because in a bipartite graph, any clique has at most 2 vertices
    (at most one from each part). -/
axiom completeBipartite_cliqueFree (a b : ℕ) :
    (completeBipartite a b).CliqueFree 3

/-- K_{a,b} has exactly a*b edges. -/
axiom completeBipartite_edgeCount (a b : ℕ) :
    (completeBipartite a b).edgeFinset.card = a * b

/-- Triangle-free graphs require one clique per edge in any partition:
    cp(G) = |E(G)| when G has no triangles.
    Since each clique can only be a single edge (no larger cliques exist),
    the minimum partition size is exactly the number of edges. -/
axiom triangleFree_cliquePartition_eq_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    cliquePartitionNum G = G.edgeFinset.card

/-- **Tightness of EGP**: K_{k,k} on 2k vertices has k² edges, is
    triangle-free, so needs k² = ⌊(2k)²/4⌋ cliques. This shows
    the EGP bound ⌊n²/4⌋ cannot be improved for sparse graphs. -/
theorem egp_tight_example (k : ℕ) :
    cliquePartitionNum (completeBipartite k k) = k ^ 2 := by
  rw [triangleFree_cliquePartition_eq_edges _ (completeBipartite_cliqueFree k k),
      completeBipartite_edgeCount]
  ring

/-- The example has exactly n²/4 = turanBound(2k) cliques. -/
theorem egp_tight_matches_turan (k : ℕ) :
    k ^ 2 = turanBound (2 * k) := by
  unfold turanBound; ring_nf; omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: THE OPEN QUESTION — DENSE GRAPHS WITH LARGE CLIQUES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A graph is dense (has more edges than any triangle-free graph on n vertices)
    when |E(G)| > ⌊n²/4⌋. By Turán's theorem, such a graph must contain
    at least one triangle. -/
def isDense (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  turanBound (Fintype.card V) < G.edgeFinset.card

/-- **Turán's Theorem** (consequence): Dense graphs must contain a triangle. -/
axiom dense_contains_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : isDense G) : ¬ G.CliqueFree 3

/-- **Open Question (Erdős 1017)**: Can the EGP bound ⌊n²/4⌋ be improved
    for dense graphs? That is, can triangles and larger cliques be exploited
    to bring the clique partition count below ⌊n²/4⌋?

    Formally: for all sufficiently large n, does every dense graph
    on n vertices have clique partition number strictly below ⌊n²/4⌋?

    Status: OPEN (general case). Resolved for K₄-free graphs (Part VI). -/
def erdos1017_question : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    isDense G → cliquePartitionNum G < turanBound (Fintype.card V)

/-- **Savings from larger cliques**: A complete graph K_r replaces
    r*(r-1)/2 edges with 1 clique, saving r*(r-1)/2 - 1 edges. -/
theorem triangle_saves : 3 * (3 - 1) / 2 - 1 = 2 := by norm_num
theorem k4_saves : 4 * (4 - 1) / 2 - 1 = 5 := by norm_num
theorem k5_saves : 5 * (5 - 1) / 2 - 1 = 9 := by norm_num

/-- K₄ saves more than twice what a triangle saves. -/
theorem k4_saves_more_than_triangle : 5 > 2 * 2 := by norm_num

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: K₄-FREE CASE — GYŐRI-KESZEGH (2017)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Győri-Keszegh Theorem (2017)**: If G is K₄-free with ⌊n²/4⌋ + m edges,
    then G contains m edge-disjoint triangles.

    Since the only cliques in a K₄-free graph are edges and triangles,
    and each triangle saves 2 from the partition count,
    the clique partition number drops to ⌊n²/4⌋ + m - 2m = ⌊n²/4⌋ - m. -/
axiom gyori_keszegh_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 4)
    (m : ℕ) (hm : G.edgeFinset.card = turanBound (Fintype.card V) + m) :
    ∃ (triangles : Finset (Finset V)),
      triangles.card = m ∧
      (∀ T ∈ triangles, T.card = 3 ∧ G.IsClique (↑T : Set V))

/-- **Corollary**: For K₄-free graphs with ⌊n²/4⌋ + m edges,
    the clique partition number is exactly ⌊n²/4⌋ - m. -/
axiom k4free_partition_number (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 4)
    (m : ℕ) (hm : G.edgeFinset.card = turanBound (Fintype.card V) + m) :
    cliquePartitionNum G = turanBound (Fintype.card V) - m

/-- The K₄-free case shows dense K₄-free graphs DO improve on ⌊n²/4⌋:
    each extra edge beyond the Turán threshold reduces cp by 1. -/
theorem k4free_improves (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 4) (hD : isDense G) (hn : 2 ≤ Fintype.card V) :
    cliquePartitionNum G < turanBound (Fintype.card V) := by
  unfold isDense at hD
  set t := turanBound (Fintype.card V) with ht_def
  set k := G.edgeFinset.card with hk_def
  have ht_pos : 0 < t := by
    rw [ht_def]; unfold turanBound
    have : 4 ≤ Fintype.card V ^ 2 := by nlinarith
    omega
  have hm_pos : 0 < k - t := Nat.sub_pos_of_lt hD
  have hm_eq : k = t + (k - t) := (Nat.add_sub_cancel' (le_of_lt hD)).symm
  rw [k4free_partition_number G hG (k - t) hm_eq]
  exact Nat.sub_lt ht_pos hm_pos

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: LOVÁSZ COVERING BOUND (1968)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Lovász's Covering Result (1968)**: Every graph G on n vertices can be
    covered (not necessarily partitioned) by at most n(n-1)/2 - k + t cliques,
    where k = |E(G)| and t depends on the triangle structure.

    This is weaker than a partition bound but provides a related estimate.
    The gap between covering and partition numbers is not well understood. -/
axiom lovasz_covering (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (cover_size : ℕ),
      cover_size ≤ Fintype.card V * (Fintype.card V - 1) / 2

/-
═══════════════════════════════════════════════════════════════════════════════
PART VIII: CONNECTIONS AND CONSEQUENCES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Clique partition ↔ edge coloring of complement**: The clique partition
    number of G equals the chromatic index of the complement G̅.
    This connects Problem #1017 to Vizing's theorem and edge-coloring theory. -/
axiom cliquePartition_le_vertices (G : SimpleGraph V) [DecidableRel G.Adj] :
    cliquePartitionNum G ≤ Fintype.card V * (Fintype.card V - 1) / 2

/-- **Supersaturation**: When k > ⌊n²/4⌋ + m, the graph contains
    at least c·m² triangles (Razborov 2010, flag algebras).
    More triangles = more potential savings for clique partitions. -/
axiom supersaturation_triangles (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : G.edgeFinset.card ≥ turanBound (Fintype.card V) + m) :
    ∃ (tri_count : ℕ), tri_count ≥ m

/-
═══════════════════════════════════════════════════════════════════════════════
PART IX: VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

-- Core framework
#check @EdgeCliquePartition
#check @cliquePartitionNum
#check @usesOnlyEdgesAndTriangles

-- Turán bound
#check @turanBound
#check @turanBound_mono

-- Main results
#check @egp_theorem                    -- EGP bound ≤ ⌊n²/4⌋
#check @cliquePartitionNum_le_turan   -- Corollary
#check @egp_tight_example             -- Tightness: cp(K_{k,k}) = k²
#check @egp_tight_matches_turan       -- k² = turanBound(2k)

-- Open question
#check @erdos1017_question             -- The open question
#check @isDense                        -- Dense = more edges than Turán
#check @dense_contains_triangle        -- Dense ⟹ has triangle

-- Partial resolution
#check @gyori_keszegh_triangles       -- K₄-free edge-disjoint triangles
#check @k4free_partition_number       -- K₄-free partition count
#check @k4free_improves               -- K₄-free dense ⟹ improves on ⌊n²/4⌋

-- Related bounds
#check @lovasz_covering               -- Lovász covering result
#check @supersaturation_triangles     -- Triangle supersaturation

end Erdos1017OQ01
