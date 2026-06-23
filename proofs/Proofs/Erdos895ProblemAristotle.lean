/-
  Aristotle targets for Erdős Problem #895
  Supporting lemmas for the independent additive triple theorem.
  See Erdos895Problem.lean for the main formalization.

  Criteria for inclusion:
  - triangleFree_neighborhood_independent: N(v) is independent in triangle-free G (direct)
  - triangleFree_degree_sum_bound: d(u)+d(v) ≤ n for adjacent u,v (Mantel step)
  - mantel_theorem: triangle-free graphs have ≤ n²/4 edges (classical 1907 result)
  - NOT barber_theorem (main SAT-verified result, beyond Aristotle scope)
  - NOT counterexample_17 (requires explicit SAT-based graph construction)
  - NOT erdos895_sat_verified (computational verification, not a proof)
-/
import Mathlib

namespace Erdos895ProblemAristotle

open Finset SimpleGraph

/-
  Core definitions reproduced from Erdos895Problem.lean (self-contained).
-/

abbrev GraphOnInterval (n : ℕ) := SimpleGraph (Fin n)

def IsTriangleFree {n : ℕ} (G : GraphOnInterval n) : Prop :=
  ∀ a b c : Fin n, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)

def IsIndependentTriple {n : ℕ} (G : GraphOnInterval n) (a b c : Fin n) : Prop :=
  ¬G.Adj a b ∧ ¬G.Adj b c ∧ ¬G.Adj a c

def IsAdditiveTriple {n : ℕ} (a b c : Fin n) : Prop :=
  (a.val : ℕ) + b.val = c.val ∧ a.val > 0 ∧ b.val > 0

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Key Structural Lemma (Triangle-Free Neighborhood)
-- ═══════════════════════════════════════════════════════════════════

/-- Triangle-free implies neighborhood is independent:
    if v is adjacent to both u and w, then u and w are not adjacent.
    Direct consequence of IsTriangleFree. -/
theorem triangleFree_neighborhood_independent {n : ℕ} (G : GraphOnInterval n)
    (hG : IsTriangleFree G) (v u w : Fin n)
    (hvu : G.Adj v u) (hvw : G.Adj v w) :
    ¬G.Adj u w := fun huw => hG v u w ⟨hvu, huw, hvw⟩

/-- Triangle-free is symmetric in its arguments:
    we can permute the triple (a, b, c) and the property still holds. -/
theorem isTriangleFree_symm {n : ℕ} (G : GraphOnInterval n)
    (hG : IsTriangleFree G) (a b c : Fin n) :
    ¬(G.Adj b a ∧ G.Adj a c ∧ G.Adj b c) := by
  intro ⟨hba, hac, hbc⟩
  exact hG b a c ⟨hba, hac, hbc⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Neighbor Disjointness in Triangle-Free Graphs
-- ═══════════════════════════════════════════════════════════════════

/-- In a triangle-free graph, the neighborhoods of adjacent vertices are disjoint.
    If G.Adj u v, then N(u) ∩ N(v) = ∅.
    Proof: any common neighbor w would form a triangle u-w-v.
    Mathlib: use Finset.disjoint_left, SimpleGraph.neighborFinset. -/
theorem triangleFree_neighbor_disjoint {n : ℕ} (G : GraphOnInterval n)
    [DecidableRel G.Adj] (hG : IsTriangleFree G)
    (u v : Fin n) (huv : G.Adj u v) :
    Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
  rw [Finset.disjoint_left]
  intro w hwu hwv
  rw [SimpleGraph.mem_neighborFinset] at hwu hwv
  exact hG u w v ⟨hwu, G.symm hwv, huv⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Degree Sum Bound (Key Step for Mantel)
-- ═══════════════════════════════════════════════════════════════════

/-- In a triangle-free graph, adjacent vertices u,v satisfy deg(u) + deg(v) ≤ n.
    Proof: N(u) and N(v) are disjoint (by triangle-freeness) and both ⊆ Fin n,
    so |N(u)| + |N(v)| ≤ |Fin n| = n.
    Mathlib: Finset.card_union_le, Finset.card_fin, triangleFree_neighbor_disjoint. -/
theorem triangleFree_degree_sum_bound {n : ℕ} (G : GraphOnInterval n)
    [DecidableRel G.Adj] (hG : IsTriangleFree G)
    (u v : Fin n) (huv : G.Adj u v) :
    (G.neighborFinset u).card + (G.neighborFinset v).card ≤ n := by
  have hdisj := triangleFree_neighbor_disjoint G hG u v huv
  have hunion_le : (G.neighborFinset u ∪ G.neighborFinset v).card ≤ n :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n)
  linarith [Finset.card_union_of_disjoint hdisj]

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Mantel's Theorem
-- ═══════════════════════════════════════════════════════════════════

/-- Mantel's theorem (1907): A triangle-free graph on n vertices has at most ⌊n²/4⌋ edges.
    Proof sketch (double counting):
      For each edge {u,v}: deg(u) + deg(v) ≤ n  (by triangleFree_degree_sum_bound)
      Summing over all edges:  Σ_{uv ∈ E} [d(u) + d(v)] ≤ n·|E|
      But the LHS = Σ_u d(u)² ≥ (Σ_u d(u))²/n = (2|E|)²/n
      So (2|E|)²/n ≤ n·|E|, giving 4|E|² ≤ n²·|E|, so |E| ≤ n²/4.
    Mathlib: See SimpleGraph.edgeFinset, sum_degrees_eq_twice_card_edges. -/
theorem mantel_theorem {n : ℕ} (G : GraphOnInterval n) [DecidableRel G.Adj]
    (hG : IsTriangleFree G) :
    G.edgeFinset.card ≤ n ^ 2 / 4 := by
  have hcf : G.CliqueFree (2 + 1) := by
    intro t ht
    rw [SimpleGraph.isNClique_iff] at ht
    obtain ⟨hclique_set, hcard⟩ := ht
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
    exact hG a b c ⟨
      hclique_set (by simp) (by simp) hab,
      hclique_set (by simp) (by simp) hbc,
      hclique_set (by simp) (by simp) hac⟩
  have hbound : G.edgeFinset.card ≤
      (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + (n % 2).choose 2 := by
    have key := CliqueFree.card_edgeFinset_le hcf
    simp only [Fintype.card_fin] at key
    exact key
  have hchoose : (n % 2).choose 2 = 0 :=
    Nat.choose_eq_zero_of_lt (Nat.mod_lt n (by norm_num))
  calc G.edgeFinset.card
      ≤ (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + (n % 2).choose 2 := hbound
    _ = (n ^ 2 - (n % 2) ^ 2) / 4 + 0 := by rw [hchoose]; norm_num
    _ ≤ n ^ 2 / 4 := by simp only [add_zero]; exact Nat.div_le_div_right (Nat.sub_le _ _)

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Simple Utility Facts
-- ═══════════════════════════════════════════════════════════════════

/-- Additive triple (1, 1, 2) exists in Fin 18: 1 + 1 = 2. -/
theorem additive_triple_1_1_2 : IsAdditiveTriple (⟨1, by omega⟩ : Fin 18)
    ⟨1, by omega⟩ ⟨2, by omega⟩ :=
  ⟨rfl, by omega, by omega⟩

/-- Additive triple (1, 2, 3) exists in Fin 18: 1 + 2 = 3. -/
theorem additive_triple_1_2_3 : IsAdditiveTriple (⟨1, by omega⟩ : Fin 18)
    ⟨2, by omega⟩ ⟨3, by omega⟩ :=
  ⟨rfl, by omega, by omega⟩

/-- For n ≥ 18 vertices, n² / 4 ≥ 81. -/
theorem threshold_mantel_bound (n : ℕ) (hn : n ≥ 18) : n ^ 2 / 4 ≥ 81 := by
  omega

end Erdos895ProblemAristotle
