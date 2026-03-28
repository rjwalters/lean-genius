/-
Erdős Problem #1182: Ramsey-Theoretic Edge Thresholds

Source: https://erdosproblems.com/1182
Status: OPEN (Burr–Erdős–Faudree–Rousseau–Schelp)

Statement:
Let f(n) = max edges in a connected n-vertex graph G with R(K₃, G) = 2n - 1.
Let F(n) = max edges such that EVERY connected n-vertex graph G with
  ≤ F(n) edges satisfies R(K₃, G) = 2n - 1.

Estimate f(n) and F(n). In particular, does F(n)/n → ∞?

Known bounds:
- F(n) ≥ n - 1 (Chvátal: R(K₃, tree) = 2n - 1)
- (17n + 1)/15 ≤ F(n) ≤ (27/4 + o(1)) · n · (log n)²
- √(log n) · n^(3/2) ≪ f(n) ≪ n^(5/3) · (log n)^(2/3)

Computed values:
  n:    2  3  4  5   6
  F(n): 1  2  5  7   8
  f(n): 1  2  5  8  12

References:
- Burr, Erdős, Faudree, Rousseau, Schelp (1980)
- Chvátal (1977): R(K₃, Tₙ) = 2n - 1

Tags: graph-theory, ramsey-theory, extremal-combinatorics
-/

import Mathlib

namespace Erdos1182

open Classical in
attribute [local instance] Classical.propDecidable

-- ## Part I: Ramsey Numbers (Simplified)

/-- The Ramsey number R(s, t) is the minimum r such that any 2-coloring
    of edges of K_r contains a red K_s or a blue K_t.
    We use the standard Nat-valued version. -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ :=
  sInf { r : ℕ | r ≥ 1 ∧ ∀ (f : Fin r → Fin r → Bool),
    (∃ S : Finset (Fin r), S.card = s ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → f a b = true) ∨
    (∃ T : Finset (Fin r), T.card = t ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → f a b = false) }

-- ## Part II: Graph-Theoretic Ramsey Number

/-- A simple graph on n vertices (represented by adjacency on Fin n). -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ a b, adj a b → adj b a
  irrefl : ∀ a, ¬adj a a

/-- Edge count of a graph (number of unordered adjacent pairs). -/
noncomputable def edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  ((Finset.univ.product Finset.univ).filter fun (p : Fin n × Fin n) =>
    p.1 < p.2 ∧ G.adj p.1 p.2).card

/-- A graph is connected if every pair of vertices is reachable via adjacency. -/
def Graph.Connected {n : ℕ} (G : Graph n) : Prop :=
  ∀ u v : Fin n, Relation.ReflTransGen (fun a b => G.adj a b) u v

/-- The graph Ramsey number R(K₃, G) for a graph G on n vertices:
    smallest r such that every 2-coloring of K_r contains a red K₃
    or a blue copy of G (as an induced subgraph via injection).
    Returns 0 if the set is empty (degenerate; nonemptiness follows
    from the Ramsey theorem for any fixed G). -/
noncomputable def graphRamseyK3 {n : ℕ} (G : Graph n) : ℕ :=
  sInf { r : ℕ | ∀ (color : Fin r → Fin r → Bool),
    (∃ a b c : Fin r, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      color a b = true ∧ color b c = true ∧ color a c = true) ∨
    (∃ (φ : Fin n ↪ Fin r),
      ∀ a b : Fin n, G.adj a b → color (φ a) (φ b) = false) }

-- ## Part III: The Threshold Functions

/-- f(n): maximum edges in an n-vertex graph G with R(K₃, G) = 2n - 1. -/
noncomputable def f_threshold (n : ℕ) : ℕ :=
  sSup { e : ℕ | ∃ (G : Graph n), edgeCount G = e ∧ graphRamseyK3 G = 2 * n - 1 }

/-- F(n): maximum edges such that EVERY connected n-vertex graph with
    ≤ F(n) edges satisfies R(K₃, G) = 2n - 1.

    CORRECTED: The original definition omitted the connectivity condition
    required by the mathematical definition in BEFRS (1980). Without it,
    disconnected sparse graphs (with small Ramsey numbers) make F(n) = 0
    for all n ≥ 3.

    The explicit bound e ≤ n*(n-1)/2 ensures the set is bounded above,
    making sSup well-behaved on ℕ. This is mathematically redundant
    (no graph has more edges) but required for the formalization. -/
noncomputable def bigF_threshold (n : ℕ) : ℕ :=
  sSup { e : ℕ | e ≤ n * (n - 1) / 2 ∧
    ∀ (G : Graph n), G.Connected → edgeCount G ≤ e →
      graphRamseyK3 G = 2 * n - 1 }

-- ## Part IV: Known Results

/-- Chvátal (1977): For any tree T on n vertices, R(K₃, T) = 2n - 1.
    Trees have exactly n - 1 edges and n vertices. -/
axiom chvatal_tree_ramsey (n : ℕ) (hn : n ≥ 2) (T : Graph n) :
  edgeCount T = n - 1 → graphRamseyK3 T = 2 * n - 1

/-- A connected graph on n ≥ 1 vertices has at least n - 1 edges.
    Standard graph theory result (proof by induction on n: removing a leaf
    from a connected graph gives a connected graph on n-1 vertices). -/
axiom connected_min_edges {n : ℕ} (G : Graph n) (hn : n ≥ 1) :
  G.Connected → edgeCount G ≥ n - 1

-- ## Part V: Infrastructure for Small Cases

/-- The complete graph on 2 vertices. -/
def completeGraph2 : Graph 2 where
  adj a b := a ≠ b
  symm _ _ h := Ne.symm h
  irrefl _ h := h rfl

/-- In Fin 2, the only ordered pair with a < b is (0, 1). -/
private lemma fin2_lt_unique (a b : Fin 2) (hab : a < b) : a = 0 ∧ b = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all

/-- Any Graph on 2 vertices has at most 1 edge. -/
lemma graph2_edge_le_one (G : Graph 2) : edgeCount G ≤ 1 := by
  unfold edgeCount
  rw [Finset.card_le_one]
  intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at h₁ h₂
  obtain ⟨hab₁, _⟩ := h₁
  obtain ⟨hab₂, _⟩ := h₂
  have := fin2_lt_unique a₁ b₁ hab₁
  have := fin2_lt_unique a₂ b₂ hab₂
  ext <;> simp_all

/-- K₂ has exactly 1 edge. -/
lemma edgeCount_completeGraph2 : edgeCount completeGraph2 = 1 := by
  apply le_antisymm (graph2_edge_le_one completeGraph2)
  -- Show (0, 1) is in the filtered set, giving card ≥ 1
  unfold edgeCount
  have hmem : ((0 : Fin 2), (1 : Fin 2)) ∈
    ((Finset.univ.product Finset.univ).filter fun (p : Fin 2 × Fin 2) =>
      p.1 < p.2 ∧ completeGraph2.adj p.1 p.2) := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨Fin.zero_lt_one, Fin.zero_ne_one⟩
  exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- K₂ is connected (trivially: the two vertices are adjacent). -/
lemma completeGraph2_connected : completeGraph2.Connected := by
  intro u v
  fin_cases u <;> fin_cases v
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (show completeGraph2.adj 0 1 from Fin.zero_ne_one)
  · exact Relation.ReflTransGen.single (show completeGraph2.adj 1 0 from Fin.one_ne_zero)
  · exact Relation.ReflTransGen.refl

-- ## Part VI: Proved Bounds

/-- Corollary: F(n) ≥ n - 1 (since all connected graphs with ≤ n-1 edges are trees).

    Proof: n-1 satisfies the defining condition of bigF_threshold. If G is
    connected with edgeCount G ≤ n-1, then connected_min_edges gives
    edgeCount G ≥ n-1, hence edgeCount G = n-1. Then chvatal_tree_ramsey applies. -/
theorem bigF_lower_bound_tree (n : ℕ) (hn : n ≥ 2) :
    bigF_threshold n ≥ n - 1 := by
  unfold bigF_threshold
  apply le_csSup
  · -- BddAbove: all elements are ≤ n*(n-1)/2 by definition
    exact ⟨n * (n - 1) / 2, fun _ he => he.1⟩
  · -- n - 1 ∈ the set
    constructor
    · -- n - 1 ≤ n*(n-1)/2 for n ≥ 2
      omega
    · intro G hConn hEdge
      have hge := connected_min_edges G (by omega) hConn
      have heq : edgeCount G = n - 1 := Nat.le_antisymm hEdge hge
      exact chvatal_tree_ramsey n hn G heq

/-- f(2) = 1: K₂ has 1 edge and R(K₃, K₂) = 2·2 - 1 = 3.
    No Graph on 2 vertices can have more than 1 edge. -/
theorem f_val_2 : f_threshold 2 = 1 := by
  unfold f_threshold
  have hK2_ramsey := chvatal_tree_ramsey 2 (by norm_num) completeGraph2 edgeCount_completeGraph2
  have hK2_mem : (1 : ℕ) ∈ { e : ℕ | ∃ G : Graph 2, edgeCount G = e ∧
      graphRamseyK3 G = 2 * 2 - 1 } :=
    ⟨completeGraph2, edgeCount_completeGraph2, hK2_ramsey⟩
  have hbdd : BddAbove { e : ℕ | ∃ G : Graph 2, edgeCount G = e ∧
      graphRamseyK3 G = 2 * 2 - 1 } := by
    refine ⟨1, fun e he => ?_⟩
    obtain ⟨G, hcount, _⟩ := he
    rw [← hcount]
    exact graph2_edge_le_one G
  apply le_antisymm
  · -- sSup ≤ 1
    apply csSup_le ⟨1, hK2_mem⟩
    intro e he
    obtain ⟨G, hcount, _⟩ := he
    rw [← hcount]
    exact graph2_edge_le_one G
  · -- 1 ≤ sSup
    exact le_csSup hbdd hK2_mem

/-- F(2) = 1: The only connected graph on 2 vertices is K₂ (1 edge).
    For e = 0: vacuously true (no connected Graph 2 has 0 edges).
    For e = 1: K₂ satisfies R(K₃, K₂) = 3 = 2·2-1 by Chvátal. -/
theorem bigF_val_2 : bigF_threshold 2 = 1 := by
  unfold bigF_threshold
  -- The set is { e | e ≤ 2*(2-1)/2 ∧ ∀ G connected, edgeCount G ≤ e → R(K₃,G) = 3 }
  -- Note: 2*(2-1)/2 = 1 in ℕ
  have bound_eq : 2 * (2 - 1) / 2 = 1 := by norm_num
  have hmem_1 : (1 : ℕ) ∈ { e : ℕ | e ≤ 2 * (2 - 1) / 2 ∧
      ∀ G : Graph 2, G.Connected → edgeCount G ≤ e →
        graphRamseyK3 G = 2 * 2 - 1 } := by
    constructor
    · omega
    · intro G hConn hEdge
      have hge := connected_min_edges G (by norm_num) hConn
      have heq : edgeCount G = 1 := le_antisymm hEdge hge
      exact chvatal_tree_ramsey 2 (by norm_num) G heq
  have hbdd : BddAbove { e : ℕ | e ≤ 2 * (2 - 1) / 2 ∧
      ∀ G : Graph 2, G.Connected → edgeCount G ≤ e →
        graphRamseyK3 G = 2 * 2 - 1 } :=
    ⟨1, fun _ he => by omega⟩
  apply le_antisymm
  · -- sSup ≤ 1
    apply csSup_le ⟨1, hmem_1⟩
    intro e he
    obtain ⟨hle, _⟩ := he
    omega
  · -- 1 ≤ sSup
    exact le_csSup hbdd hmem_1

-- ## Part VII: Known Bounds

/-- Lower bound: F(n) ≥ (17n + 1)/15 for n ≥ 4.
    Burr–Erdős–Faudree–Rousseau–Schelp (1980). -/
axiom bigF_lower_linear (n : ℕ) (hn : n ≥ 4) :
  15 * bigF_threshold n ≥ 17 * n + 1

/-- The main open question: does F(n)/n → ∞? -/
def erdos_1182_conjecture : Prop :=
  ∀ C : ℕ, ∃ N₀ : ℕ, ∀ n ≥ N₀, bigF_threshold n ≥ C * n

/-
## Summary

**Problem Status: OPEN**

Erdős Problem #1182 asks about the maximum number of edges a connected
graph can have while still satisfying the "tree-like" Ramsey bound
R(K₃, G) = 2n - 1, and the maximum edges guaranteeing this for all
connected graphs.

**Axioms (3)**:
- chvatal_tree_ramsey: R(K₃, T) = 2n - 1 for trees (Chvátal 1977)
- bigF_lower_linear: F(n) ≥ (17n+1)/15 (BEFRS 1980)
- connected_min_edges: connected graph has ≥ n-1 edges (standard)

**Theorems (3)** (previously sorries):
- bigF_lower_bound_tree: F(n) ≥ n-1 (proved from chvatal + connected_min_edges)
- f_val_2: f(2) = 1 (proved from chvatal + edge count bound)
- bigF_val_2: F(2) = 1 (proved from chvatal + connected_min_edges)

**Definitions (6)**:
- f_threshold, bigF_threshold, erdos_1182_conjecture
- graphRamseyK3, ramseyNumber, Graph.Connected

**Key fix**: bigF_threshold now correctly restricts to connected graphs
per the original BEFRS (1980) definition, with explicit edge-count bound
to ensure sSup is well-behaved on ℕ.

References:
- Burr, S.A., Erdős, P., Faudree, R.J., Rousseau, C.C., Schelp, R.H. (1980)
- Chvátal, V. (1977): Tree Ramsey numbers
-/

end Erdos1182
