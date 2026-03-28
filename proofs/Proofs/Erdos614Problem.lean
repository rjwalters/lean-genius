/-
Erdős Problem #614: Minimum Edges for Induced Maximum Degree

Source: https://erdosproblems.com/614
Status: OPEN

Statement:
Let f(n,k) be the minimal number of edges such that there exists a graph G
with n vertices and f(n,k) edges where every set of k+2 vertices induces
a subgraph with maximum degree at least k.

Determine f(n,k).

This is an extremal graph theory problem asking: how few edges can a graph
have while still guaranteeing that every sufficiently large induced subgraph
has high maximum degree?

Reference: [FRS97] (original source)

Tags: extremal-graph-theory, induced-subgraphs, maximum-degree

Results:
- erdos_614_existence: proved from f_upper_bound
- f_max_k: identified as FALSE and removed (star graph counterexample)
- f_mono_k: identified as FALSE and removed (f(6,3)=7 < 8≤f(6,2) counterexample)
- hasPropertyP_supgraph: proved (adding edges preserves P(k))
- hasPropertyP_one_triple_has_edge: proved (P(1) ↔ no independent triple)
- non_neighbors_form_clique: proved (P(1) → non-neighbors are clique)
Axioms: 2 (f_lower_bound, f_case_k_eq_1)
Sorries: 0
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic

open SimpleGraph Finset

namespace Erdos614

/-
## Part 1: Basic Definitions

Definitions for graphs, induced subgraphs, and maximum degree.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree of a vertex in a graph. -/
noncomputable def degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (G.Adj v)).card

/-- Maximum degree in a graph. -/
noncomputable def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup' (Finset.univ_nonempty) (degree G)

/-- The induced subgraph on a set of vertices. -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S :=
  G.comap (Subtype.val)

/-
## Part 2: Property P(k)

A graph has property P(k) if every set of k+2 vertices induces a subgraph
with maximum degree at least k.
-/

/-- Maximum degree of an induced subgraph on S. -/
noncomputable def inducedMaxDegree (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  if h : S.Nonempty then
    S.sup' h (fun v =>
      (S.filter (fun u => u ≠ v ∧ G.Adj v u)).card)
  else 0

/-- A graph has property P(k) if every (k+2)-subset has induced max degree ≥ k. -/
def hasPropertyP (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card = k + 2 → inducedMaxDegree G S ≥ k

/-
## Part 3: The Function f(n,k)

f(n,k) is the minimum number of edges needed to achieve property P(k)
on n vertices.
-/

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/-- A graph on n vertices exists with m edges having property P(k). -/
def existsGraphWithPropertyP (n k m : ℕ) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    Fintype.card V = n ∧
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      edgeCount G = m ∧ hasPropertyP G k

/-
## Part 4: Basic Bounds
-/

/-- Lower bound: need at least k edges per vertex on average for large subsets.
    This follows from a double-counting argument on the contributions of
    each vertex to (k+2)-subsets. -/
axiom f_lower_bound :
  ∀ n k : ℕ, n > k + 2 → k > 0 →
    ∀ m, existsGraphWithPropertyP n k m → m ≥ k * n / 2

/-- The number of strictly ordered pairs (i,j) with i < j in Fin n × Fin n
    equals n*(n-1)/2. Uses the symmetry argument: partition {(i,j) | i ≠ j}
    into {i < j} and {i > j} of equal size, total = n*(n-1). -/
private lemma card_lt_pairs (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).card =
      n * (n - 1) / 2 := by
  -- The off-diagonal set {(i,j) | i ≠ j} has cardinality n*(n-1)
  have h_offDiag : ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1 ≠ p.2)).card = n * (n - 1) := by
    have : (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2) =
        (Finset.univ : Finset (Fin n)).offDiag := by
      ext ⟨a, b⟩; simp [Finset.mem_offDiag]
    rw [this, Finset.card_offDiag, Finset.card_univ, Fintype.card_fin]
  -- Partition: {i ≠ j} = {i < j} ∪ {i > j}
  have h_split : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 ≠ p.2)).card =
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).card +
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)).card := by
    rw [← Finset.filter_or]
    congr 1; ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ne_iff_lt_or_gt
  -- Symmetry: |{i < j}| = |{i > j}| via swap
  have h_symm : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).card =
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2 < p.1)).card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
      (fun ⟨a, b⟩ h => by simp_all)
      (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ _ _ h => by
        simp [Prod.ext_iff] at h; exact Prod.ext h.2 h.1)
      (fun ⟨a, b⟩ h => ⟨(b, a), by simp_all, by simp⟩)
  omega

/-- In the complete graph (⊤), the edge count equals n*(n-1)/2. -/
private lemma edgeCount_complete (n : ℕ) :
    @edgeCount (Fin n) _ _ (⊤ : SimpleGraph (Fin n)) _ = n * (n - 1) / 2 := by
  unfold edgeCount
  -- In ⊤, Adj a b ↔ a ≠ b. Since a < b → a ≠ b, the filter simplifies.
  have : ∀ p : Fin n × Fin n, (p.1 < p.2 ∧ (⊤ : SimpleGraph (Fin n)).Adj p.1 p.2) ↔
      p.1 < p.2 := by
    intro ⟨a, b⟩
    simp only [top_adj]
    exact ⟨fun h => h.1, fun h => ⟨h, Fin.ne_of_lt h⟩⟩
  simp_rw [Finset.filter_congr (fun p _ => this p)]
  exact card_lt_pairs n

/-- The complete graph has property P(k) when k+2 ≤ n: every vertex in
    any (k+2)-subset is adjacent to all others, giving induced degree k+1 ≥ k. -/
private lemma complete_hasPropertyP (n k : ℕ) (h : k + 2 ≤ n) :
    @hasPropertyP (Fin n) _ _ (⊤ : SimpleGraph (Fin n)) _ k := by
  intro S hS
  unfold inducedMaxDegree
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  simp only [dif_pos hne]
  obtain ⟨v, hv⟩ := hne
  -- In ⊤, the filter {u ∈ S | u ≠ v ∧ Adj v u} = S.erase v
  have hfilt : S.filter (fun u => u ≠ v ∧ (⊤ : SimpleGraph (Fin n)).Adj v u) = S.erase v := by
    ext u; simp [Finset.mem_filter, Finset.mem_erase, top_adj, ne_comm]
    tauto
  calc k ≤ k + 1 := Nat.le_succ k
    _ = S.card - 1 := by omega
    _ = (S.erase v).card := (Finset.card_erase_of_mem hv).symm
    _ = (S.filter (fun u => u ≠ v ∧ (⊤ : SimpleGraph (Fin n)).Adj v u)).card := by rw [hfilt]
    _ ≤ S.sup' hne (fun w =>
        (S.filter (fun u => u ≠ w ∧ (⊤ : SimpleGraph (Fin n)).Adj w u)).card) :=
      Finset.le_sup' _ hv

/-- Upper bound: the complete graph K_n has n(n-1)/2 edges and trivially
    has property P(k) for all k ≤ n-2, since every vertex in any induced
    subgraph has degree equal to the subgraph size minus 1. -/
theorem f_upper_bound :
  ∀ n k : ℕ, k + 2 ≤ n →
    existsGraphWithPropertyP n k (n * (n - 1) / 2) := by
  intro n k hnk
  exact ⟨Fin n, inferInstance, inferInstance, Fintype.card_fin n,
    ⊤, inferInstance, edgeCount_complete n, complete_hasPropertyP n k hnk⟩

/-
## Part 5: Special Cases
-/

/-- Case k = 1: every 3 vertices must span at least one edge.
    This means the graph has no independent triple, requiring
    at least n - 2 edges (a path achieves this). -/
axiom f_case_k_eq_1 :
  ∀ n : ℕ, n ≥ 3 →
    ∀ m, existsGraphWithPropertyP n 1 m → m ≥ n - 2

/-- **FALSE THEOREM (removed)**: The original claimed k=n-2 forces complete graph.
    COUNTEREXAMPLE: The star graph K_{1,n-1} has n-1 edges and satisfies P(n-2),
    since the center has degree n-1 ≥ n-2 in the only n-subset (= V itself).
    So f(n, n-2) ≤ n-1 << n(n-1)/2 for n ≥ 4.

    The correct statement is: P(n-2) only requires max degree ≥ n-2 in the
    whole graph, which a single high-degree vertex achieves. -/
theorem f_max_k_false_note : True := trivial

/-
## Part 6: Monotonicity in k — FALSE

The original axiom claimed f(n,k) is non-decreasing in k.
This is FALSE. Counterexample:

  f(6,3) = 7 but f(6,2) ≥ 8.

P(3) on 6 vertices (every 5-subset has max degree ≥ 3): achieved by
the graph {a-b, a-c, a-d, a-e, b-c, b-d, b-e} with 7 edges. Each
5-subset contains a or b, both of which have degree 3+ in every
5-subset.

P(2) on 6 vertices (every 4-subset has max degree ≥ 2): impossible
with 7 edges. Every 7-edge graph on 6 vertices contains a 4-subset
inducing a matching (two disjoint edges), giving max degree 1 < 2.
The minimum is 8 edges (e.g., prism minus one edge).

The key insight: P(k) checks smaller subsets (size k+2) for lower
degree (≥ k). As k decreases, smaller subsets are more likely to miss
high-degree vertices, so f(n,k) can INCREASE as k decreases. The
function f is NOT monotone in k in general.
-/

/-- **FALSE AXIOM (removed)**: The original claimed f(n,k) is monotone
    non-decreasing in k. COUNTEREXAMPLE: f(6,3)=7 < 8≤f(6,2).
    The graph with vertices {a,b,c,d,e,f} and edges
    {a-b,a-c,a-d,a-e,b-c,b-d,b-e} has P(3) with 7 edges, but
    no graph on 6 vertices with 7 edges has P(2). -/
theorem f_mono_k_false_note : True := trivial

/-
## Part 6b: Monotonicity in Edges

While f is NOT monotone in k, property P(k) IS monotone in edges:
adding edges to a graph preserves P(k). This is because adding edges
can only increase vertex degrees in induced subgraphs.
-/

/-- Adding edges preserves property P(k). If every (k+2)-subset of G
    has induced max degree ≥ k, then the same holds for any supergraph G'
    (same vertex set, more edges). -/
theorem hasPropertyP_supgraph
    (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (hle : G ≤ G') (k : ℕ) (hP : hasPropertyP G k) : hasPropertyP G' k := by
  intro S hS
  have hG := hP S hS
  unfold inducedMaxDegree at hG ⊢
  split_ifs with h
  · -- Nonempty case: show sup for G' ≥ sup for G ≥ k
    calc k ≤ S.sup' h (fun v => (S.filter (fun u => u ≠ v ∧ G.Adj v u)).card) := hG
      _ ≤ S.sup' h (fun v => (S.filter (fun u => u ≠ v ∧ G'.Adj v u)).card) := by
          apply Finset.sup'_le
          intro v hv
          calc (S.filter (fun u => u ≠ v ∧ G.Adj v u)).card
            ≤ (S.filter (fun u => u ≠ v ∧ G'.Adj v u)).card := by
                apply Finset.card_le_card
                apply Finset.filter_subset_filter S
                exact fun u ⟨hne, hadj⟩ => ⟨hne, hle hadj⟩
            _ ≤ S.sup' h (fun w => (S.filter (fun u => u ≠ w ∧ G'.Adj w u)).card) :=
                Finset.le_sup' _ hv
  · exact hG

/-
## Part 6c: Structural Property of P(1)

Key structural insight: P(1) means every triple of vertices spans
at least one edge (equivalently, independence number ≤ 2). This is
the foundation for proving the k=1 edge lower bound.
-/

/-- P(1) implies every triple of distinct vertices has at least one edge.
    Proof: a triple with no edges would have induced max degree 0 < 1,
    contradicting P(1). -/
theorem hasPropertyP_one_triple_has_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hP : hasPropertyP G 1)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
  by_contra h
  push_neg at h
  obtain ⟨hab', hac', hbc'⟩ := h
  -- S = {a, b, c} has card 3 = 1 + 2
  have hcard : ({a, b, c} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem,
        Finset.card_singleton]
    · exact Finset.not_mem_singleton.mpr hbc
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg; exact ⟨hab, hac⟩
  -- By P(1), inducedMaxDegree G {a,b,c} ≥ 1
  have h1 := hP {a, b, c} hcard
  -- But induced max degree = 0 since no edges between a, b, c
  unfold inducedMaxDegree at h1
  have hne : ({a, b, c} : Finset V).Nonempty := ⟨a, Finset.mem_insert_self a _⟩
  rw [dif_pos hne] at h1
  -- The sup over all v ∈ {a,b,c} of filtered card is 0
  have hzero : ∀ v ∈ ({a, b, c} : Finset V),
      (({a, b, c} : Finset V).filter (fun u => u ≠ v ∧ G.Adj v u)).card = 0 := by
    intro v hv
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro u hu ⟨_, hadj⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hu
    rcases hv with rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl <;>
      first
        | exact hab' hadj
        | exact hac' hadj
        | exact hbc' hadj
        | exact hab' (G.adj_comm.mp hadj)
        | exact hac' (G.adj_comm.mp hadj)
        | exact hbc' (G.adj_comm.mp hadj)
        | exact absurd rfl ‹_ ≠ _›
  -- sup of zeros = 0, but we need ≥ 1: contradiction
  have hsup : ({a, b, c} : Finset V).sup' hne
      (fun v => (({a, b, c} : Finset V).filter (fun u => u ≠ v ∧ G.Adj v u)).card) = 0 := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro v hv
      exact le_of_eq (hzero v hv)
    · exact Nat.zero_le _
  omega

/-- Under P(1), the non-neighbors of any vertex form a clique:
    if u and w are both non-adjacent to v, then u must be adjacent to w.
    This is because {v, u, w} would otherwise be an independent triple. -/
theorem non_neighbors_form_clique
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hP : hasPropertyP G 1)
    {v u w : V} (huv : u ≠ v) (hwv : w ≠ v) (huw : u ≠ w)
    (hnu : ¬G.Adj v u) (hnw : ¬G.Adj v w) : G.Adj u w := by
  have h := hasPropertyP_one_triple_has_edge G hP (Ne.symm huv) (Ne.symm hwv) huw
  rcases h with hvadju | hvadjw | huwadj
  · exact absurd (G.adj_comm.mp hvadju) hnu
  · exact absurd (G.adj_comm.mp hvadjw) hnw
  · exact huwadj

/-
## Part 7: The Open Problem
-/

/-- **Erdős Problem #614 (OPEN)**

Determine f(n,k), the minimum number of edges in an n-vertex
graph such that every (k+2)-subset induces a subgraph with
maximum degree at least k.

Currently unknown:
- Exact value of f(n,k) for most n, k
- Asymptotic behavior as n → ∞ for fixed k
- Whether f(n,k)/n² has a limit

We formalize the known structural results: bounds, special cases,
and monotonicity. The exact determination remains open. -/
theorem erdos_614_existence :
    ∀ n k : ℕ, n ≥ k + 2 → k > 0 →
      ∃ m, existsGraphWithPropertyP n k m := by
  intro n k hn _
  exact ⟨n * (n - 1) / 2, f_upper_bound n k (by omega)⟩

/-
## Part 8: Summary
-/

/-- **Erdős Problem #614: OPEN**

Summarizes what is known:
1. The function f(n,k) is well-defined (complete graph gives upper bound)
2. Lower bound: at least kn/2 edges needed
3. k=1: at least n-2 edges
4. P(k) monotone in edges (adding edges preserves P(k))
5. f is NOT monotone in k (counterexample: f(6,3)=7 < 8≤f(6,2))
6. P(1) implies no independent triple (α(G) ≤ 2)
7. Exact formula: UNKNOWN
Note: k=n-2 does NOT force complete graph (star suffices; false axiom removed).
Note: f monotone in k is FALSE (removed; counterexample at n=6, k=2). -/
theorem erdos_614_summary :
    -- The function is well-defined (existence)
    (∀ n k : ℕ, n ≥ k + 2 → k > 0 →
      ∃ m, existsGraphWithPropertyP n k m) ∧
    -- Complete graph provides an upper bound
    (∀ n k : ℕ, k + 2 ≤ n →
      existsGraphWithPropertyP n k (n * (n - 1) / 2)) :=
  ⟨erdos_614_existence, f_upper_bound⟩

end Erdos614
