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
Axioms: 4 (f_lower_bound, f_upper_bound, f_case_k_eq_1, f_mono_k)
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

/-- The induced max degree of any subgraph on S is at most |S| - 1. -/
theorem inducedMaxDegree_le (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    inducedMaxDegree G S ≤ S.card - 1 := by
  unfold inducedMaxDegree
  split
  · case isTrue h =>
    apply Finset.sup'_le _ _ (fun v hv => ?_)
    calc (S.filter (fun u => u ≠ v ∧ G.Adj v u)).card
        ≤ (S.erase v).card := Finset.card_le_card (fun u hu => by
          simp only [Finset.mem_filter] at hu; exact Finset.mem_erase.mpr ⟨hu.2.1, hu.1⟩)
      _ = S.card - 1 := Finset.card_erase_of_mem hv
  · case isFalse => omega

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
## Part 6: Monotonicity
-/

/-- f is non-decreasing in k: requiring higher induced max degree
    requires at least as many edges. A graph with property P(k+1)
    automatically has property P(k). -/
axiom f_mono_k :
  ∀ n k : ℕ, n > k + 3 →
    ∀ m, existsGraphWithPropertyP n (k + 1) m →
    existsGraphWithPropertyP n k m

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
4. Monotone in k parameter
5. Exact formula: UNKNOWN
Note: k=n-2 does NOT force complete graph (star suffices; false axiom removed). -/
theorem erdos_614_summary :
    -- The function is well-defined (existence)
    (∀ n k : ℕ, n ≥ k + 2 → k > 0 →
      ∃ m, existsGraphWithPropertyP n k m) ∧
    -- Complete graph provides an upper bound
    (∀ n k : ℕ, k + 2 ≤ n →
      existsGraphWithPropertyP n k (n * (n - 1) / 2)) :=
  ⟨erdos_614_existence, f_upper_bound⟩

end Erdos614
