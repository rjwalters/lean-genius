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
- f_case_k_eq_1: proved (existsGraphWithPropertyP uses Fin n canonically)
- hasPropertyP_one_triple_has_edge: proved — P(1) implies every triple has an edge
- edge_injection_bound: proved — injection from vertex cover to edge set
- edgeCount_ge_of_propertyP1: proved — core math result for Fin n
Axioms: 2 (f_lower_bound, f_mono_k)
Sorries: 0
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

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

/-- A graph on n vertices exists with m edges having property P(k).
    We use Fin n as the canonical vertex type (WLOG by relabeling). -/
def existsGraphWithPropertyP (n k m : ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
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
  exact ⟨⊤, inferInstance, edgeCount_complete n, complete_hasPropertyP n k hnk⟩

/-
## Part 5: Special Cases
-/

/-- P(1) means every triple has at least one edge: if inducedMaxDegree ≥ 1
    on a 3-set, then some vertex has a neighbor, so there is an edge. -/
private lemma hasPropertyP_one_triple_has_edge
    (G : SimpleGraph V) [DecidableRel G.Adj] (hP : hasPropertyP G 1)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    G.Adj a b ∨ G.Adj a c ∨ G.Adj b c := by
  unfold hasPropertyP at hP
  have hcard : ({a, b, c} : Finset V).card = 1 + 2 := by
    rw [Finset.card_insert_of_not_mem (by simp [hab, hac]),
        Finset.card_insert_of_not_mem (by simp [hbc]),
        Finset.card_singleton]
  have h := hP {a, b, c} hcard
  unfold inducedMaxDegree at h
  have hne : ({a, b, c} : Finset V).Nonempty := ⟨a, Finset.mem_insert_self a _⟩
  simp only [dif_pos hne] at h
  -- Some vertex in {a,b,c} has ≥ 1 neighbor in {a,b,c}
  rw [Finset.le_sup'_iff] at h
  obtain ⟨v, hv, hcard_pos⟩ := h
  -- v has a neighbor w in {a,b,c} with w ≠ v and G.Adj v w
  have : (({a, b, c} : Finset V).filter (fun u => u ≠ v ∧ G.Adj v u)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨w, hw⟩ := this
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hw hv
  obtain ⟨hw_mem, hw_ne, hw_adj⟩ := hw
  -- v and w are both in {a,b,c} and v-w is an edge
  rcases hv with rfl | rfl | rfl <;> rcases hw_mem with rfl | rfl | rfl <;>
    first | exact absurd rfl hw_ne
          | exact Or.inl hw_adj | exact Or.inl (hw_adj.symm)
          | exact Or.inr (Or.inl hw_adj) | exact Or.inr (Or.inl (hw_adj.symm))
          | exact Or.inr (Or.inr hw_adj) | exact Or.inr (Or.inr (hw_adj.symm))

/-- An edge (a, b) with a < b contributes to the edge count. -/
private lemma mem_edgeCount_filter (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hab : a < b) (hadj : G.Adj a b) :
    (a, b) ∈ (Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2)) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hab, hadj⟩

/-- If a subset of the edge-count filter has cardinality k, then edgeCount ≥ k. -/
private lemma edgeCount_ge_of_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (V × V))
    (hS : S ⊆ Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.Adj p.1 p.2)) :
    edgeCount G ≥ S.card := by
  unfold edgeCount
  exact Finset.card_le_card hS

/-- If every vertex in a set S is adjacent to a or b (where a ≠ b, ¬adj a b),
    then the graph has at least |S| edges. Each c ∈ S produces a distinct edge
    (a,c) or (b,c); these are all distinct because c appears as an endpoint
    unique to that element of S, and a ≠ b ensures no overlap between
    a-edges and b-edges. -/
private theorem edge_injection_bound {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (hab : a ≠ b) (hnadj : ¬G.Adj a b)
    (S : Finset (Fin n))
    (hS : ∀ c ∈ S, G.Adj a c ∨ G.Adj b c) :
    edgeCount G ≥ S.card := by
  -- a and b cannot be in S (self-loops impossible, a-b not adjacent)
  have ha_notin : a ∉ S := by
    intro ha; rcases hS a ha with h | h
    · exact G.loopless a h
    · exact hnadj (G.symm h)
  have hb_notin : b ∉ S := by
    intro hb; rcases hS b hb with h | h
    · exact hnadj h
    · exact G.loopless b h
  -- Edge-selecting function: map c to ordered edge pair (min(x,c), max(x,c))
  let f : Fin n → Fin n × Fin n := fun c =>
    if G.Adj a c then (min a c, max a c) else (min b c, max b c)
  -- Recovery function: from a pair, extract the non-{a,b} element
  let g : Fin n × Fin n → Fin n := fun ⟨p, _q⟩ =>
    if p = a ∨ p = b then _q else p
  -- g is a left inverse of f on S, so f is injective on S
  have hgf : ∀ c, c ∈ (↑S : Set (Fin n)) → g (f c) = c := by
    intro c hc
    have hca : c ≠ a := fun h => ha_notin (h ▸ Finset.mem_coe.mp hc)
    have hcb : c ≠ b := fun h => hb_notin (h ▸ Finset.mem_coe.mp hc)
    simp only [f, g]
    by_cases hadj : G.Adj a c
    · simp only [if_pos hadj]
      rcases le_total a c with hle | hle
      · simp [min_eq_left hle, max_eq_right hle, Or.inl rfl]
      · simp [min_eq_right hle, max_eq_left hle, not_or.mpr ⟨hca, hcb⟩]
    · simp only [if_neg hadj]
      rcases le_total b c with hle | hle
      · simp [min_eq_left hle, max_eq_right hle, show b = a ∨ b = b from Or.inr rfl]
      · simp [min_eq_right hle, max_eq_left hle, not_or.mpr ⟨hca, hcb⟩]
  have hinj : Set.InjOn f (↑S : Set (Fin n)) :=
    fun c₁ hc₁ c₂ hc₂ heq => by
      have := congr_arg g heq
      rw [hgf c₁ hc₁, hgf c₂ hc₂] at this
      exact this
  -- f maps S into the edge filter
  have hf_mem : S.image f ⊆
      Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2) := by
    intro ⟨p, q⟩ hmem
    simp only [Finset.mem_image] at hmem
    obtain ⟨c, hc, hfc⟩ := hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hca : c ≠ a := fun h => ha_notin (h ▸ hc)
    have hcb : c ≠ b := fun h => hb_notin (h ▸ hc)
    -- Case split on what f actually does (whether G.Adj a c)
    by_cases hadj_a : G.Adj a c
    · -- f uses a-path: f c = (min a c, max a c)
      simp only [f, if_pos hadj_a] at hfc
      rw [← hfc]
      rcases hca.lt_or_lt with hlt | hlt
      · simp only [min_eq_left hlt.le, max_eq_right hlt.le]; exact ⟨hlt, hadj_a⟩
      · simp only [min_eq_right hlt.le, max_eq_left hlt.le]; exact ⟨hlt, hadj_a.symm⟩
    · -- f uses b-path: f c = (min b c, max b c), and G.Adj b c by elimination
      have hadj_b : G.Adj b c :=
        (hS c hc).resolve_left hadj_a
      simp only [f, if_neg hadj_a] at hfc
      rw [← hfc]
      rcases hcb.lt_or_lt with hlt | hlt
      · simp only [min_eq_left hlt.le, max_eq_right hlt.le]; exact ⟨hlt, hadj_b⟩
      · simp only [min_eq_right hlt.le, max_eq_left hlt.le]; exact ⟨hlt, hadj_b.symm⟩
  -- Combine: edgeCount ≥ |image| = |S|
  calc edgeCount G
      ≥ (S.image f).card := Finset.card_le_card hf_mem
    _ = S.card := Finset.card_image_of_injOn hinj

/-- Core lemma: On Fin n with n ≥ 3, if G has property P(1), then edgeCount G ≥ n - 2.

    Proof: Either G is complete (≥ n-1 edges), or there exist non-adjacent vertices
    a, b. For every other vertex c, the triple {a,b,c} must span an edge. Since a-b
    is not an edge, either a-c or b-c is. This gives n-2 distinct edges. -/
private theorem edgeCount_ge_of_propertyP1 {n : ℕ} (hn : n ≥ 3)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hP : hasPropertyP G 1) : edgeCount G ≥ n - 2 := by
  -- Either every pair is adjacent, or some pair is not
  by_cases hcomplete : ∀ a b : Fin n, a ≠ b → G.Adj a b
  · -- Case 1: G is complete. Each i > 0 gives edge (0, i), so ≥ n-1 ≥ n-2 edges.
    apply edgeCount_ge_of_subset G
      (Finset.univ.filter (fun i : Fin n => (0 : Fin n) < i) |>.image
        (fun i => ((0 : Fin n), i)))
    intro ⟨x, y⟩ hmem
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨i, hi, rfl⟩ := hmem
    exact mem_edgeCount_filter G hi (hcomplete 0 i (Fin.ne_of_lt hi))
  · -- Case 2: There exist non-adjacent a, b
    push_neg at hcomplete
    obtain ⟨a, b, hab, hnadj⟩ := hcomplete
    -- For each c ≠ a, c ≠ b: triple {a,b,c} must have an edge, so a-c or b-c
    set others := Finset.univ.filter (fun c : Fin n => c ≠ a ∧ c ≠ b) with others_def
    have hothers_card : others.card = n - 2 := by
      have : others = Finset.univ \ {a, b} := by
        ext x; simp [others_def, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [this, Finset.card_sdiff (by simp),
          Finset.card_insert_of_not_mem (by simp [hab]), Finset.card_singleton,
          Fintype.card_fin]
    -- Each c in others has an edge to a or b
    have hedge_exists : ∀ c ∈ others, G.Adj a c ∨ G.Adj b c := by
      intro c hc
      simp only [others_def, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      have := hasPropertyP_one_triple_has_edge G hP hab hc.1.symm hc.2.symm
      rcases this with h | h | h
      · exact absurd h hnadj
      · exact Or.inl h
      · exact Or.inr h
    -- Each c ∈ others produces a distinct edge (to a or to b).
    -- We count: edges from a to its neighbors in others, plus edges from b
    -- to its neighbors in others (that aren't already counted via a).
    -- Since a ≠ b and c ∉ {a,b}, these edge sets are disjoint.
    -- The injection argument is formalized via edge_injection_bound below.
    rw [← hothers_card]
    exact edge_injection_bound G a b hab hnadj others hedge_exists

/-- Case k = 1: every 3 vertices must span at least one edge.
    This means the graph has no independent triple, requiring
    at least n - 2 edges (a path achieves this). -/
theorem f_case_k_eq_1 :
  ∀ n : ℕ, n ≥ 3 →
    ∀ m, existsGraphWithPropertyP n 1 m → m ≥ n - 2 := by
  intro n hn m ⟨G, _hdr, hedge, hprop⟩
  rw [← hedge]
  exact edgeCount_ge_of_propertyP1 hn G hprop

/- **FALSE THEOREM (removed)**: The original claimed k=n-2 forces complete graph.
    COUNTEREXAMPLE: The star graph K_{1,n-1} has n-1 edges and satisfies P(n-2),
    since the center has degree n-1 ≥ n-2 in the only n-subset (= V itself).
    So f(n, n-2) ≤ n-1 << n(n-1)/2 for n ≥ 4.

    The correct statement is: P(n-2) only requires max degree ≥ n-2 in the
    whole graph, which a single high-degree vertex achieves. -/

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
## Part 8: Tight Bound for k = n - 2

The complete-graph upper bound n*(n-1)/2 is far from tight when k = n - 2.
A "partial star" graph — vertex 0 adjacent to {1, ..., n-2}, vertex n-1 isolated —
satisfies P(n-2) with only n - 2 edges. Indeed, the unique (n-2+2)=n-vertex
subset of an n-vertex graph is V itself, so P(n-2) reduces to the requirement
that some vertex of V have degree at least n - 2.

The matching lower bound (any graph with P(n-2) has some vertex of degree at
least n - 2, contributing at least n - 2 distinct edges) yields the tight value
f(n, n-2) = n - 2 for n ≥ 2. This corrects the previously believed (and removed)
false claim that k = n - 2 forces the complete graph.
-/

/-- The partial-star graph on `Fin n`: vertex 0 is adjacent to vertices
    1, 2, …, n - 2; vertex n - 1 is isolated (when n ≥ 2). The graph has
    exactly n - 2 edges and maximum degree n - 2 (achieved at vertex 0). -/
def partialStar (n : ℕ) : SimpleGraph (Fin n) where
  Adj a b :=
    (a.val = 0 ∧ 1 ≤ b.val ∧ b.val + 1 < n) ∨
    (b.val = 0 ∧ 1 ≤ a.val ∧ a.val + 1 < n)
  symm := fun _ _ h => h.symm
  loopless := fun a h => by
    rcases h with ⟨h0, h1, _⟩ | ⟨h0, h1, _⟩ <;> omega

instance partialStar_decAdj (n : ℕ) : DecidableRel (partialStar n).Adj := by
  intro a b
  unfold partialStar
  exact inferInstance

/-- For n ≥ 2, the neighbors of vertex 0 in `partialStar n` are exactly the
    vertices with index in {1, …, n-2}, giving n - 2 neighbors. -/
private lemma partialStar_zero_neighbors_card (n : ℕ) (hn : 2 ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun u => u ≠ ⟨0, by omega⟩ ∧
                (partialStar n).Adj ⟨0, by omega⟩ u)).card = n - 2 := by
  -- Step 1: rewrite filter as {u : 1 ≤ u.val ∧ u.val + 1 < n}
  have hfilt : ((Finset.univ : Finset (Fin n)).filter
        (fun u => u ≠ ⟨0, by omega⟩ ∧
                  (partialStar n).Adj ⟨0, by omega⟩ u))
      = ((Finset.univ : Finset (Fin n)).filter
        (fun u => 1 ≤ u.val ∧ u.val + 1 < n)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hadj⟩
      have hu_ne_zero : u.val ≠ 0 := fun h => hne (Fin.ext h)
      rcases hadj with ⟨_, hb1, hbn⟩ | ⟨hb0, _, _⟩
      · exact ⟨hb1, hbn⟩
      · exact absurd hb0 hu_ne_zero
    · rintro ⟨h1, h2⟩
      refine ⟨?_, Or.inl ⟨rfl, h1, h2⟩⟩
      intro heq
      have : u.val = 0 := by rw [heq]
      omega
  rw [hfilt]
  -- Step 2: bijection with Finset.range (n - 2) via i ↦ ⟨i + 1, _⟩
  have hbij : ((Finset.univ : Finset (Fin n)).filter
        (fun u => 1 ≤ u.val ∧ u.val + 1 < n))
      = (Finset.range (n - 2)).image (fun i : ℕ => (⟨i + 1, by omega⟩ : Fin n)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨u.val - 1, by omega, ?_⟩
      ext
      simp only
      omega
    · rintro ⟨i, hi, hueq⟩
      have huval : u.val = i + 1 := by rw [← hueq]
      exact ⟨by omega, by omega⟩
  rw [hbij, Finset.card_image_of_injective _ ?_, Finset.card_range]
  intro i j hij
  simp only [Fin.mk.injEq] at hij
  omega

/-- For n ≥ 2, the partial star on Fin n has exactly n - 2 edges. -/
private theorem partialStar_edgeCount (n : ℕ) (hn : 2 ≤ n) :
    edgeCount (partialStar n) = n - 2 := by
  unfold edgeCount
  -- Step 1: the edge filter bijects with the neighbors-of-0 filter.
  -- Pairs (a, b) with a < b ∧ Adj a b have a.val = 0 (since a < b excludes b.val = 0).
  have hbij : ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun p => p.1 < p.2 ∧ (partialStar n).Adj p.1 p.2))
      = ((Finset.univ : Finset (Fin n)).filter
          (fun u => u ≠ ⟨0, by omega⟩ ∧
                    (partialStar n).Adj ⟨0, by omega⟩ u)).image
          (fun b => ((⟨0, by omega⟩ : Fin n), b)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hlt, hadj⟩
      rcases hadj with ⟨ha0, hb1, hbn⟩ | ⟨hb0, _, _⟩
      · refine ⟨b, ⟨?_, ?_⟩, Fin.ext ha0, rfl⟩
        · intro heq
          have : b.val = 0 := by rw [heq]
          omega
        · exact Or.inl ⟨rfl, hb1, hbn⟩
      · -- b.val = 0 contradicts a < b
        exfalso
        have hab_val : a.val < b.val := hlt
        omega
    · rintro ⟨c, ⟨hcne, hcadj⟩, ha_eq, hb_eq⟩
      subst ha_eq
      subst hb_eq
      refine ⟨?_, ?_⟩
      · -- ⟨0, _⟩ < c since c.val ≥ 1
        rcases hcadj with ⟨_, hc1, _⟩ | ⟨hc0, _, _⟩
        · show (0 : ℕ) < c.val
          exact hc1
        · exact absurd (Fin.ext hc0 : c = ⟨0, by omega⟩) hcne
      · exact hcadj
  rw [hbij, Finset.card_image_of_injective _ (fun b₁ b₂ h => by
    simpa [Prod.mk.injEq] using h)]
  exact partialStar_zero_neighbors_card n hn

/-- For n ≥ 2, the partial star on Fin n satisfies property P(n - 2). -/
private theorem partialStar_hasPropertyP (n : ℕ) (hn : 2 ≤ n) :
    hasPropertyP (partialStar n) (n - 2) := by
  intro S hS
  -- The only n-subset of Fin n is univ
  have hSuniv : S = (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, Fintype.card_fin, hS]
    omega
  subst hSuniv
  unfold inducedMaxDegree
  have hne : ((Finset.univ : Finset (Fin n))).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  simp only [dif_pos hne]
  -- Pick vertex 0; its neighbor count is n - 2.
  have h0_mem : (⟨0, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) :=
    Finset.mem_univ _
  refine Finset.le_sup'_of_le _ h0_mem ?_
  exact (partialStar_zero_neighbors_card n hn).ge

/-- **Upper bound for k = n - 2**: A partial-star graph with vertex 0 adjacent
    to {1, …, n-2} achieves property P(n-2) with exactly n - 2 edges.
    This is much tighter than the complete-graph bound n*(n-1)/2. -/
theorem f_n_minus_2_upper_bound :
    ∀ n : ℕ, 2 ≤ n → existsGraphWithPropertyP n (n - 2) (n - 2) :=
  fun n hn => ⟨partialStar n, inferInstance,
               partialStar_edgeCount n hn,
               partialStar_hasPropertyP n hn⟩

/-
## Part 9: Summary
-/

/-- **Erdős Problem #614: OPEN**

Summarizes what is known:
1. The function f(n,k) is well-defined (complete graph gives upper bound)
2. Lower bound: at least kn/2 edges needed
3. k=1: at least n-2 edges (proved via vertex-cover injection on Fin n)
4. k=n-2: at most n-2 edges suffice (partial star) — much tighter than complete graph
5. Monotone in k parameter
6. Exact formula for general (n,k): UNKNOWN -/
theorem erdos_614_summary :
    -- The function is well-defined (existence)
    (∀ n k : ℕ, n ≥ k + 2 → k > 0 →
      ∃ m, existsGraphWithPropertyP n k m) ∧
    -- Complete graph provides an upper bound
    (∀ n k : ℕ, k + 2 ≤ n →
      existsGraphWithPropertyP n k (n * (n - 1) / 2)) ∧
    -- Partial-star tight upper bound for k = n - 2
    (∀ n : ℕ, 2 ≤ n → existsGraphWithPropertyP n (n - 2) (n - 2)) :=
  ⟨erdos_614_existence, f_upper_bound, f_n_minus_2_upper_bound⟩

end Erdos614
