/-
# Erdős Problem #533: Triangle-Free Subsets in K₅-Free Dense Graphs

If a graph G on n vertices has no K₅ and at least δn² edges (for any δ > 0),
must G contain a triangle-free induced subgraph on ≫_δ n vertices?

Known results:
- True when δ > 1/16: Erdős–Hajnal–Simonovits–Sós–Szemerédi
- True for K₄-free (instead of K₅-free) for all δ > 0: same authors
- Fails for K₇-free at δ = 1/4: Erdős–Rogers construction

Status: OPEN.

Reference: https://erdosproblems.com/533
-/

import Mathlib

/- ## Definitions -/

/-- A simple graph on n vertices, represented by its edge set. -/
structure SGraph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ i j, adj i j → adj j i
  irrefl : ∀ i, ¬adj i i

/-- A set S of vertices forms a clique in G. -/
def IsClique {n : ℕ} (G : SGraph n) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → G.adj i j

/-- G contains a clique of size k. -/
def HasClique {n : ℕ} (G : SGraph n) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card = k ∧ IsClique G S

/-- The induced subgraph of G on vertex set S. -/
def InducedSubgraph {n : ℕ} (G : SGraph n) (S : Finset (Fin n)) :
    ∀ (i j : Fin n), i ∈ S → j ∈ S → Prop :=
  fun i j _ _ => G.adj i j

/-- A set S of vertices is triangle-free in G: no 3 vertices in S form a triangle. -/
def IsTriangleFree {n : ℕ} (G : SGraph n) (S : Finset (Fin n)) : Prop :=
  ¬∃ (a b c : Fin n), a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.adj a b ∧ G.adj b c ∧ G.adj a c

/-- The number of edges in G. -/
noncomputable def edgeCount {n : ℕ} (G : SGraph n) : ℕ :=
  Finset.card (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.adj p.1 p.2)
    (Finset.univ.product Finset.univ))

/- ## SimpleGraph Bridge -/

/-- Bridge SGraph to Mathlib's SimpleGraph for access to the full Mathlib graph theory API.
    This enables using Mathlib's clique, independent set, and Ramsey theory results. -/
def SGraph.toSimpleGraph {n : ℕ} (G : SGraph n) : SimpleGraph (Fin n) where
  Adj i j := G.adj i j
  symm := fun hab => G.symm _ _ hab
  loopless := G.irrefl

@[simp]
theorem SGraph.toSimpleGraph_adj {n : ℕ} (G : SGraph n) (i j : Fin n) :
    G.toSimpleGraph.Adj i j ↔ G.adj i j :=
  Iff.rfl

/- ## Basic Properties -/

/-- The empty vertex set is trivially a clique -/
theorem isClique_empty {n : ℕ} (G : SGraph n) : IsClique G ∅ :=
  fun _ hi => absurd hi (Finset.not_mem_empty _)

/-- The empty vertex set is trivially triangle-free -/
theorem isTriangleFree_empty {n : ℕ} (G : SGraph n) : IsTriangleFree G ∅ :=
  fun ⟨_, _, _, ha, _, _, _, _, _, _, _⟩ => absurd ha (Finset.not_mem_empty _)

/-- A clique on n vertices has at most n elements -/
theorem hasClique_le_n {n : ℕ} (G : SGraph n) (k : ℕ) (h : HasClique G k) :
    k ≤ n := by
  obtain ⟨S, hcard, _⟩ := h
  have : S.card ≤ Fintype.card (Fin n) := S.card_le_univ
  simp [Fintype.card_fin] at this
  omega

/-- A K₅-free graph on n ≤ 4 vertices is trivially K₅-free -/
theorem k5_free_of_small {n : ℕ} (G : SGraph n) (hn : n ≤ 4) : ¬HasClique G 5 := by
  intro h
  have := hasClique_le_n G 5 h
  omega

/-- A singleton is always triangle-free -/
theorem isTriangleFree_singleton {n : ℕ} (G : SGraph n) (v : Fin n) :
    IsTriangleFree G {v} := by
  intro ⟨a, b, _, ha, hb, _, hab, _, _, _, _⟩
  simp at ha hb
  exact absurd (ha.symm ▸ hb) hab

/-- Subsets of triangle-free sets are triangle-free -/
theorem isTriangleFree_subset {n : ℕ} (G : SGraph n) (S T : Finset (Fin n))
    (hTS : T ⊆ S) (hS : IsTriangleFree G S) : IsTriangleFree G T := by
  intro ⟨a, b, c, ha, hb, hc, hab, hbc, hac, eab, ebc, eac⟩
  exact hS ⟨a, b, c, hTS ha, hTS hb, hTS hc, hab, hbc, hac, eab, ebc, eac⟩

/-- Subsets of cliques are cliques -/
theorem isClique_subset {n : ℕ} (G : SGraph n) (S T : Finset (Fin n))
    (hTS : T ⊆ S) (hS : IsClique G S) : IsClique G T :=
  fun i hi j hj hij => hS i (hTS hi) j (hTS hj) hij

/-- If a graph has a k-clique and j ≤ k, it has a j-clique -/
theorem hasClique_mono {n : ℕ} (G : SGraph n) {j k : ℕ} (hjk : j ≤ k)
    (hk : HasClique G k) : HasClique G j := by
  obtain ⟨S, hcard, hclique⟩ := hk
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_smaller_set S j (hcard ▸ hjk)
  exact ⟨T, hTcard, isClique_subset G S T hTS hclique⟩

/-- Every graph has a 0-clique (empty set) -/
theorem hasClique_zero {n : ℕ} (G : SGraph n) : HasClique G 0 :=
  ⟨∅, Finset.card_empty, isClique_empty G⟩

/-- Every nonempty graph has a 1-clique (singleton) -/
theorem hasClique_one {n : ℕ} (G : SGraph n) (hn : 0 < n) : HasClique G 1 :=
  ⟨{⟨0, hn⟩}, Finset.card_singleton _, fun i hi j hj hij => by
    simp [Finset.mem_singleton] at hi hj; exact absurd (hi ▸ hj) hij⟩

/-- Any pair of vertices is triangle-free -/
theorem isTriangleFree_pair {n : ℕ} (G : SGraph n) (u v : Fin n) :
    IsTriangleFree G {u, v} := by
  intro ⟨a, b, c, ha, hb, hc, hab, hbc, hac, _, _, _⟩
  simp [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first | exact absurd rfl hab | exact absurd rfl hbc | exact absurd rfl hac

/-- A graph with no triangles has all subsets triangle-free -/
theorem isTriangleFree_of_no_triangle {n : ℕ} (G : SGraph n)
    (hG : ¬HasClique G 3) (S : Finset (Fin n)) : IsTriangleFree G S := by
  intro ⟨a, b, c, _, _, _, hab, hbc, hac, eab, ebc, eac⟩
  apply hG
  refine ⟨{a, b, c}, ?_, ?_⟩
  · have hab' : a ∉ ({b, c} : Finset _) := by simp [hab, hac]
    have hbc' : b ∉ ({c} : Finset _) := by simp [hbc]
    rw [Finset.card_insert_of_not_mem hab', Finset.card_insert_of_not_mem hbc',
        Finset.card_singleton]
  · intro i hi j hj hij
    simp [Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      first | exact absurd rfl hij | exact eab | exact ebc | exact eac |
      exact G.symm _ _ eab | exact G.symm _ _ ebc | exact G.symm _ _ eac

/-- Edge count is at most n², since we filter from the n × n product. -/
theorem edgeCount_le_sq {n : ℕ} (G : SGraph n) : edgeCount G ≤ n ^ 2 := by
  unfold edgeCount
  have h1 := Finset.card_le_card (Finset.filter_subset
    (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.adj p.1 p.2)
    (Finset.univ.product Finset.univ))
  have h2 : (Finset.univ.product (Finset.univ : Finset (Fin n))).card = n ^ 2 := by
    simp [Finset.card_product, sq]
  linarith

/-- The number of strictly ordered pairs (i,j) with i < j in Fin n equals n*(n-1)/2. -/
private lemma card_strict_upper_tri (n : ℕ) :
    ((Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).filter
      (fun p : Fin n × Fin n => p.1 < p.2)).card = n * (n - 1) / 2 := by
  -- Off-diagonal {(i,j) | i ≠ j} has n*(n-1) elements
  have h_od : ((Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).filter
      (fun p : Fin n × Fin n => p.1 ≠ p.2)).card = n * (n - 1) := by
    have : (Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).filter
        (fun p : Fin n × Fin n => p.1 ≠ p.2) = (Finset.univ : Finset (Fin n)).offDiag := by
      ext ⟨a, b⟩; simp [Finset.mem_offDiag]
    rw [this, Finset.card_offDiag, Finset.card_univ, Fintype.card_fin]
  -- Split: {i ≠ j} = {i < j} ∪ {i > j}
  have h_split : ((Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).filter
      (fun p : Fin n × Fin n => p.1 ≠ p.2)).card =
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 < p.2)).card +
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.2 < p.1)).card := by
    rw [← Finset.filter_or]
    congr 1; ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ne_iff_lt_or_gt
  -- Symmetry: |{i < j}| = |{i > j}| via the swap bijection
  have h_symm : ((Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).filter
      (fun p : Fin n × Fin n => p.1 < p.2)).card =
      ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.2 < p.1)).card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
      (fun ⟨a, b⟩ h => by simp_all)
      (fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ _ _ h => by
        simp [Prod.ext_iff] at h; exact Prod.ext h.2 h.1)
      (fun ⟨a, b⟩ h => ⟨(b, a), by simp_all, by simp⟩)
  omega

/-- **Tight edge bound**: A simple graph on n vertices has at most n*(n-1)/2 edges.
    Improves `edgeCount_le_sq` from n² to the exact maximum. -/
theorem edgeCount_le {n : ℕ} (G : SGraph n) : edgeCount G ≤ n * (n - 1) / 2 := by
  unfold edgeCount
  have h1 : (Finset.univ ×ˢ Finset.univ).filter
      (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.adj p.1 p.2)
      ⊆ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 < p.2) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
    exact hp.1
  linarith [Finset.card_le_card h1, card_strict_upper_tri n]

/-- Clique-freeness is upward-closed: no j-clique implies no k-clique for k ≥ j.
    Contrapositive of hasClique_mono. -/
theorem not_hasClique_mono {n : ℕ} (G : SGraph n) {j k : ℕ} (hjk : j ≤ k)
    (hj : ¬HasClique G j) : ¬HasClique G k :=
  fun hk => hj (hasClique_mono G hjk hk)

/-- K₅-free graphs are also K₇-free. The Erdős–Rogers counterexample
    uses K₇-free graphs, so it does not directly obstruct Problem 533. -/
theorem k5_free_implies_k7_free {n : ℕ} (G : SGraph n) (h : ¬HasClique G 5) :
    ¬HasClique G 7 :=
  not_hasClique_mono G (by omega) h

/- ## Neighborhood Structure -/

/-- The open neighborhood of a vertex v: all vertices adjacent to v. -/
noncomputable def neighborhood {n : ℕ} (G : SGraph n) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun u => G.adj v u)

/-- The degree of a vertex. -/
noncomputable def degree {n : ℕ} (G : SGraph n) (v : Fin n) : ℕ :=
  (neighborhood G v).card

/-- Membership in the neighborhood. -/
@[simp]
theorem mem_neighborhood {n : ℕ} (G : SGraph n) (v u : Fin n) :
    u ∈ neighborhood G v ↔ G.adj v u := by
  simp [neighborhood]

/-- A vertex is not in its own neighborhood (no self-loops). -/
theorem not_mem_neighborhood_self {n : ℕ} (G : SGraph n) (v : Fin n) :
    v ∉ neighborhood G v := by
  simp [G.irrefl v]

/-- If S ⊆ N(v) is a clique in G, then S ∪ {v} is a clique in G.
    Key structural lemma: adding v to a clique in its neighborhood gives a larger clique. -/
theorem clique_in_neighborhood_extends {n : ℕ} (G : SGraph n) (v : Fin n)
    (S : Finset (Fin n)) (hS : S ⊆ neighborhood G v) (hv : v ∉ S)
    (hClique : IsClique G S) : IsClique G (insert v S) := by
  intro i hi j hj hij
  simp [Finset.mem_insert] at hi hj
  rcases hi with rfl | hi <;> rcases hj with rfl | hj
  · exact absurd rfl hij
  · exact mem_neighborhood G v j |>.mp (hS hj)
  · exact G.symm _ _ (mem_neighborhood G v i |>.mp (hS hi))
  · exact hClique i hi j hj hij

/-- **Neighborhood K₄-freeness**: In a K₅-free graph, the neighborhood of any
    vertex is K₄-free. This is because a K₄ in N(v) together with v forms a K₅.

    This is the key structural observation connecting K₅-freeness to K₄-freeness:
    locally (in neighborhoods), K₅-free graphs look K₄-free. -/
theorem neighborhood_k4_free {n : ℕ} (G : SGraph n) (hK5 : ¬HasClique G 5)
    (v : Fin n) : ∀ S : Finset (Fin n), S ⊆ neighborhood G v → S.card = 4 →
    ¬IsClique G S := by
  intro S hSN hcard hClique
  apply hK5
  have hv : v ∉ S := by
    intro hv
    exact not_mem_neighborhood_self G v (hSN hv)
  refine ⟨insert v S, ?_, clique_in_neighborhood_extends G v S hSN hv hClique⟩
  rw [Finset.card_insert_of_not_mem hv, hcard]

/-- The neighborhood of any vertex in a K₅-free graph has no K₄.
    Restated using HasClique for compatibility with the k4_free_triangle_free_subset axiom. -/
theorem neighborhood_hasClique_4_false {n : ℕ} (G : SGraph n) (hK5 : ¬HasClique G 5)
    (v : Fin n) : ¬∃ S : Finset (Fin n), S ⊆ neighborhood G v ∧ S.card = 4 ∧
    IsClique G S := by
  intro ⟨S, hSN, hcard, hClique⟩
  exact neighborhood_k4_free G hK5 v S hSN hcard hClique

/- ## Turán-Type Bounds -/

/-- **Turán's bound for K₅-free graphs**: a K₅-free graph on n vertices has at
    most (3/8)n² edges. This is tight, achieved by the complete 4-partite graph
    T(n,4) with parts as equal as possible.

    Why axiomatized: Turán's theorem requires an extremal graph theory argument
    (induction on n with vertex deletion, or the Zykov symmetrization method).
    The general statement for K_{r+1}-free graphs gives (1-1/r)n²/2 edges. -/
axiom turan_k5_free (n : ℕ) (G : SGraph n) (hK5 : ¬HasClique G 5) :
    (edgeCount G : ℝ) ≤ 3 / 8 * n ^ 2

/-- Turán's bound constrains the density parameter δ: in a K₅-free graph,
    the density δ satisfies δ ≤ 3/8. So Problem 533 only needs δ ∈ (0, 3/8]. -/
theorem density_bound_k5_free (n : ℕ) (G : SGraph n) (hK5 : ¬HasClique G 5)
    (δ : ℝ) (hEdges : δ * n ^ 2 ≤ (edgeCount G : ℝ)) :
    δ * n ^ 2 ≤ 3 / 8 * n ^ 2 := by
  linarith [turan_k5_free n G hK5]

/- ## Known Partial Results -/

/-- Erdős–Hajnal–Simonovits–Sós–Szemerédi: for δ > 1/16, any K₅-free graph
    on n vertices with ≥ δn² edges has a triangle-free subset of ≫ n vertices. -/
axiom ehsss_result (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ : 1 / 16 < δ)
    (G : SGraph n) (hK5 : ¬HasClique G 5)
    (hEdges : δ * n ^ 2 ≤ (edgeCount G : ℝ)) :
  ∃ (S : Finset (Fin n)), IsTriangleFree G S ∧
    (S.card : ℝ) ≥ δ / 2 * n

/-- For K₄-free graphs, the result holds for all δ > 0. -/
axiom k4_free_triangle_free_subset (n : ℕ) (hn : 1 ≤ n)
    (δ : ℝ) (hδ : 0 < δ)
    (G : SGraph n) (hK4 : ¬HasClique G 4)
    (hEdges : δ * n ^ 2 ≤ (edgeCount G : ℝ)) :
  ∃ (c : ℝ) (S : Finset (Fin n)), 0 < c ∧ IsTriangleFree G S ∧
    (S.card : ℝ) ≥ c * n

/- ## Partial Resolution -/

/-- For δ > 1/16, Problem 533 follows from the known ehsss_result.
    The constant c = δ/2 works. The open part is 0 < δ ≤ 1/16. -/
theorem erdos_533_for_large_delta (δ : ℝ) (hδ : 0 < δ) (hδ_large : 1 / 16 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (hn : 1 ≤ n)
      (G : SGraph n) (hK5 : ¬HasClique G 5)
      (hEdges : δ * n ^ 2 ≤ (edgeCount G : ℝ)),
    ∃ (S : Finset (Fin n)), IsTriangleFree G S ∧
      (S.card : ℝ) ≥ c * n :=
  ⟨δ / 2, by linarith, fun n hn G hK5 hEdges =>
    ehsss_result n hn δ hδ_large G hK5 hEdges⟩

/-- K₄-free graphs satisfy the conclusion of Problem 533 for all δ > 0.
    K₄-free is a strictly stronger condition than K₅-free, so this resolves
    the conjecture for a subset of graphs. Follows from the K₄-free axiom. -/
theorem erdos_533_for_k4_free (δ : ℝ) (hδ : 0 < δ)
    (n : ℕ) (hn : 1 ≤ n) (G : SGraph n)
    (hK4 : ¬HasClique G 4)
    (hEdges : δ * n ^ 2 ≤ (edgeCount G : ℝ)) :
    ∃ (S : Finset (Fin n)), IsTriangleFree G S ∧
      ∃ c : ℝ, 0 < c ∧ (S.card : ℝ) ≥ c * n := by
  obtain ⟨c, S, hc, hTF, hSize⟩ := k4_free_triangle_free_subset n hn δ hδ G hK4 hEdges
  exact ⟨S, hTF, c, hc, hSize⟩

/- ## Strategy: Neighborhood Approach

The key proof strategy for Problem 533:
1. In a K₅-free graph G, neighborhood N(v) is K₄-free (neighborhood_k4_free)
2. By the K₄-free result (k4_free_triangle_free_subset), dense K₄-free graphs
   contain linear-size triangle-free subsets
3. If G has ≥ δn² edges, average degree ≥ 2δn, so some vertex v has deg(v) ≥ 2δn
4. If N(v) is dense enough, applying step 2 gives a triangle-free set of size ≫ δn

The challenge is step 4: the edge density within N(v) may not be quadratic
in |N(v)|. This is the core difficulty of the open problem. -/

/-- The degree of any vertex is at most n - 1 (no self-loops). -/
theorem degree_le {n : ℕ} (G : SGraph n) (v : Fin n) : degree G v ≤ n - 1 := by
  unfold degree neighborhood
  have h : (Finset.univ.filter (fun u => G.adj v u)).card ≤
      (Finset.univ.erase v).card := by
    apply Finset.card_le_card
    intro u hu
    simp at hu ⊢
    exact ⟨fun h => absurd h (G.irrefl v ∘ (· ▸ hu)), hu⟩
  simp [Finset.card_erase_of_mem (Finset.mem_univ v), Fintype.card_fin] at h
  exact h

/- ## The Open Question -/

/-- Erdős Problem #533: For every δ > 0, any K₅-free graph on n vertices
    with at least δn² edges must contain a triangle-free induced subgraph
    on ≫_δ n vertices.

    This is the open conjecture; it should be a `Prop`, not an `axiom`,
    since asserting it via `axiom` would amount to assuming the conjecture
    is true (which is unknown). The full conjecture is
    `∀ δ > 0, erdos_533_conjecture δ _`. -/
def erdos_533_conjecture (δ : ℝ) (_hδ : 0 < δ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (hn : 1 ≤ n)
    (G : SGraph n) (hK5 : ¬HasClique G 5)
    (hEdges : δ * n ^ 2 ≤ (edgeCount G : ℝ)),
  ∃ (S : Finset (Fin n)), IsTriangleFree G S ∧
    (S.card : ℝ) ≥ c * n
