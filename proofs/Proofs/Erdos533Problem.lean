/-!
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

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

/-! ## Definitions -/

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

/-! ## Known Partial Results -/

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

/-- Erdős–Rogers counterexample: there exist K₇-free graphs with n/4 · n edges
    where every triangle-free subset has o(n) vertices. -/
axiom erdos_rogers_counterexample :
  ∀ C : ℝ, 0 < C → ∃ (n : ℕ) (G : SGraph n),
    1 ≤ n ∧ ¬HasClique G 7 ∧
    (1 : ℝ) / 4 * n ^ 2 ≤ (edgeCount G : ℝ) ∧
    ∀ (S : Finset (Fin n)), IsTriangleFree G S →
      (S.card : ℝ) < C * n

/-! ## The Open Question -/

/-- Erdős Problem #533: For every δ > 0, any K₅-free graph on n vertices
    with at least δn² edges must contain a triangle-free induced subgraph
    on ≫_δ n vertices. -/
axiom erdos_533_conjecture (δ : ℝ) (hδ : 0 < δ) :
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (hn : 1 ≤ n)
    (G : SGraph n) (hK5 : ¬HasClique G 5)
    (hEdges : δ * n ^ 2 ≤ (edgeCount G : ℝ)),
  ∃ (S : Finset (Fin n)), IsTriangleFree G S ∧
    (S.card : ℝ) ≥ c * n
