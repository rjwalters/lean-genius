/-!
# Erdős Problem #579 — Independent Sets in K₂,₂,₂-Free Dense Graphs

Let δ > 0. If n is sufficiently large and G is a graph on n vertices with
no K₂,₂,₂ (complete tripartite graph with parts of size 2) and at least
δn² edges, then G contains an independent set of size ≫_δ n.

Known:
- Proved for δ > 1/8 by Erdős, Hajnal, Sós, and Szemerédi (1983)
- Open for general δ > 0

A problem of Erdős, Hajnal, Sós, and Szemerédi.

Reference: https://erdosproblems.com/579
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! ## K₂,₂,₂-Free Graphs -/

/-- The complete tripartite graph K₂,₂,₂: three independent pairs
    with all edges between different pairs.
    A graph contains K₂,₂,₂ if there exist 6 vertices
    a₁,a₂,b₁,b₂,c₁,c₂ (pairwise distinct) such that all
    cross-edges exist but no edges within {a₁,a₂}, {b₁,b₂}, {c₁,c₂}. -/
def SimpleGraph.ContainsK222 (G : SimpleGraph V) [DecidableEq V] : Prop :=
  ∃ (a₁ a₂ b₁ b₂ c₁ c₂ : V),
    a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ c₁ ≠ c₂ ∧
    -- All six vertices are distinct
    ({a₁, a₂, b₁, b₂, c₁, c₂} : Finset V).card = 6 ∧
    -- All cross-edges exist
    G.Adj a₁ b₁ ∧ G.Adj a₁ b₂ ∧ G.Adj a₁ c₁ ∧ G.Adj a₁ c₂ ∧
    G.Adj a₂ b₁ ∧ G.Adj a₂ b₂ ∧ G.Adj a₂ c₁ ∧ G.Adj a₂ c₂ ∧
    G.Adj b₁ c₁ ∧ G.Adj b₁ c₂ ∧ G.Adj b₂ c₁ ∧ G.Adj b₂ c₂

/-- A K₂,₂,₂-free graph -/
def SimpleGraph.IsK222Free (G : SimpleGraph V) [DecidableEq V] : Prop :=
  ¬G.ContainsK222

/-! ## Dense Graphs and Independent Sets -/

/-- A graph on Fin n has at least δn² edges -/
def isDense (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (δ : ℝ) : Prop :=
  δ * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)

/-- An independent set: a set of vertices with no edges between them -/
def SimpleGraph.IsIndepSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/-- The independence number: the size of the largest independent set -/
noncomputable def SimpleGraph.independenceNumber (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : ℕ :=
  Finset.sup (Finset.univ.powerset.filter G.IsIndepSet) Finset.card

/-! ## EHSS Result for δ > 1/8 -/

/-- Erdős–Hajnal–Sós–Szemerédi (1983): for δ > 1/8, K₂,₂,₂-free graphs
    with ≥ δn² edges have an independent set of linear size -/
axiom ehss_result :
  ∀ δ : ℝ, δ > 1 / 8 →
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ n in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          G.IsK222Free → isDense G δ →
            c * (n : ℝ) ≤ (G.independenceNumber : ℝ)

/-! ## The Erdős–Hajnal–Sós–Szemerédi Conjecture -/

/-- Erdős Problem 579: For every δ > 0 and n sufficiently large,
    every K₂,₂,₂-free graph on n vertices with at least δn² edges
    has an independent set of size ≫_δ n. Open for δ ≤ 1/8. -/
axiom ErdosProblem579 :
  ∀ δ : ℝ, δ > 0 →
    ∃ c : ℝ, c > 0 ∧
      ∀ᶠ n in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          G.IsK222Free → isDense G δ →
            c * (n : ℝ) ≤ (G.independenceNumber : ℝ)

/-! ## Connection to Turán Theory -/

/-- The octahedron is K₂,₂,₂. By the Kruskal–Katona theorem,
    the Turán number ex(n; K₂,₂,₂) = (1/8 + o(1))n².
    This explains the threshold δ = 1/8 in the EHSS result. -/
axiom turan_K222 :
  ∃ f : ℕ → ℝ, (∀ᶠ n in Filter.atTop, f n = 0) ∧
    ∀ᶠ n in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.IsK222Free →
          (G.edgeFinset.card : ℝ) ≤ (1 / 8 + f n) * (n : ℝ) ^ 2
