/-
  Erdős Problem #584: Cycle-Connected Subgraphs

  Source: https://erdosproblems.com/584
  Status: OPEN (partial results known)

  Statement:
  Let G be a graph with n vertices and δn² edges. Are there subgraphs
  H₁, H₂ ⊆ G such that:

  1) H₁ has ≫ δ³n² edges and:
     - Every two edges are contained in a cycle of length ≤ 6
     - If two edges share a vertex, they are on a cycle of length 4

  2) H₂ has ≫ δ²n² edges and:
     - Every two edges are contained in a cycle of length ≤ 8

  Partial Results:
  - Duke-Erdős (1982): H₁ for n sufficiently large (fixed δ)
  - Duke-Erdős-Rödl (1984): H₁ with δ⁵ instead of δ³
  - Fox-Sudakov (2008): H₂ when δ > n^{-1/5}

  The main challenge is proving these when δ = n^{-c} for c > 0.

  References:
  - [DuEr82] Duke-Erdős
  - [DER84] Duke-Erdős-Rödl, "More results on subgraphs..."
  - [FoSu08b] Fox-Sudakov, "On a problem of Duke-Erdős-Rödl..."
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

open Nat Real

namespace Erdos584

/- ## Part I: Graph Definitions -/

/-- A simple graph on n vertices. -/
structure Graph (n : ℕ) where
  edges : Finset (Fin n × Fin n)
  symm : ∀ e ∈ edges, (e.2, e.1) ∈ edges
  no_loops : ∀ e ∈ edges, e.1 ≠ e.2

/-- Number of edges in a graph. -/
def Graph.edgeCount {n : ℕ} (G : Graph n) : ℕ := G.edges.card / 2

/-- Edge density: e(G) / n². -/
noncomputable def Graph.density {n : ℕ} (G : Graph n) : ℝ :=
  G.edgeCount / (n : ℝ)^2

/-- A graph has density δ if e(G) ≥ δn². -/
def HasDensity {n : ℕ} (G : Graph n) (δ : ℝ) : Prop :=
  (G.edgeCount : ℝ) ≥ δ * n^2

/- ## Part II: Subgraphs -/

/-- H is a subgraph of G. -/
def IsSubgraph {n : ℕ} (H G : Graph n) : Prop :=
  H.edges ⊆ G.edges

/- ## Part III: Cycle Connectivity -/

/-- A path in the graph. -/
structure Path {n : ℕ} (G : Graph n) where
  vertices : List (Fin n)
  consecutive : ∀ i, i + 1 < vertices.length →
    (vertices.get ⟨i, by omega⟩, vertices.get ⟨i + 1, by omega⟩) ∈ G.edges

/-- A cycle of length k. -/
def IsCycle {n : ℕ} {G : Graph n} (p : Path G) (k : ℕ) : Prop :=
  p.vertices.length = k ∧
  p.vertices.Nodup ∧
  (p.vertices.head!, p.vertices.getLast!) ∈ G.edges

/-- Two edges are on a common cycle of length ≤ k. -/
def OnCommonCycle {n : ℕ} (G : Graph n) (e1 e2 : Fin n × Fin n) (k : ℕ) : Prop :=
  ∃ p : Path G, IsCycle p k ∧
    e1.1 ∈ p.vertices ∧ e1.2 ∈ p.vertices ∧
    e2.1 ∈ p.vertices ∧ e2.2 ∈ p.vertices

/-- Every two edges are on a cycle of length ≤ k. -/
def IsCycleConnected {n : ℕ} (G : Graph n) (k : ℕ) : Prop :=
  ∀ e1 e2 : Fin n × Fin n, e1 ∈ G.edges → e2 ∈ G.edges →
    ∃ j ≤ k, OnCommonCycle G e1 e2 j

/-- Edges sharing a vertex are on a 4-cycle. -/
def AdjacentEdgesOn4Cycle {n : ℕ} (G : Graph n) : Prop :=
  ∀ e1 e2 : Fin n × Fin n, e1 ∈ G.edges → e2 ∈ G.edges →
    (e1.1 = e2.1 ∨ e1.1 = e2.2 ∨ e1.2 = e2.1 ∨ e1.2 = e2.2) →
    OnCommonCycle G e1 e2 4

/- ## Part IV: The Main Conjecture -/

/-- The H₁ property: 6-cycle connected with adjacent edges on 4-cycles. -/
def HasH1Property {n : ℕ} (H : Graph n) : Prop :=
  IsCycleConnected H 6 ∧ AdjacentEdgesOn4Cycle H

/-- The H₂ property: 8-cycle connected. -/
def HasH2Property {n : ℕ} (H : Graph n) : Prop :=
  IsCycleConnected H 8

/-- **Erdős Conjecture #584 (H₁):**
    Every dense graph has a large 6-cycle connected subgraph. -/
def ErdosConjecture584_H1 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (G : Graph n) (δ : ℝ),
    δ > 0 → HasDensity G δ →
    ∃ H : Graph n, IsSubgraph H G ∧ HasH1Property H ∧
      (H.edgeCount : ℝ) ≥ C * δ^3 * n^2

/-- **Erdős Conjecture #584 (H₂):**
    Every dense graph has a large 8-cycle connected subgraph. -/
def ErdosConjecture584_H2 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (G : Graph n) (δ : ℝ),
    δ > 0 → HasDensity G δ →
    ∃ H : Graph n, IsSubgraph H G ∧ HasH2Property H ∧
      (H.edgeCount : ℝ) ≥ C * δ^2 * n^2

/-- The full conjecture combines both H₁ and H₂. -/
def ErdosConjecture584 : Prop :=
  ErdosConjecture584_H1 ∧ ErdosConjecture584_H2

/- ## Part V: Known Results -/

/-- **Duke-Erdős Theorem (1982):**
    H₁ exists for fixed δ when n is sufficiently large.
    This was the first partial result, but only applies for fixed density. -/
axiom duke_erdos_1982 :
    ∀ δ : ℝ, δ > 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ G : Graph n,
      HasDensity G δ → ∃ H : Graph n,
        IsSubgraph H G ∧ HasH1Property H ∧
        (H.edgeCount : ℝ) ≥ δ^3 * n^2 / 1000

/-- **Duke-Erdős-Rödl Theorem (1984):**
    H₁ with δ⁵ exponent instead of the conjectured δ³.
    The best known uniform bound for H₁. -/
axiom duke_erdos_rodl_1984 :
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (G : Graph n) (δ : ℝ),
      δ > 0 → HasDensity G δ →
      ∃ H : Graph n, IsSubgraph H G ∧ HasH1Property H ∧
        (H.edgeCount : ℝ) ≥ C * δ^5 * n^2

/-- **Fox-Sudakov Theorem (2008):**
    H₂ when δ > n^{-1/5}. This leaves the sparse regime open. -/
axiom fox_sudakov_2008 (n : ℕ) (G : Graph n) (δ : ℝ)
    (hδ : δ > 0) (h_lower : δ > (n : ℝ)^(-(1/5 : ℝ)))
    (h_dense : HasDensity G δ) :
    ∃ H : Graph n, IsSubgraph H G ∧ HasH2Property H ∧
      (H.edgeCount : ℝ) ≥ δ^2 * n^2 / 1000

/- ## Part VI: The Main Challenge -/

/-- The sparse regime: δ = n^{-c} for some c > 0. -/
def IsSparseRegime (n : ℕ) (δ : ℝ) (c : ℝ) : Prop :=
  c > 0 ∧ δ = (n : ℝ)^(-c)

/-- **The Main Open Question:**
    Does the conjecture hold in the sparse regime?
    For δ = n^{-c} with 0 < c < 1/2, must there exist a 6-cycle
    connected subgraph with ≫ δ³n² edges? -/
def SparseRegimeConjecture : Prop :=
  ∀ c : ℝ, c > 0 → c < 1/2 →
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (G : Graph n),
      let δ := (n : ℝ)^(-c)
      HasDensity G δ →
      ∃ H : Graph n, IsSubgraph H G ∧ HasH1Property H ∧
        (H.edgeCount : ℝ) ≥ C * δ^3 * n^2

/- ## Part VII: Quantitative Bounds -/

/-- Best known exponent for H₁: δ⁵ from Duke-Erdős-Rödl (1984). -/
def bestKnownExponentH1 : ℝ := 5

/-- Target exponent for H₁: δ³ is the conjectured bound. -/
def targetExponentH1 : ℝ := 3

/-- The gap between known and conjectured exponents is significant. -/
example : targetExponentH1 < bestKnownExponentH1 := by norm_num

/-- Best known density threshold for H₂: δ > n^{-1/5} (Fox-Sudakov). -/
def bestKnownThresholdH2 : ℝ := 1/5

/- ## Part VIII: Summary -/

/-- **Summary of Erdős Problem #584:**
    Formalizes three partial results toward the cycle-connected subgraph conjecture:
    1. Duke-Erdős (1982): H₁ for fixed δ
    2. Duke-Erdős-Rödl (1984): H₁ with δ⁵ (best uniform bound)
    3. Fox-Sudakov (2008): H₂ for δ > n^{-1/5}

    The full conjecture (δ³ for H₁, δ² for H₂ in all regimes) remains OPEN. -/
theorem erdos_584_summary :
    (∀ δ : ℝ, δ > 0 → ∃ N : ℕ, ∀ n ≥ N, ∀ G : Graph n,
      HasDensity G δ → ∃ H : Graph n, IsSubgraph H G ∧ HasH1Property H ∧
        (H.edgeCount : ℝ) ≥ δ^3 * n^2 / 1000) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (G : Graph n) (δ : ℝ),
      δ > 0 → HasDensity G δ →
      ∃ H : Graph n, IsSubgraph H G ∧ HasH1Property H ∧
        (H.edgeCount : ℝ) ≥ C * δ^5 * n^2) :=
  ⟨duke_erdos_1982, duke_erdos_rodl_1984⟩

end Erdos584
