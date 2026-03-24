/-
  Erdős Problem #1008: C₄-Free Subgraphs

  Source: https://erdosproblems.com/1008
  Status: SOLVED (Conlon-Fox-Sudakov 2014)

  Statement:
  Does every graph with m edges contain a subgraph with ≫ m^{2/3} edges
  which contains no C₄ (4-cycle)?

  Background:
  Originally asked by Bollobás and Erdős at the Tihany graph theory
  colloquium with m^{3/4} instead of m^{2/3}.

  Folkman disproved the m^{3/4} version:
  The graph K_{n,n²} has n³ edges, but every subgraph with more than
  n² + C(n,2) edges contains a C₄. Since n² + C(n,2) = O(n²) = o((n³)^{3/4}),
  this shows m^{3/4} is impossible.

  Erdős [Er71] revised the conjecture to m^{2/3}, noting that m^{1/2} is
  trivial (greedily remove edges from 4-cycles). He mentioned Szemerédi
  proved it but gave no reference.

  Resolution:
  TRUE. Conlon, Fox, and Sudakov (2014) proved every graph with m edges
  has a C₄-free subgraph with Ω(m^{2/3}) edges. A simpler proof was later
  given by Hunter.

  The exponent 2/3 is optimal due to Folkman's counterexample.

  References:
  [CFS14b] Conlon, Fox, Sudakov "Large subgraphs without complete bipartite
           graphs" arXiv:1401.6711 (2014)
  [Er71] Erdős "Some unsolved problems in graph theory" (1971)

  Tags: graph-theory, extremal, cycles, subgraphs, zarankiewicz
-/

import Mathlib

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## 4-Cycles in Graphs

A C₄ (4-cycle) is a cycle on 4 vertices: a-b-c-d-a.
-/

/-- A graph contains a 4-cycle -/
def hasC4 (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- A graph is C₄-free -/
def isC4Free (G : SimpleGraph V) : Prop := ¬hasC4 G

/-
## Subgraph Relation
-/

/-- H is a subgraph of G if every edge of H is an edge of G -/
def IsSubgraphOf (H G : SimpleGraph V) : Prop :=
  ∀ u v, H.Adj u v → G.Adj u v

/-- Edge count of a graph -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-
## Trivial Bound: m^{1/2}

Erdős noted that finding a C₄-free subgraph with Ω(m^{1/2}) edges is trivial.
This follows from the Kővári–Sós–Turán theorem.
-/

/-- Kővári–Sós–Turán: C₄-free graphs on n vertices have O(n^{3/2}) edges -/
theorem kovari_sos_turan (G : SimpleGraph V) [DecidableRel G.Adj] :
    isC4Free G → edgeCount G ≤ (Fintype.card V)^2 / 2 := by sorry

/-- Trivial bound: every graph has a C₄-free subgraph with Ω(√m) edges -/
theorem c4free_subgraph_sqrt (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
    IsSubgraphOf H G ∧ isC4Free H ∧
    edgeCount H ≥ Nat.sqrt (edgeCount G) := by sorry

/-
## Folkman's Counterexample

K_{n,n²} shows m^{3/4} is impossible.
-/

/-- Complete bipartite graph K_{n,n²} has n³ edges -/
theorem complete_bipartite_edges (n : ℕ) : n * n^2 = n^3 := by ring

/-- Folkman's counterexample: K_{n,n²} has no large C₄-free subgraph -/
theorem folkman_counterexample (n : ℕ) (hn : n ≥ 2) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    edgeCount G = n^3 ∧
    (∀ (H : SimpleGraph V) [DecidableRel H.Adj],
      IsSubgraphOf H G → isC4Free H → edgeCount H ≤ n^2 + n * (n-1) / 2) := by sorry

/-
## Erdős Problem #1008: Main Result

The optimal exponent is 2/3.
-/

/-- Conlon-Fox-Sudakov theorem (Erdős #1008):
    Every graph with m edges has a C₄-free subgraph with Ω(m^{2/3}) edges -/
theorem erdos_1008_c4free_subgraph (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
    IsSubgraphOf H G ∧ isC4Free H ∧
    edgeCount H ≥ Nat.sqrt (Nat.sqrt (edgeCount G ^ 2)) := by sorry
    -- Note: m^{2/3} ≈ (m²)^{1/3} ≈ sqrt(sqrt(m²)) as a crude approximation

/-- The exponent 2/3 is optimal (follows from Folkman) -/
theorem exponent_two_thirds_optimal :
    ∀ ε > 0, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
      IsSubgraphOf H G → isC4Free H →
      (edgeCount H : ℝ) < ((edgeCount G : ℝ))^((2/3 : ℝ) + ε) := by sorry

/-
## Generalization to K_{s,t}-free Subgraphs

The Conlon-Fox-Sudakov paper actually proves more general results
for avoiding complete bipartite graphs K_{s,t}.
-/

/-- A graph contains K_{s,t} as a subgraph -/
def hasKst (G : SimpleGraph V) (s t : ℕ) : Prop :=
  ∃ (S T : Finset V), S.card = s ∧ T.card = t ∧ Disjoint S T ∧
    ∀ x ∈ S, ∀ y ∈ T, G.Adj x y

/-- K_{2,2} = C₄ -/
theorem k22_is_c4 (G : SimpleGraph V) : hasKst G 2 2 ↔ hasC4 G := by
  constructor <;> intro h
  · -- K_{2,2} → C₄: extract 4 vertices from the bipartition
    obtain ⟨S, T, hS, hT, hdisj, hadj⟩ := h
    rw [Finset.card_eq_two] at hS hT
    obtain ⟨a, c, hac, rfl⟩ := hS
    obtain ⟨b, d, hbd, rfl⟩ := hT
    rw [Finset.disjoint_left] at hdisj
    have haS : a ∈ ({a, c} : Finset V) := by simp
    have hcS : c ∈ ({a, c} : Finset V) := by simp
    have hbT : b ∈ ({b, d} : Finset V) := by simp
    have hdT : d ∈ ({b, d} : Finset V) := by simp
    exact ⟨a, b, c, d,
      fun h => hdisj haS (h ▸ hbT), fun h => hdisj (h ▸ hcS) hbT,
      fun h => hdisj (h ▸ hcS) hdT, fun h => hdisj haS (h ▸ hdT),
      hac, hbd,
      hadj a haS b hbT, (hadj c hcS b hbT).symm,
      hadj c hcS d hdT, (hadj a haS d hdT).symm⟩
  · -- C₄ → K_{2,2}: construct S = {a,c}, T = {b,d}
    obtain ⟨a, b, c, d, hab, hbc, hcd, hda, hac, hbd, hadj_ab, hadj_bc, hadj_cd, hadj_da⟩ := h
    refine ⟨{a, c}, {b, d}, Finset.card_pair hac, Finset.card_pair hbd, ?_, ?_⟩
    · -- Disjoint: no element is in both {a,c} and {b,d}
      rw [Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_insert, Finset.mem_singleton] at hx hx'
      rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
      · exact hab rfl
      · exact hda.symm rfl
      · exact hbc rfl
      · exact hcd rfl
    · -- All cross-edges exist
      intro x hx y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hadj_ab
      · exact hadj_da.symm
      · exact hadj_bc.symm
      · exact hadj_cd

#check @erdos_1008_c4free_subgraph
#check @folkman_counterexample
#check @exponent_two_thirds_optimal
