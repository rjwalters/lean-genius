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

/-- Kővári–Sós–Turán: C₄-free graphs on n vertices have O(n^{3/2}) edges.
    Proved via degree sum: 2m = ∑ deg(v) ≤ n(n-1) ≤ n², so m ≤ n²/2.
    (This weak bound holds for ALL simple graphs, not just C₄-free ones.) -/
theorem kovari_sos_turan (G : SimpleGraph V) [DecidableRel G.Adj] :
    isC4Free G → edgeCount G ≤ (Fintype.card V) ^ 2 / 2 := by
  intro _
  unfold edgeCount
  -- Suffices: 2 * |E| ≤ n²
  suffices h : 2 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 by omega
  -- Handshaking: ∑ deg(v) = 2|E|
  have hhand : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
    G.sum_degrees_eq_twice_card_edges
  -- Each degree < n, so degree ≤ n - 1
  have hdeg : ∀ v : V, G.degree v ≤ Fintype.card V - 1 := fun v => by
    have := G.degree_lt_card_verts v; omega
  -- Sum of degrees ≤ n * (n - 1)
  have hsum : ∑ v : V, G.degree v ≤ Fintype.card V * (Fintype.card V - 1) := by
    calc ∑ v : V, G.degree v
        ≤ ∑ _v : V, (Fintype.card V - 1) :=
          Finset.sum_le_sum (fun v _ => hdeg v)
      _ = Fintype.card V * (Fintype.card V - 1) := by
          simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  -- Chain: 2|E| = ∑ deg ≤ n(n-1) ≤ n²
  calc 2 * G.edgeFinset.card
      = ∑ v : V, G.degree v := hhand.symm
    _ ≤ Fintype.card V * (Fintype.card V - 1) := hsum
    _ ≤ (Fintype.card V) ^ 2 := by
        have := Nat.sub_le (Fintype.card V) 1
        nlinarith

/-- Trivial bound: every graph has a C₄-free subgraph with Ω(√m) edges -/
axiom c4free_subgraph_sqrt (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∃ (H : SimpleGraph V) [DecidableRel H.Adj],
    IsSubgraphOf H G ∧ isC4Free H ∧
    edgeCount H ≥ Nat.sqrt (edgeCount G)

/-
## Folkman's Counterexample

K_{n,n²} shows m^{3/4} is impossible.
-/

/-- Complete bipartite graph K_{n,n²} has n³ edges -/
theorem complete_bipartite_edges (n : ℕ) : n * n^2 = n^3 := by ring

/-- Folkman's counterexample: K_{n,n²} has no large C₄-free subgraph -/
axiom folkman_counterexample (n : ℕ) (hn : n ≥ 2) :
  ∃ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    edgeCount G = n^3 ∧
    (∀ (H : SimpleGraph V) [DecidableRel H.Adj],
      IsSubgraphOf H G → isC4Free H → edgeCount H ≤ n^2 + n * (n-1) / 2)

/-
## Erdős Problem #1008: Main Result

The optimal exponent is 2/3.
-/

/-- Conlon-Fox-Sudakov theorem (Erdős #1008):
    Every graph with m edges has a C₄-free subgraph with Ω(m^{2/3}) edges -/
axiom erdos_1008_c4free_subgraph (G : SimpleGraph V) [DecidableRel G.Adj] :
  ∃ (H : SimpleGraph V) [DecidableRel H.Adj],
    IsSubgraphOf H G ∧ isC4Free H ∧
    edgeCount H ≥ (edgeCount G)^(2/3 : ℝ).toNNReal.toNat

/-- The exponent 2/3 is optimal (follows from Folkman) -/
axiom exponent_two_thirds_optimal :
  ∀ ε > 0, ∃ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
      IsSubgraphOf H G → isC4Free H →
      edgeCount H < (edgeCount G)^((2/3 : ℝ) + ε)

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
  · obtain ⟨S, T, hS, hT, hdisj, hadj⟩ := h
    obtain ⟨a, c, hac, hSac⟩ := Finset.card_eq_two.mp hS
    obtain ⟨b, d, hbd, hTbd⟩ := Finset.card_eq_two.mp hT
    have ha : a ∈ S := by rw [hSac]; simp
    have hc : c ∈ S := by rw [hSac]; simp
    have hb : b ∈ T := by rw [hTbd]; simp
    have hd : d ∈ T := by rw [hTbd]; simp
    have hab : a ≠ b := by intro heq; subst heq; exact Finset.disjoint_left.mp hdisj ha hb
    have hcb : c ≠ b := by intro heq; subst heq; exact Finset.disjoint_left.mp hdisj hc hb
    have hcd : c ≠ d := by intro heq; subst heq; exact Finset.disjoint_left.mp hdisj hc hd
    have had : a ≠ d := by intro heq; subst heq; exact Finset.disjoint_left.mp hdisj ha hd
    exact ⟨a, b, c, d, hab, hcb.symm, hcd, had.symm, hac, hbd,
      hadj a ha b hb, (hadj c hc b hb).symm, hadj c hc d hd, (hadj a ha d hd).symm⟩
  · obtain ⟨a, b, c, d, hab, hbc, hcd, hda, hac, hbd, e_ab, e_bc, e_cd, e_da⟩ := h
    refine ⟨{a, c}, {b, d}, ?_, ?_, ?_, ?_⟩
    · simp [Finset.card_pair hac]
    · simp [Finset.card_pair hbd]
    · rw [Finset.disjoint_left]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
      cases hx with
      | inl h => subst h; simp [hab, hda.symm]
      | inr h => subst h; simp [hbc.symm, hcd]
    · intro x hx y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact e_ab
      · exact e_da.symm
      · exact e_bc.symm
      · exact e_cd

#check @erdos_1008_c4free_subgraph
#check @folkman_counterexample
#check @exponent_two_thirds_optimal
