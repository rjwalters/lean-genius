-- Erdős Problem #1008 — C₄-Free Subgraphs
--
-- Statement:
-- Does every graph with m edges contain a subgraph with ≫ m^{2/3} edges
-- which contains no C₄ (4-cycle)?
--
-- Answer: YES (SOLVED).
-- Conlon, Fox, and Sudakov (2014) proved every graph with m edges
-- has a C₄-free subgraph with Ω(m^{2/3}) edges. The exponent 2/3
-- is optimal due to Folkman's counterexample K_{n,n²}.
--
-- Background:
-- Originally asked by Bollobás and Erdős at the Tihany colloquium (1966)
-- with m^{3/4}. Folkman quickly disproved 3/4 using K_{n,n²}.
-- Erdős [Er71] revised to m^{2/3}. Szemerédi reportedly proved it
-- (no published reference). Conlon-Fox-Sudakov gave a published proof (2014).
--
-- Status: AXIOMATIZED
-- Axioms: 3 (Kővári-Sós-Turán, main CFS result, exponent optimality)
-- Sorries: 0
--
-- References:
-- [CFS14] Conlon, Fox, Sudakov "Large subgraphs without complete bipartite
--         graphs" arXiv:1401.6711 (2014)
-- [Er71] Erdős "Some unsolved problems in graph theory and combinatorial
--        analysis" (1971)
-- [KST54] Kővári, Sós, Turán "On a problem of K. Zarankiewicz" (1954)
--
-- Tags: graph-theory, extremal, cycles, subgraphs, zarankiewicz, solved

import Mathlib

open SimpleGraph Finset

namespace Erdos1008

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ## 4-Cycles and C₄-Freeness

/-- A graph contains a 4-cycle C₄: four distinct vertices a-b-c-d-a with
    edges ab, bc, cd, da. This is equivalent to containing K_{2,2}. -/
def HasC4 (G : SimpleGraph V) : Prop :=
  ∃ a b c d : V, a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- A graph is C₄-free if it contains no 4-cycle. -/
def IsC4Free (G : SimpleGraph V) : Prop := ¬HasC4 G

/-- A graph contains K_{s,t}: disjoint sets S, T with |S|=s, |T|=t
    and all cross-edges present. -/
def HasKst (G : SimpleGraph V) (s t : ℕ) : Prop :=
  ∃ (S T : Finset V), S.card = s ∧ T.card = t ∧ Disjoint S T ∧
    ∀ x ∈ S, ∀ y ∈ T, G.Adj x y

-- ## K_{2,2} = C₄ Equivalence

omit [Fintype V] in
/-- K_{2,2} → C₄: disjoint pairs with all cross-edges form a 4-cycle. -/
theorem k22_implies_c4 (G : SimpleGraph V) (h : HasKst G 2 2) : HasC4 G := by
  obtain ⟨S, T, hS, hT, hdisj, hadj⟩ := h
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

omit [Fintype V] in
/-- C₄ → K_{2,2}: a 4-cycle a-b-c-d-a gives S={a,c}, T={b,d}. -/
theorem c4_implies_k22 (G : SimpleGraph V) (h : HasC4 G) : HasKst G 2 2 := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hda, hac, hbd, e_ab, e_bc, e_cd, e_da⟩ := h
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

omit [Fintype V] in
/-- C₄ = K_{2,2}: the fundamental equivalence connecting 4-cycles
    to the Zarankiewicz problem. -/
theorem k22_iff_c4 (G : SimpleGraph V) : HasKst G 2 2 ↔ HasC4 G :=
  ⟨k22_implies_c4 G, c4_implies_k22 G⟩

-- ## Structural Properties of C₄-Free Graphs

omit [Fintype V] [DecidableEq V] in
/-- The empty graph is C₄-free. -/
theorem empty_isC4Free : IsC4Free (⊥ : SimpleGraph V) := by
  intro ⟨a, b, _, _, _, _, _, _, _, _, hab, _, _, _⟩
  exact (SimpleGraph.bot_adj a b).mp hab

omit [Fintype V] [DecidableEq V] in
/-- C₄-freeness is hereditary: subgraphs of C₄-free graphs are C₄-free. -/
theorem c4free_of_subgraph {G H : SimpleGraph V}
    (hsub : ∀ u v, H.Adj u v → G.Adj u v) (hG : IsC4Free G) : IsC4Free H := by
  intro ⟨a, b, c, d, h1, h2, h3, h4, h5, h6, e1, e2, e3, e4⟩
  exact hG ⟨a, b, c, d, h1, h2, h3, h4, h5, h6,
    hsub a b e1, hsub b c e2, hsub c d e3, hsub d a e4⟩

omit [Fintype V] [DecidableEq V] in
/-- C₄-freeness is monotone w.r.t. the subgraph lattice. -/
theorem c4free_mono {G H : SimpleGraph V} (hle : H ≤ G) (hG : IsC4Free G) : IsC4Free H :=
  c4free_of_subgraph (fun _ _ huv => hle huv) hG

omit [Fintype V] [DecidableEq V] in
/-- In a C₄-free graph, any two distinct vertices share at most one
    common neighbor. This is the key structural constraint. -/
theorem c4free_common_neighbor_unique {G : SimpleGraph V}
    (hfree : IsC4Free G) (a b : V) (hab : a ≠ b) :
    ∀ x y : V, G.Adj a x → G.Adj b x → G.Adj a y → G.Adj b y → x = y := by
  intro x y hax hbx hay hby
  by_contra hxy
  exact hfree ⟨a, x, b, y, G.ne_of_adj hax, (G.ne_of_adj hbx).symm,
    G.ne_of_adj hby, (G.ne_of_adj hay).symm, hab, hxy,
    hax, hbx.symm, hby, hay.symm⟩

/-- A graph with at most 3 edges is C₄-free (a C₄ requires 4 edges). -/
theorem c4free_of_few_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.edgeFinset.card ≤ 3) : IsC4Free G := by
  intro ⟨a, b, c, d, hab, hbc, hcd, hda, hac, hbd, e_ab, e_bc, e_cd, e_da⟩
  have m1 : s(a, b) ∈ G.edgeFinset := G.mem_edgeFinset.mpr e_ab
  have m2 : s(b, c) ∈ G.edgeFinset := G.mem_edgeFinset.mpr e_bc
  have m3 : s(c, d) ∈ G.edgeFinset := G.mem_edgeFinset.mpr e_cd
  have m4 : s(d, a) ∈ G.edgeFinset := G.mem_edgeFinset.mpr e_da
  have ne12 : s(a, b) ≠ s(b, c) := by
    intro heq; rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> contradiction
  have ne13 : s(a, b) ≠ s(c, d) := by
    intro heq; rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨h1, _⟩
    · exact hac rfl
    · exact hda h1.symm
  have ne14 : s(a, b) ≠ s(d, a) := by
    intro heq; rcases Sym2.eq_iff.mp heq with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hda h1.symm
    · exact hbd h2
  have ne23 : s(b, c) ≠ s(c, d) := by
    intro heq; rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> contradiction
  have ne24 : s(b, c) ≠ s(d, a) := by
    intro heq; rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨h1, _⟩
    · exact hbd rfl
    · exact hab h1.symm
  have ne34 : s(c, d) ≠ s(d, a) := by
    intro heq; rcases Sym2.eq_iff.mp heq with ⟨rfl, _⟩ | ⟨h1, _⟩
    · exact hcd rfl
    · exact hac h1.symm
  have hsub : ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)) ⊆ G.edgeFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> assumption
  have nm3 : s(c, d) ∉ ({s(d, a)} : Finset (Sym2 V)) := Finset.notMem_singleton.mpr ne34
  have nm2 : s(b, c) ∉ insert s(c, d) ({s(d, a)} : Finset (Sym2 V)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ne23, ne24⟩
  have nm1 : s(a, b) ∉ insert s(b, c) (insert s(c, d) ({s(d, a)} : Finset (Sym2 V))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨ne12, ne13, ne14⟩
  have hcard : ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 V)).card = 4 := by
    simp only [Finset.card_insert_of_notMem nm1, Finset.card_insert_of_notMem nm2,
      Finset.card_insert_of_notMem nm3, Finset.card_singleton]
  linarith [Finset.card_le_card hsub]

-- ## Folkman's Counterexample: m^{3/4} is Impossible

/-- Edge count of K_{n,n²}: n · n² = n³. -/
theorem complete_bipartite_edge_count (n : ℕ) : n * n ^ 2 = n ^ 3 := by ring

/-- (n³)^{2/3} = n² for positive n: the Folkman ratio is 1,
    showing the exponent 2/3 is tight. -/
theorem folkman_ratio (n : ℕ) (_hn : n > 0) :
    ((n : ℝ) ^ 3) ^ ((2 : ℝ) / 3) = (n : ℝ) ^ 2 := by
  rw [← Real.rpow_natCast (n : ℝ) 3, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

-- ## Main Theorems (Axiomatized)

/-- Kővári-Sós-Turán theorem (C₄ case): every n-vertex C₄-free graph
    has O(n^{3/2}) edges. The precise bound is
    |E| ≤ (1/2)(1 + √(4n-3))√n, simplified here. -/
axiom kovari_sos_turan (G : SimpleGraph V) [DecidableRel G.Adj] :
  IsC4Free G → (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt 2 +
    (Fintype.card V : ℝ) / 2

/-- Erdős Problem #1008 (Conlon-Fox-Sudakov 2014):
    Every graph with m edges has a C₄-free subgraph with Ω(m^{2/3}) edges.
    Proved using dependent random choice. -/
axiom erdos_1008 :
  ∃ c : ℝ, c > 0 ∧
    ∀ (W : Type) [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
      ∃ (H : SimpleGraph W) (_ : DecidableRel H.Adj),
        (∀ u v, H.Adj u v → G.Adj u v) ∧
        IsC4Free H ∧
        (H.edgeFinset.card : ℝ) ≥ c * (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3)

/-- The exponent 2/3 is optimal: for every ε > 0, Folkman's K_{n,n²}
    shows no C₄-free subgraph achieves m^{2/3 + ε} edges. -/
axiom exponent_optimal :
  ∀ ε : ℝ, ε > 0 →
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
      (G.edgeFinset.card : ℝ) > 0 ∧
      ∀ (H : SimpleGraph W) (_ : DecidableRel H.Adj),
        (∀ u v, H.Adj u v → G.Adj u v) → IsC4Free H →
        (H.edgeFinset.card : ℝ) < (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3 + ε)

-- ## Derived Results

/-- Every graph has a C₄-free subgraph (trivially: the empty graph). -/
theorem c4free_subgraph_exists (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (H : SimpleGraph V), H ≤ G ∧ IsC4Free H :=
  ⟨⊥, bot_le, empty_isC4Free⟩

#check @erdos_1008
#check @exponent_optimal
#check @kovari_sos_turan

end Erdos1008
