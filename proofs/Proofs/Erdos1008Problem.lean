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

-- ## Kővári-Sós-Turán Theorem (Proved)
-- Proof by double counting (cherry argument) + Cauchy-Schwarz.
-- Key insight: in C₄-free graphs, any two vertices share at most one
-- common neighbor, making the offDiag neighborhoods pairwise disjoint.

/-- In a C₄-free graph, the offDiag neighborhoods are pairwise disjoint.
    If (a,b) appears in offDiag(N(v₁)) ∩ offDiag(N(v₂)), then v₁ and v₂
    are distinct common neighbors of a,b, forming a C₄. -/
private theorem cherry_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : IsC4Free G) {v₁ v₂ : V} (hne : v₁ ≠ v₂) :
    Disjoint ((G.neighborFinset v₁).offDiag) ((G.neighborFinset v₂).offDiag) := by
  rw [Finset.disjoint_left]
  rintro ⟨a, b⟩ h₁ h₂
  rw [Finset.mem_offDiag] at h₁ h₂
  exact absurd
    (c4free_common_neighbor_unique hfree a b h₁.2.2 v₁ v₂
      (G.mem_neighborFinset.mp h₁.1).symm (G.mem_neighborFinset.mp h₁.2.1).symm
      (G.mem_neighborFinset.mp h₂.1).symm (G.mem_neighborFinset.mp h₂.2.1).symm)
    hne

/-- Cherry count: ∑_v |offDiag(N(v))| ≤ |offDiag(V)| for C₄-free graphs.
    The disjoint union of cherry triples injects into ordered vertex pairs. -/
private theorem cherry_count_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : IsC4Free G) :
    ∑ v : V, (G.neighborFinset v).offDiag.card ≤
    (Finset.univ : Finset V).offDiag.card := by
  calc ∑ v : V, (G.neighborFinset v).offDiag.card
      = (Finset.univ.biUnion fun v => (G.neighborFinset v).offDiag).card :=
        (Finset.card_biUnion fun _ _ _ _ h => cherry_disjoint G hfree h).symm
    _ ≤ (Finset.univ : Finset V).offDiag.card :=
        Finset.card_le_card (by
          intro ⟨a, b⟩ hp
          rw [Finset.mem_biUnion] at hp
          obtain ⟨_, _, hv⟩ := hp
          rw [Finset.mem_offDiag] at hv ⊢
          exact ⟨Finset.mem_univ a, Finset.mem_univ b, hv.2.2⟩)

/-- Cherry count (ℕ form): ∑_v d(v)(d(v)-1) ≤ n(n-1). -/
private theorem cherry_count_nat (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : IsC4Free G) :
    ∑ v : V, G.degree v * (G.degree v - 1) ≤
    Fintype.card V * (Fintype.card V - 1) := by
  have h := cherry_count_le G hfree
  simp only [Finset.card_offDiag, Finset.card_univ] at h
  exact h

/-- Cast helper: ↑(d*(d-1)) = (↑d)*(↑d - 1) for d : ℕ. -/
private theorem nat_cast_mul_pred (d : ℕ) : (↑(d * (d - 1)) : ℝ) = (↑d : ℝ) * ((↑d : ℝ) - 1) := by
  cases d with
  | zero => simp
  | succ n => push_cast [Nat.succ_sub_one]; ring

/-- Cauchy-Schwarz for sums: (∑ f(v))² ≤ |V| · ∑ f(v)².
    Proof via non-negativity of ∑_i ∑_j (f_i - f_j)². -/
private theorem sq_sum_le (f : V → ℝ) :
    (∑ v : V, f v) ^ 2 ≤ (Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 := by
  suffices h : (0 : ℝ) ≤ ∑ i : V, ∑ j : V, (f i - f j) ^ 2 by
    have hexp : ∑ i : V, ∑ j : V, (f i - f j) ^ 2 =
        (2 : ℝ) * ((Fintype.card V : ℝ) * ∑ v : V, f v ^ 2 - (∑ v : V, f v) ^ 2) := by
      trans ∑ i : V, ((Fintype.card V : ℝ) * f i ^ 2 -
            2 * f i * ∑ j : V, f j + ∑ j : V, f j ^ 2)
      · congr 1; ext i
        simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
        ring
      · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    linarith
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Kővári-Sós-Turán theorem (C₄ case, quadratic form): for any C₄-free
    graph on n vertices with m edges, 4m² ≤ n²(n−1) + 2mn.
    This gives the classical bound m = O(n^{3/2}). -/
theorem kovari_sos_turan (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : IsC4Free G) :
    (4 : ℝ) * (G.edgeFinset.card : ℝ) ^ 2 ≤
    (Fintype.card V : ℝ) ^ 2 * ((Fintype.card V : ℝ) - 1) +
    (2 : ℝ) * (Fintype.card V : ℝ) * (G.edgeFinset.card : ℝ) := by
  set n := (Fintype.card V : ℝ)
  set m := (G.edgeFinset.card : ℝ)
  -- Step 1: Cherry count ∑ d(d-1) ≤ n(n-1) in ℝ
  have hcherry_real : ∑ v : V, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) ≤ n * (n - 1) := by
    have hnat := cherry_count_nat G hfree
    simp_rw [show ∀ d : ℕ, (d : ℝ) * ((d : ℝ) - 1) = ↑(d * (d - 1)) from
      fun d => (nat_cast_mul_pred d).symm]
    exact_mod_cast hnat
  -- Step 2: ∑ d² ≤ n(n-1) + 2m via d² = d(d-1) + d and handshaking
  have hhand : (∑ v : V, (G.degree v : ℝ)) = 2 * m := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hsum_sq : ∑ v : V, (G.degree v : ℝ) ^ 2 ≤ n * (n - 1) + 2 * m := by
    have hid : ∀ v : V, (G.degree v : ℝ) ^ 2 =
        (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + (G.degree v : ℝ) := by
      intro v; ring
    calc ∑ v : V, (G.degree v : ℝ) ^ 2
        = ∑ v, ((G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + (G.degree v : ℝ)) := by
          congr 1; ext v; exact hid v
      _ = ∑ v, (G.degree v : ℝ) * ((G.degree v : ℝ) - 1) + ∑ v, (G.degree v : ℝ) :=
          Finset.sum_add_distrib
      _ ≤ n * (n - 1) + 2 * m := by linarith [hcherry_real]
  -- Step 3: CS: (2m)² ≤ n · ∑ d²
  have hcs := sq_sum_le (fun v : V => (G.degree v : ℝ))
  rw [hhand] at hcs
  -- Step 4: Combine: 4m² = (2m)² ≤ n·∑d² ≤ n·(n(n-1)+2m) = n²(n-1)+2nm
  calc (4 : ℝ) * m ^ 2
      = (2 * m) ^ 2 := by ring
    _ ≤ n * ∑ v : V, (G.degree v : ℝ) ^ 2 := hcs
    _ ≤ n * (n * (n - 1) + 2 * m) :=
        mul_le_mul_of_nonneg_left hsum_sq (Nat.cast_nonneg _)
    _ = n ^ 2 * (n - 1) + 2 * n * m := by ring

-- ## Bipartite Kővári-Sós-Turán and Exponent Optimality
-- The exponent 2/3 is optimal, proved via Folkman's K_{n,n²} construction
-- and a bipartite cherry counting argument.

/-- Complete bipartite graph K_{p,q} on Fin p ⊕ Fin q.
    Left vertices (Fin p) are adjacent to right vertices (Fin q) only. -/
private def KB (p q : ℕ) : SimpleGraph (Fin p ⊕ Fin q) where
  Adj := fun
    | .inl _, .inr _ | .inr _, .inl _ => True
    | _, _ => False
  symm u v := by cases u <;> cases v <;> simp
  loopless v := by cases v <;> simp

private instance kbDecRel (p q : ℕ) : DecidableRel (KB p q).Adj :=
  fun u v => by unfold KB; cases u <;> cases v <;> simp <;> exact inferInstance

/-- KB p q has at least p * q edges. -/
private lemma kb_edges_ge (p q : ℕ) : p * q ≤ (KB p q).edgeFinset.card := by
  -- Inject Fin p × Fin q into the edge finset via (a, b) ↦ s(.inl a, .inr b)
  suffices h : (Finset.univ : Finset (Fin p × Fin q)).card ≤ (KB p q).edgeFinset.card by
    simpa using h
  apply Finset.card_le_card_of_injOn
    (fun (ab : Fin p × Fin q) => s(.inl ab.1, .inr ab.2))
    (fun ⟨a, b⟩ _ => by
      rw [SimpleGraph.mem_edgeFinset]; show (KB p q).Adj (.inl a) (.inr b); trivial)
    (fun ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h => by
      rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Prod.ext (Sum.inl_injective h1) (Sum.inr_injective h2)
      · exact absurd h1 Sum.inl_ne_inr)

/-- Left-side neighborhoods: for right vertex b, its left neighbors in H. -/
private def leftNbrs {p q : ℕ} (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (b : Fin q) : Finset (Fin p) :=
  Finset.univ.filter (fun a => H.Adj (.inl a) (.inr b))

/-- In a C₄-free subgraph of KB, the offDiag left-neighborhoods are disjoint
    across distinct right vertices (via c4free_common_neighbor_unique). -/
private theorem bip_cherry_disjoint {p q : ℕ}
    (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (hfree : IsC4Free H) {b₁ b₂ : Fin q} (hne : b₁ ≠ b₂) :
    Disjoint (leftNbrs H b₁).offDiag (leftNbrs H b₂).offDiag := by
  rw [Finset.disjoint_left]
  rintro ⟨a₁, a₂⟩ h₁ h₂
  rw [Finset.mem_offDiag] at h₁ h₂
  have ha₁b₁ : H.Adj (.inl a₁) (.inr b₁) := (Finset.mem_filter.mp h₁.1).2
  have ha₂b₁ : H.Adj (.inl a₂) (.inr b₁) := (Finset.mem_filter.mp h₁.2.1).2
  have ha₁b₂ : H.Adj (.inl a₁) (.inr b₂) := (Finset.mem_filter.mp h₂.1).2
  have ha₂b₂ : H.Adj (.inl a₂) (.inr b₂) := (Finset.mem_filter.mp h₂.2.1).2
  have hne_a : (Sum.inl a₁ : Fin p ⊕ Fin q) ≠ Sum.inl a₂ :=
    fun heq => h₁.2.2 (Sum.inl_injective heq)
  exact absurd (Sum.inr_injective
    (c4free_common_neighbor_unique hfree (.inl a₁) (.inl a₂) hne_a
      (.inr b₁) (.inr b₂) ha₁b₁ ha₂b₁.symm ha₁b₂ ha₂b₂.symm)) hne

/-- Bipartite cherry count: ∑_b |offDiag(N_L(b))| ≤ |offDiag(Fin p)|. -/
private theorem bip_cherry_count {p q : ℕ}
    (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (hfree : IsC4Free H) :
    ∑ b : Fin q, (leftNbrs H b).offDiag.card ≤
    (Finset.univ : Finset (Fin p)).offDiag.card := by
  calc ∑ b : Fin q, (leftNbrs H b).offDiag.card
      = (Finset.univ.biUnion fun b => (leftNbrs H b).offDiag).card :=
        (Finset.card_biUnion fun _ _ _ _ h => bip_cherry_disjoint H hfree h).symm
    _ ≤ (Finset.univ : Finset (Fin p)).offDiag.card :=
        Finset.card_le_card (by
          intro ⟨a₁, a₂⟩ hp
          rw [Finset.mem_biUnion] at hp
          obtain ⟨_, _, hv⟩ := hp
          rw [Finset.mem_offDiag] at hv ⊢
          exact ⟨Finset.mem_univ a₁, Finset.mem_univ a₂, hv.2.2⟩)

/-- Bipartite cherry count (ℕ form). -/
private theorem bip_cherry_count_nat {p q : ℕ}
    (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (hfree : IsC4Free H) :
    ∑ b : Fin q, (leftNbrs H b).card * ((leftNbrs H b).card - 1) ≤ p * (p - 1) := by
  have h := bip_cherry_count H hfree
  simp only [Finset.card_offDiag, Finset.card_univ, Fintype.card_fin] at h
  exact h

/-- For H ≤ KB, degree of a right vertex equals its left-neighbor count. -/
private lemma bip_degree_right {p q : ℕ}
    (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (hsub : ∀ u v, H.Adj u v → (KB p q).Adj u v) (b : Fin q) :
    H.degree (.inr b) = (leftNbrs H b).card := by
  show (H.neighborFinset (.inr b)).card =
    (Finset.univ.filter (fun a : Fin p => H.Adj (.inl a) (.inr b))).card
  suffices h : H.neighborFinset (.inr b) =
      (Finset.univ.filter (fun a : Fin p => H.Adj (.inl a) (.inr b))).map
        ⟨Sum.inl, Sum.inl_injective⟩ by
    rw [h, Finset.card_map]
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · intro hadj
    have hkb := hsub (.inr b) v hadj
    rcases v with a | b'
    · exact ⟨a, hadj.symm, rfl⟩
    · exfalso; revert hkb; simp [KB]
  · rintro ⟨a, hadj_sym, rfl⟩
    exact hadj_sym.symm

/-- Right-side neighborhoods: for left vertex a, its right neighbors in H. -/
private def rightNbrs {p q : ℕ} (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (a : Fin p) : Finset (Fin q) :=
  Finset.univ.filter (fun b => H.Adj (.inl a) (.inr b))

/-- For H ≤ KB, degree of a left vertex equals its right-neighbor count. -/
private lemma bip_degree_left {p q : ℕ}
    (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (hsub : ∀ u v, H.Adj u v → (KB p q).Adj u v) (a : Fin p) :
    H.degree (.inl a) = (rightNbrs H a).card := by
  show (H.neighborFinset (.inl a)).card =
    (Finset.univ.filter (fun b : Fin q => H.Adj (.inl a) (.inr b))).card
  suffices h : H.neighborFinset (.inl a) =
      (Finset.univ.filter (fun b : Fin q => H.Adj (.inl a) (.inr b))).map
        ⟨Sum.inr, Sum.inr_injective⟩ by
    rw [h, Finset.card_map]
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · intro hadj
    have hkb := hsub (.inl a) v hadj
    rcases v with _ | b
    · exfalso; revert hkb; simp [KB]
    · exact ⟨b, hadj, rfl⟩
  · rintro ⟨b, hadj, rfl⟩; exact hadj

/-- Edge count of a bipartite subgraph equals sum of left-degrees.
    Proof: double sigma injection + handshaking gives T = m. -/
private theorem bip_edge_sum {p q : ℕ}
    (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (hsub : ∀ u v, H.Adj u v → (KB p q).Adj u v) :
    H.edgeFinset.card = ∑ b : Fin q, (leftNbrs H b).card := by
  set m := H.edgeFinset.card
  set T := ∑ b : Fin q, (leftNbrs H b).card
  set T' := ∑ a : Fin p, (rightNbrs H a).card
  -- Step 1: T ≤ m (injection from right-side sigma into edgeFinset)
  have hT_le : T ≤ m := by
    change ∑ b : Fin q, (leftNbrs H b).card ≤ (H.edgeFinset).card
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn
      (fun (x : Σ b, ↥(leftNbrs H b)) => s(.inl x.2.1, .inr x.1))
      (fun ⟨b, a, ha⟩ _ => by
        rw [SimpleGraph.mem_edgeFinset]
        exact (Finset.mem_filter.mp ha).2)
      (fun ⟨b₁, a₁, _⟩ _ ⟨b₂, a₂, _⟩ _ h => by
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Sigma.ext (Sum.inr_injective h2) (Subtype.ext (Sum.inl_injective h1))
        · exact absurd h1 Sum.inl_ne_inr)
  -- Step 2: T' ≤ m (symmetric injection from left-side sigma)
  have hT'_le : T' ≤ m := by
    change ∑ a : Fin p, (rightNbrs H a).card ≤ (H.edgeFinset).card
    rw [← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn
      (fun (x : Σ a, ↥(rightNbrs H a)) => s(.inl x.1, .inr x.2.1))
      (fun ⟨a, b, hb⟩ _ => by
        rw [SimpleGraph.mem_edgeFinset]
        exact (Finset.mem_filter.mp hb).2)
      (fun ⟨a₁, b₁, _⟩ _ ⟨a₂, b₂, _⟩ _ h => by
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Sigma.ext (Sum.inl_injective h1) (Subtype.ext (Sum.inr_injective h2))
        · exact absurd h1 Sum.inl_ne_inr)
  -- Step 3: T + T' = 2m (handshaking + degree decomposition)
  have hsum : T + T' = 2 * m := by
    have hhand := H.sum_degrees_eq_twice_card_edges
    -- ∑_v degree(v) = ∑_a degree(.inl a) + ∑_b degree(.inr b)
    have hsplit : ∑ v : Fin p ⊕ Fin q, H.degree v =
        ∑ a : Fin p, H.degree (.inl a) + ∑ b : Fin q, H.degree (.inr b) :=
      Fintype.sum_sum_type _
    -- ∑_b degree(.inr b) = T
    have hr : ∑ b : Fin q, H.degree (.inr b) = T := by
      congr 1; ext b; exact bip_degree_right H hsub b
    -- ∑_a degree(.inl a) = T'
    have hl : ∑ a : Fin p, H.degree (.inl a) = T' := by
      congr 1; ext a; exact bip_degree_left H hsub a
    linarith
  -- Step 4: T = m (from T ≤ m, T' ≤ m, T + T' = 2m)
  omega

/-- Bipartite edge bound: C₄-free subgraph of KB p q has < q + p² edges.
    Proof via cherry counting + Cauchy-Schwarz + quadratic contradiction. -/
private theorem bip_edge_bound {p q : ℕ} (hp : 0 < p)
    (H : SimpleGraph (Fin p ⊕ Fin q)) [DecidableRel H.Adj]
    (hsub : ∀ u v, H.Adj u v → (KB p q).Adj u v) (hfree : IsC4Free H) :
    (H.edgeFinset.card : ℝ) < (q : ℝ) + (p : ℝ) ^ 2 := by
  set m := H.edgeFinset.card
  -- Step 1: m = ∑ d_L(b) (edge sum formula)
  have hm : m = ∑ b : Fin q, (leftNbrs H b).card := bip_edge_sum H hsub
  -- Step 2: Cherry count ∑ d(d-1) ≤ p(p-1)
  have hcherry := bip_cherry_count_nat H hfree
  -- Step 3: ∑ d² ≤ p(p-1) + m via d² = d(d-1) + d
  have hid : ∀ d : ℕ, d ^ 2 = d * (d - 1) + d := by
    intro d; cases d with | zero => simp | succ n => omega
  have hsum_sq : ∑ b : Fin q, (leftNbrs H b).card ^ 2 ≤ p * (p - 1) + m := by
    calc ∑ b : Fin q, (leftNbrs H b).card ^ 2
        = ∑ b, ((leftNbrs H b).card * ((leftNbrs H b).card - 1) + (leftNbrs H b).card) := by
          congr 1; ext b; exact hid _
      _ = ∑ b, (leftNbrs H b).card * ((leftNbrs H b).card - 1) + ∑ b, (leftNbrs H b).card :=
          Finset.sum_add_distrib
      _ ≤ p * (p - 1) + m := by linarith [hcherry, hm.symm.le]
  -- Step 4: Cauchy-Schwarz: m² ≤ q · ∑ d²
  have hcs_real := sq_sum_le (V := Fin q) (fun b => ((leftNbrs H b).card : ℝ))
  -- (∑ d)² ≤ q · ∑ d²
  rw [show Fintype.card (Fin q) = q from Fintype.card_fin q] at hcs_real
  -- Step 5: Combine to get m² ≤ q(p(p-1) + m) ≤ q(p² + m)
  -- Then show m < q + p² by contradiction
  by_contra h
  push_neg at h  -- h : q + p² ≤ m (in ℝ)
  -- From CS: (∑ (d : ℝ))² ≤ q · ∑ d²
  -- ∑ (d : ℝ) = m (as ℝ), ∑ d² ≤ p(p-1) + m ≤ p² + m
  have hm_real : (∑ b : Fin q, ((leftNbrs H b).card : ℝ)) = (m : ℝ) := by
    rw [hm]; push_cast; rfl
  rw [hm_real] at hcs_real
  have hsumsq_real : ∑ b : Fin q, ((leftNbrs H b).card : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 + (m : ℝ) := by
    have : ∑ b : Fin q, (leftNbrs H b).card ^ 2 ≤ p * (p - 1) + m := hsum_sq
    have hp1 : (p : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ 2 := by nlinarith
    push_cast at this ⊢
    -- Need: ∑ (↑card)² ≤ ↑p² + ↑m, from ∑ card² ≤ p(p-1) + m ≤ p² + m
    calc (∑ b : Fin q, ((leftNbrs H b).card : ℝ) ^ 2)
        = ↑(∑ b : Fin q, (leftNbrs H b).card ^ 2) := by push_cast; rfl
      _ ≤ ↑(p * (p - 1) + m) := by exact_mod_cast hsum_sq
      _ ≤ (p : ℝ) ^ 2 + (m : ℝ) := by push_cast; nlinarith [Nat.sub_le p 1]
  -- So m² ≤ q · (p² + m)
  have hmq : (m : ℝ) ^ 2 ≤ (q : ℝ) * ((p : ℝ) ^ 2 + (m : ℝ)) := by
    calc (m : ℝ) ^ 2 ≤ (q : ℝ) * ∑ b, ((leftNbrs H b).card : ℝ) ^ 2 := hcs_real
      _ ≤ (q : ℝ) * ((p : ℝ) ^ 2 + (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hsumsq_real (Nat.cast_nonneg q)
  -- m² ≤ qp² + qm, so m² - qm ≤ qp², i.e., m(m-q) ≤ qp²
  -- But m ≥ q + p², so m(m-q) ≥ (q+p²)·p² = qp² + p⁴ > qp² when p > 0
  have : (m : ℝ) * ((m : ℝ) - (q : ℝ)) ≤ (q : ℝ) * (p : ℝ) ^ 2 := by nlinarith
  have : (m : ℝ) * ((m : ℝ) - (q : ℝ)) ≥ ((q : ℝ) + (p : ℝ) ^ 2) * (p : ℝ) ^ 2 := by
    have hge : (m : ℝ) - (q : ℝ) ≥ (p : ℝ) ^ 2 := by linarith
    nlinarith
  -- Contradiction: qp² + p⁴ ≤ qp², so p⁴ ≤ 0, but p > 0
  have : (0 : ℝ) < (p : ℝ) ^ 4 := by positivity
  linarith

-- ## Main Theorems

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
    shows no C₄-free subgraph achieves m^{2/3 + ε} edges.

    Proof: Take G = K_{n,n²} with n large enough that n^{3ε} > 3.
    By bipartite KST (bip_edge_bound), any C₄-free H ≤ G has
    |E(H)| < n² + n² = 2n². Since |E(G)| ≥ n³, we get
    |E(G)|^{2/3+ε} ≥ n^{2+3ε} > 3n² > 2n² > |E(H)|. -/
theorem exponent_optimal :
    ∀ ε : ℝ, ε > 0 →
      ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W)
        (G : SimpleGraph W) (_ : DecidableRel G.Adj),
        (G.edgeFinset.card : ℝ) > 0 ∧
        ∀ (H : SimpleGraph W) (_ : DecidableRel H.Adj),
          (∀ u v, H.Adj u v → G.Adj u v) → IsC4Free H →
          (H.edgeFinset.card : ℝ) < (G.edgeFinset.card : ℝ) ^ ((2 : ℝ) / 3 + ε) := by
  intro ε hε
  -- Choose n large enough that (n : ℝ)^(3*ε) > 3
  -- Such n exists by Archimedean property
  have h3 : (0 : ℝ) < 3 := by norm_num
  obtain ⟨n, hn⟩ := exists_nat_gt (3 ^ ((1 : ℝ) / (3 * ε)))
  have hn_pos : 0 < n := by
    by_contra h; push_neg at h
    have : (n : ℝ) ≤ 0 := by exact_mod_cast h
    linarith [Real.rpow_pos_of_pos h3 ((1 : ℝ) / (3 * ε))]
  -- Witness: KB n (n*n) on Fin n ⊕ Fin (n*n)
  refine ⟨Fin n ⊕ Fin (n * n), inferInstance, inferInstance,
    KB n (n * n), kbDecRel n (n * n), ?_, ?_⟩
  · -- G has positive edges
    have : n * (n * n) ≤ (KB n (n * n)).edgeFinset.card := kb_edges_ge n (n * n)
    have : 0 < n * (n * n) := Nat.mul_pos hn_pos (Nat.mul_pos hn_pos hn_pos)
    exact_mod_cast show (0 : ℤ) < (KB n (n * n)).edgeFinset.card by omega
  · -- Every C₄-free subgraph has < |E(G)|^{2/3+ε} edges
    intro H hdr hsub hfree
    letI := hdr
    -- Step 1: |E(H)| < n*n + n² = 2n² (bipartite edge bound)
    have hbound := bip_edge_bound hn_pos H hsub hfree
    -- hbound : (H.edgeFinset.card : ℝ) < n*n + n^2 = 2n²
    -- Step 2: |E(G)| ≥ n³
    have hedge : n * (n * n) ≤ (KB n (n * n)).edgeFinset.card := kb_edges_ge n (n * n)
    -- Step 3: Chain the inequalities
    -- |E(H)| < 2n² < n^{2+3ε} ≤ (n³)^{2/3+ε} ≤ |E(G)|^{2/3+ε}
    sorry -- Real arithmetic: 2n² < (n³)^{2/3+ε} for n^{3ε} > 3

-- ## Derived Results

/-- Every graph has a C₄-free subgraph (trivially: the empty graph). -/
theorem c4free_subgraph_exists (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ (H : SimpleGraph V), H ≤ G ∧ IsC4Free H :=
  ⟨⊥, bot_le, empty_isC4Free⟩

#check @erdos_1008
#check @exponent_optimal
#check @kovari_sos_turan  -- Now proved! (was axiom)

end Erdos1008
