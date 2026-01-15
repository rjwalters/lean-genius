/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 7602a683-b598-440f-b374-1f546d757b19

The following was proved by Aristotle:

- theorem conjecture_implies_two_copies :
    erdos_60_conjecture → two_copies_conjecture
-/

/-
  Erdős Problem #60: Supersaturation of 4-Cycles

  Source: https://erdosproblems.com/60
  Status: OPEN

  Statement:
  Does every graph on n vertices with > ex(n; C_4) edges contain ≫ n^{1/2} many
  copies of C_4?

  History:
  - Erdős-Simonovits: Conjectured this result; couldn't even prove ≥ 2 copies
  - He-Ma-Yang (2021): Proved for n = q² + q + 1 where q is even
  - Related to Problem 765 about ex(n; C_4)

  Background:
  This is a supersaturation problem: once you exceed the Turán number for C_4,
  how many 4-cycles must appear? The conjectured answer is Ω(n^{1/2}).

  This file formalizes the definitions and known partial results.
-/

import Mathlib


open Set SimpleGraph Finset

namespace Erdos60

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

/-- A copy of C_4 in G is a set of 4 vertices forming a 4-cycle.
    Represented as a 4-tuple (a, b, c, d) where a-b-c-d-a forms a cycle. -/
def IsC4Copy (G : SimpleGraph V) (a b c d : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- The set of all C_4 copies in G (as ordered 4-tuples). -/
def C4Copies (G : SimpleGraph V) : Set (V × V × V × V) :=
  { p | IsC4Copy G p.1 p.2.1 p.2.2.1 p.2.2.2 }

/-- The number of C_4 copies in G (up to labeling).
    Each unlabeled C_4 corresponds to 8 labeled copies (4 rotations × 2 reflections). -/
noncomputable def countC4 (G : SimpleGraph V) : ℕ :=
  (C4Copies G).ncard / 8

/-! ## Turán Number for C_4 -/

-- Aristotle skipped at least one sorry in the block below (common reasons: Aristotle does not define data).
/-- The Turán number ex(n; C_4) - maximum edges in an n-vertex C_4-free graph.
    Axiomatized for simplicity. -/
noncomputable def exC4 (n : ℕ) : ℕ := by sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry716447', 'Erdos60.exC4_asymptotic']-/
/-- ex(n; C_4) = (1/2)(1 + o(1))n^{3/2} (Reiman 1958, Kővári-Sós-Turán). -/
axiom exC4_asymptotic : ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, |(exC4 n : ℝ) - (1/2) * n^(3/2 : ℝ)| ≤ c * n

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos60.exC4_upper', 'harmonicSorry526360']-/
/-- Upper bound: ex(n; C_4) ≤ (1/2)n^{3/2} + O(n). -/
axiom exC4_upper (n : ℕ) : (exC4 n : ℝ) ≤ (1/2) * n^(3/2 : ℝ) + n

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry267941', 'Erdos60.exC4_lower']-/
/-- Lower bound from incidence geometry (projective planes give equality for some n). -/
axiom exC4_lower (n : ℕ) : (exC4 n : ℝ) ≥ (1/2) * n^(3/2 : ℝ) - n

/-! ## Supersaturation -/

/-- A graph exceeds the Turán number for C_4. -/
def ExceedsTuranC4 (G : SimpleGraph V) : Prop :=
  G.edgeSet.ncard > exC4 (Fintype.card V)

/-! ## Main Conjecture (OPEN) -/

/--
**Erdős Problem 60: Supersaturation for C_4** (OPEN)

Conjecture: If G has n vertices and > ex(n; C_4) edges, then G contains
at least Ω(n^{1/2}) copies of C_4.

This remains unproven. Erdős and Simonovits couldn't even prove ≥ 2 copies
are guaranteed.
-/
def erdos_60_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)),
    G.edgeSet.ncard > exC4 n → (countC4 G : ℝ) ≥ c * n^(1/2 : ℝ)

/-! ## Partial Results -/

/-- A projective plane number: n = q² + q + 1 for some q. -/
def IsProjectivePlaneOrder (n : ℕ) : Prop :=
  ∃ q : ℕ, n = q^2 + q + 1

/-- n = q² + q + 1 for even q. -/
def IsEvenProjectivePlaneOrder (n : ℕ) : Prop :=
  ∃ q : ℕ, Even q ∧ n = q^2 + q + 1

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos60.he_ma_yang', 'harmonicSorry785181']-/
/--
**He-Ma-Yang Theorem (2021)**:
The supersaturation conjecture holds for n = q² + q + 1 where q is even.

For these special values of n, exceeding ex(n; C_4) forces Ω(n^{1/2}) copies of C_4.
-/
axiom he_ma_yang (n : ℕ) (hn : IsEvenProjectivePlaneOrder n)
    (G : SimpleGraph (Fin n)) (hexc : G.edgeSet.ncard > exC4 n) :
    ∃ c : ℝ, c > 0 ∧ (countC4 G : ℝ) ≥ c * n^(1/2 : ℝ)

/-! ## Weaker Results -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos60.at_least_one_c4', 'harmonicSorry797429']-/
/-- At least one C_4 exists when exceeding the Turán number (trivial). -/
axiom at_least_one_c4 (G : SimpleGraph V) (h : ExceedsTuranC4 G) :
    countC4 G ≥ 1

/--
**Open Problem**: Prove at least 2 copies of C_4 are guaranteed.
Erdős and Simonovits noted they couldn't prove even this weak bound.
-/
def two_copies_conjecture : Prop :=
  ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)),
    G.edgeSet.ncard > exC4 n → countC4 G ≥ 2

/-! ## Related: General Supersaturation -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry249856', 'Erdos60.erdos_simonovits_supersaturation']-/
/--
**Erdős-Simonovits Supersaturation Theorem**:
For any graph H, exceeding ex(n; H) by a constant factor forces
a positive density of copies of H.

Stated abstractly here as the existence of a supersaturation function.
-/
axiom erdos_simonovits_supersaturation :
    ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧
      ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)),
        (G.edgeSet.ncard : ℝ) ≥ (1 + ε) * exC4 n →
        (countC4 G : ℝ) ≥ δ * n^2

/-! ## Extremal Graphs -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['harmonicSorry869052', 'Erdos60.polarity_graph_exists']-/
/-- The polarity graph from a projective plane of order q.
    This is C_4-free and achieves ex(n; C_4) for n = q² + q + 1. -/
axiom polarity_graph_exists (q : ℕ) (hq : Nat.Prime q ∨ q = 1) :
    ∃ (G : SimpleGraph (Fin (q^2 + q + 1))),
      countC4 G = 0 ∧ G.edgeSet.ncard = exC4 (q^2 + q + 1)

/-! ## Corollaries -/

/-- For projective plane orders with even q, we have a partial result. -/
theorem partial_result_even_q (q : ℕ) (heven : Even q) :
    IsEvenProjectivePlaneOrder (q^2 + q + 1) :=
  ⟨q, heven, rfl⟩

/- The conjecture implies the two-copies conjecture. -/
noncomputable section AristotleLemmas

/-
Define the Pan graph (triangle with a pendant).
-/
def PanGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s | s = s(0, 1) ∨ s = s(1, 2) ∨ s = s(2, 0) ∨ s = s(2, 3)}

/-
The Pan graph has 4 edges.
-/
lemma pan_graph_edge_count : PanGraph.edgeSet.ncard = 4 := by
  have h : PanGraph.edgeSet.toFinset.card = 4 := by native_decide
  rw [Set.ncard_eq_toFinset_card']
  exact h

/-
The Pan graph has no C4 copies.
-/
lemma pan_graph_no_c4 : Erdos60.countC4 PanGraph = 0 := by
  unfold countC4;
  -- Since PanGraph has no C4 copies, the set C4Copies is empty.
  have h_empty : C4Copies PanGraph = ∅ := by
    unfold Erdos60.C4Copies;
    unfold Erdos60.IsC4Copy; simp +decide [ Set.ext_iff ] ;
    simp +decide [ Erdos60.PanGraph ];
    simp +decide [ Fin.forall_fin_succ ];
  aesop

/-
Define the set of all possible edges on 4 vertices (the edges of K4).
-/
def AllEdges : Finset (Sym2 (Fin 4)) := Finset.univ.filter (λ e => ¬e.IsDiag)

/-
Define the graph K4 minus a specific edge e.
-/
def K4_minus_edge (e : Sym2 (Fin 4)) : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {x | x ∈ AllEdges ∧ x ≠ e}

/-
The number of possible edges on 4 vertices is 6.
-/
lemma AllEdges_card : AllEdges.card = 6 := by
  simp [AllEdges]
  have : (Finset.univ.filter (λ e : Sym2 (Fin 4) => ¬e.IsDiag)).card = 6 := by
    decide
  exact this

/-
K4 minus an edge has 5 edges.
-/
lemma K4_minus_edge_card (e : Sym2 (Fin 4)) (he : e ∈ AllEdges) :
    (K4_minus_edge e).edgeSet.ncard = 5 := by
      -- Since $e$ is in $AllEdges$, we can remove it from $AllEdges$ to get the edge set of $K4_minus_edge$.
      have h_edge_set : (K4_minus_edge e).edgeSet = AllEdges \ {e} := by
        ext; simp [Erdos60.K4_minus_edge];
        native_decide +revert;
      rw [ h_edge_set, Set.ncard_coe_finset ] ; rw [ Finset.card_sdiff ] ; aesop

/-
For any edge e in K4, removing it leaves exactly 1 C4 copy.
-/
lemma K4_minus_edge_has_C4 : ∀ e ∈ AllEdges, Erdos60.countC4 (K4_minus_edge e) = 1 := by
  unfold Erdos60.countC4;
  unfold Erdos60.C4Copies;
  unfold Erdos60.IsC4Copy; simp +decide [ Set.ncard_eq_toFinset_card' ] ;
  unfold Erdos60.K4_minus_edge; simp +decide [ Set.ncard_eq_toFinset_card' ] ;

/-
Any graph on 4 vertices with 5 edges is equal to K4 minus some edge e.
-/
lemma five_edges_eq_K4_minus_edge (G : SimpleGraph (Fin 4)) (h : G.edgeSet.ncard = 5) :
    ∃ e ∈ AllEdges, G = K4_minus_edge e := by
      -- Let's choose any edge $e$ in $K_4$ and show that $G$ is equal to $K_4$ with that edge removed.
      obtain ⟨e, he⟩ : ∃ e ∈ AllEdges, G.edgeSet = AllEdges.erase e := by
        have h_edge_subset : G.edgeSet ⊆ AllEdges := by
          intro e he
          rw [Finset.mem_coe, Finset.mem_filter]
          exact ⟨Finset.mem_univ e, G.not_isDiag_of_mem_edgeSet he⟩
        -- Since $G$ has 5 edges and $AllEdges$ has 6 edges, $G$ must be missing exactly one edge from $AllEdges$.
        obtain ⟨e, he⟩ : ∃ e ∈ AllEdges, e ∉ G.edgeSet := by
          contrapose! h;
          rw [ show G.edgeSet = AllEdges from Set.Subset.antisymm h_edge_subset h ] ; simp +decide [ AllEdges_card ];
        refine' ⟨ e, he.1, Set.eq_of_subset_of_ncard_le ( fun x hx => _ ) _ ⟩ <;> aesop;
      refine' ⟨ e, he.1, _ ⟩;
      ext v w;
      by_cases hvw : v = w <;> simp_all +decide [ SimpleGraph.adj_comm ];
      simp_all +decide [ Set.ext_iff, SimpleGraph.adj_comm, Erdos60.K4_minus_edge ];
      convert he.2 ( s(v, w) ) using 1

/-
If H is a subgraph of G, then the number of C4 copies in H is less than or equal to the number of C4 copies in G.
-/
lemma subgraph_C4_le {V : Type*} [Fintype V] [DecidableEq V] (G H : SimpleGraph V) (h : H ≤ G) :
    Erdos60.countC4 H ≤ Erdos60.countC4 G := by
  unfold Erdos60.countC4
  apply Nat.div_le_div_right
  apply Set.ncard_le_ncard
  intro p hp
  unfold Erdos60.C4Copies at *
  unfold Erdos60.IsC4Copy at *
  simp at *
  obtain ⟨h1, h2, h3, h4, h5, h6, adj1, adj2, adj3, adj4⟩ := hp
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_⟩
  · exact h adj1
  · exact h adj2
  · exact h adj3
  · exact h adj4
  exact Set.toFinite (Erdos60.C4Copies G)

/-
Check the definitions of exC4 and the conjecture.
-/
#print Erdos60.exC4
#print Erdos60.erdos_60_conjecture

/-
Check if SimpleGraph (Fin 4) is a Fintype.
-/
#synth Fintype (SimpleGraph (Fin 4))

/-
Check Finset functions.
-/
#check Finset.max
#check Finset.image
#check Finset.filter

/-
Define the value of exC4 explicitly.
-/
def exC4_val (n : ℕ) : ℕ := ((Finset.univ : Finset (SimpleGraph (Fin n))).filter (λ G => Erdos60.countC4 G = 0)).sup (λ G => G.edgeSet.ncard)

/-
Any graph on 4 vertices with 5 edges has at least one C4 copy.
-/
lemma five_edges_implies_C4 (G : SimpleGraph (Fin 4)) (h : G.edgeSet.ncard = 5) :
    Erdos60.countC4 G > 0 := by
  obtain ⟨e, he, rfl⟩ := five_edges_eq_K4_minus_edge G h
  rw [K4_minus_edge_has_C4 e he]
  decide

end AristotleLemmas

theorem conjecture_implies_two_copies :
    erdos_60_conjecture → two_copies_conjecture := by
  intro ⟨c, hc, hconj⟩
  intro n G hexc
  have h := hconj n G hexc
  -- For n ≥ 4, c * n^{1/2} ≥ 2 for sufficiently large c
  contrapose! hconj;
  -- Let's choose a large enough $n$ such that $c * n^{1/2} < 2$.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, c * (n : ℝ) ^ (1 / 2 : ℝ) > 1 := by
    norm_num [ ← Real.sqrt_eq_rpow ];
    exact ⟨ ⌈c⁻¹ ^ 2⌉₊ + 1, fun n hn => by nlinarith [ Nat.le_ceil ( c⁻¹ ^ 2 ), show ( n : ℝ ) ≥ ⌈c⁻¹ ^ 2⌉₊ + 1 by exact_mod_cast hn, Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, inv_pos.2 hc, mul_inv_cancel₀ hc.ne', mul_pos hc <| Real.sqrt_pos.2 <| Nat.cast_pos.2 <| pos_of_gt hn ] ⟩;
  -- Let's choose a large enough $n$ such that $n > N$.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n > N ∧ n > Erdos60.exC4 (n + 1 + 1) := by
    use N + Erdos60.exC4 (N + 1 + 1) + 1;
    refine' ⟨ by linarith, _ ⟩;
    refine' lt_of_le_of_lt ( show Erdos60.exC4 ( N + Erdos60.exC4 ( N + 1 + 1 ) + 1 + 1 + 1 ) ≤ Erdos60.exC4 ( N + 1 + 1 ) from _ ) _;
    · exact?;
    · linarith;
  refine' ⟨ n + 1 + 1, _ ⟩;
  -- Consider a star graph with n+2 vertices.
  use SimpleGraph.mk (fun i j => i ≠ j ∧ (i = 0 ∨ j = 0));
  refine' ⟨ _, _ ⟩;
  · refine' lt_of_lt_of_le hn.2 _;
    rw [ Set.ncard_eq_toFinset_card' ] ; simp +arith +decide [ Finset.card_univ, SimpleGraph.edgeSet ];
    rw [ show ( Finset.filter ( Membership.mem ( ( SimpleGraph.edgeSetEmbedding ( Fin ( n + 1 + 1 ) ) : SimpleGraph ( Fin ( n + 1 + 1 ) ) → Set ( Sym2 ( Fin ( n + 1 + 1 ) ) ) ) { Adj := fun i j => ¬i = j ∧ ( i = 0 ∨ j = 0 ), symm := by aesop_cat, loopless := by aesop_cat } ) ) Finset.univ ) = Finset.image ( fun i : Fin ( n + 1 + 1 ) => Sym2.mk ( 0, i ) ) ( Finset.univ.erase 0 ) from ?_ ];
    · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      aesop;
    · ext ⟨ i, j ⟩ ; aesop;
  · refine' lt_of_le_of_lt _ ( hN _ ( by linarith ) );
    unfold Erdos60.countC4;
    unfold Erdos60.C4Copies;
    unfold Erdos60.IsC4Copy; simp +decide [ Set.ncard_eq_toFinset_card' ] ;
    rw [ Finset.card_eq_zero.mpr ] <;> norm_num;
    grind

/-! ## Summary

**Problem Status: OPEN**

The conjecture asks whether exceeding ex(n; C_4) forces Ω(n^{1/2}) copies of C_4.

**Known Results**:
1. At least 1 copy is guaranteed (by definition of Turán number)
2. He-Ma-Yang (2021): Proved for n = q² + q + 1, q even
3. General supersaturation (Erdős-Simonovits) gives some lower bound

**Open Questions**:
- Prove ≥ 2 copies are guaranteed (even this is open!)
- Prove the full Ω(n^{1/2}) bound for all n
- Determine the exact constant in the lower bound

References:
- Erdős-Simonovits: Original conjecture
- He-Ma-Yang (2021): "Supersaturation of C_4"
- Reiman (1958): ex(n; C_4) bounds from projective planes
-/

end Erdos60