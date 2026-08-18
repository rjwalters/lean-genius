import Proofs.Erdos85BranchDeficitSymmetry

/-! # The parity consequence of the one-high same-miss principle

This module isolates the exact graph-theoretic bridge behind the proposed
one-high `same-miss` collapse.  If the predicate “misses the fixed far
branch” is constant across every internal edge of a five-vertex branch, its
miss set is a union of edges of the induced matching and therefore has even
cardinality.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A miss predicate which is invariant across internal branch edges cuts
out a finite one-regular induced graph, so the corresponding directed miss
count is even. -/
theorem even_highBranchMissCount_of_internalEdge_miss_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} {v : V}
    (hv : G.degree v = d + 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (s t u : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1)
    (hu : u ∈ ((Finset.univ.erase s).erase t))
    (houterDegree : ∀ {a : V}, a ∈ secondLayerBranch G v s →
      G.degree a = d)
    (hsame : ∀ {x y : V},
      x ∈ secondLayerBranch G v s →
      y ∈ secondLayerBranch G v s → G.Adj x y →
      ((G.neighborFinset x ∩ secondLayerBranch G v u).card = 0 ↔
       (G.neighborFinset y ∩ secondLayerBranch G v u).card = 0)) :
    Even (highBranchMissCount G v s u) := by
  classical
  let B := secondLayerBranch G v s
  let misses : V → Prop := fun x =>
    (G.neighborFinset x ∩ secondLayerBranch G v u).card = 0
  let M := B.filter misses
  let K := G.induce (↑M : Set V)
  have hinternalLe : ∀ x ∈ B,
      (G.neighborFinset x ∩ B).card ≤ 1 := by
    intro x hx
    have hxs : x ≠ s.1 := by
      intro heq
      subst x
      exact (Finset.mem_sdiff.mp hx).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr s.2)
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v x s hxs
  have hinternalOne : ∀ x ∈ M,
      (G.neighborFinset x ∩ B).card = 1 := by
    intro x hxM
    have hxParts := Finset.mem_filter.mp hxM
    have hconserve := card_farBranch_misses_eq_internalDegree
      G hfree hv hexternal s t hst x hxParts.1 (houterDegree hxParts.1)
    have huMem : u ∈ (((Finset.univ.erase s).erase t).filter fun w =>
        (G.neighborFinset x ∩ secondLayerBranch G v w).card = 0) := by
      exact Finset.mem_filter.mpr ⟨hu, hxParts.2⟩
    have hpos : 0 < ((((Finset.univ.erase s).erase t).filter fun w =>
        (G.neighborFinset x ∩ secondLayerBranch G v w).card = 0).card) :=
      Finset.card_pos.mpr ⟨u, huMem⟩
    have hle := hinternalLe x hxParts.1
    dsimp [B] at hle
    have hone :
        (G.neighborFinset x ∩ secondLayerBranch G v s).card = 1 := by
      omega
    simpa [B] using hone
  have hKdegree : ∀ x : {z : V // z ∈ M}, K.degree x = 1 := by
    intro x
    rw [← K.card_neighborFinset_eq_degree]
    have hcard : (K.neighborFinset x).card =
        (G.neighborFinset x.1 ∩ B).card := by
      apply Finset.card_bij (fun y _ => y.1)
      · intro y hy
        have hadj : G.Adj x.1 y.1 :=
          (K.mem_neighborFinset x y).mp hy
        exact Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset x.1 y.1).mpr hadj,
          (Finset.mem_filter.mp y.2).1⟩
      · intro y hy z hz heq
        exact Subtype.ext heq
      · intro y hy
        have hyParts := Finset.mem_inter.mp hy
        have hxParts := Finset.mem_filter.mp x.2
        have hadj : G.Adj x.1 y :=
          (G.mem_neighborFinset x.1 y).mp hyParts.1
        have hyMiss : misses y :=
          (hsame hxParts.1 hyParts.2 hadj).mp hxParts.2
        let yM : {z : V // z ∈ M} :=
          ⟨y, Finset.mem_filter.mpr ⟨hyParts.2, hyMiss⟩⟩
        refine ⟨yM, ?_, rfl⟩
        exact (K.mem_neighborFinset x yM).mpr hadj
    rw [hcard]
    exact hinternalOne x.1 x.2
  have hcardEven : Even (Fintype.card {z : V // z ∈ M}) := by
    have hhand := K.sum_degrees_eq_twice_card_edges
    have hsum : (∑ x : {z : V // z ∈ M}, K.degree x) =
        Fintype.card {z : V // z ∈ M} := by
      simp [hKdegree]
    refine ⟨K.edgeFinset.card, ?_⟩
    calc
      Fintype.card {z : V // z ∈ M} =
          ∑ x : {z : V // z ∈ M}, K.degree x := hsum.symm
      _ = K.edgeFinset.card + K.edgeFinset.card := by
        simpa [two_mul] using hhand
  have hmissCard : highBranchMissCount G v s u = M.card := by
    rfl
  rw [hmissCard, ← Fintype.card_coe]
  exact hcardEven

/-- Pointwise same-miss on all internal edges makes every far entry in a
source row even. -/
theorem even_highBranchMissCount_of_sameMiss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} {v : V}
    (hv : G.degree v = d + 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d)
    (hsame : ∀ (s : {z : V // z ∈ G.neighborSet v}) {x y : V},
      x ∈ secondLayerBranch G v s →
      y ∈ secondLayerBranch G v s → G.Adj x y →
      ∀ u ∈ ((Finset.univ.erase s).erase (mate s)),
      ((G.neighborFinset x ∩ secondLayerBranch G v u).card = 0 ↔
       (G.neighborFinset y ∩ secondLayerBranch G v u).card = 0)) :
    ∀ s u, u ∈ ((Finset.univ.erase s).erase (mate s)) →
      Even (highBranchMissCount G v s u) := by
  intro s u hu
  apply even_highBranchMissCount_of_internalEdge_miss_iff
    G hfree hv hexternal s (mate s) u (hmateAdj s) hu
  · intro a ha
    apply houterDegree
    rw [secondLayer]
    exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, ha⟩
  · intro x y hx hy hxy
    exact hsame s hx hy hxy u hu

/-- The elementary rectangle obstruction behind a possible proof of
same-miss: cross-neighbors selected on opposite sides of an internal edge
cannot themselves be adjacent. -/
theorem not_adj_cross_witnesses_of_internal_branch_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s u w : {z : V // z ∈ G.neighborSet v}}
    (hsu : s ≠ u) (hsw : s ≠ w)
    {x y a b : V}
    (hx : x ∈ secondLayerBranch G v s)
    (hy : y ∈ secondLayerBranch G v s)
    (ha : a ∈ secondLayerBranch G v u)
    (hb : b ∈ secondLayerBranch G v w)
    (hxy : G.Adj x y) (hya : G.Adj y a) (hxb : G.Adj x b) :
    ¬ G.Adj a b := by
  have hxa : x ≠ a := by
    intro heq
    have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp : s ∈ (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}))
      (by simp : u ∈ (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}))
      hsu
    exact (Finset.disjoint_left.mp hdisj) hx (heq ▸ ha)
  have hyb : y ≠ b := by
    intro heq
    have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp : s ∈ (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}))
      (by simp : w ∈ (Finset.univ : Finset {z : V // z ∈ G.neighborSet v}))
      hsw
    exact (Finset.disjoint_left.mp hdisj) hy (heq ▸ hb)
  intro hab
  exact hfree (containsC4_of_two_common hxa hyb
    hxy.symm hya hxb.symm hab.symm)

/-- If the two endpoints of an internal branch edge have different missed
far branches, the two opposite cross-neighbors exist and are forced
nonadjacent.  This packages the local configuration that the remaining
same-miss proof must rule out globally. -/
theorem exists_nonadjacent_cross_witnesses_of_different_misses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s u w : {z : V // z ∈ G.neighborSet v}}
    (hsu : s ≠ u) (hsw : s ≠ w)
    {x y : V}
    (hx : x ∈ secondLayerBranch G v s)
    (hy : y ∈ secondLayerBranch G v s)
    (hxy : G.Adj x y)
    (hySeesU : (G.neighborFinset y ∩
      secondLayerBranch G v u).card ≠ 0)
    (hxSeesW : (G.neighborFinset x ∩
      secondLayerBranch G v w).card ≠ 0) :
    ∃ a ∈ secondLayerBranch G v u,
      ∃ b ∈ secondLayerBranch G v w,
        G.Adj y a ∧ G.Adj x b ∧ ¬ G.Adj a b := by
  have hUne : (G.neighborFinset y ∩
      secondLayerBranch G v u).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun hempty => by
      apply hySeesU
      rw [hempty]
      rfl)
  have hWne : (G.neighborFinset x ∩
      secondLayerBranch G v w).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun hempty => by
      apply hxSeesW
      rw [hempty]
      rfl)
  obtain ⟨a, ha⟩ := hUne
  obtain ⟨b, hb⟩ := hWne
  have haParts := Finset.mem_inter.mp ha
  have hbParts := Finset.mem_inter.mp hb
  refine ⟨a, haParts.2, b, hbParts.2,
    (G.mem_neighborFinset y a).mp haParts.1,
    (G.mem_neighborFinset x b).mp hbParts.1, ?_⟩
  exact not_adj_cross_witnesses_of_internal_branch_edge
    G hfree hsu hsw hx hy haParts.2 hbParts.2 hxy
      ((G.mem_neighborFinset y a).mp haParts.1)
      ((G.mem_neighborFinset x b).mp hbParts.1)

end

end Erdos85
