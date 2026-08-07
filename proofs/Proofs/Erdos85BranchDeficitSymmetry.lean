import Proofs.Erdos85CleanHighBranchObstruction

/-!
# Symmetry of branch deficits

Between two finite vertex sets, adjacency incidences can be counted from
either side.  When every vertex has at most one neighbor across, the number
of vertices missing the opposite set is therefore symmetric for equal-size
sets.  Applied to high-root branches, this makes the directed dirty-sector
miss matrix symmetric.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Bipartite adjacency incidences counted from either shore agree. -/
theorem sum_card_neighbor_inter_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) =
      ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  classical
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_bij (fun p _ => ⟨p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset] at hp ⊢
    exact ⟨hp.2.2, by simpa [G.adj_comm] using hp.2.1, hp.1⟩
  · intro p hp q hq hpq
    cases p
    cases q
    cases hpq
    rfl
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset] at hp
    refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hp.2.2, by simpa [G.adj_comm] using hp.2.1, hp.1⟩
    · cases p
      rfl

/-- For a zero-one-valued function, its sum plus the number of zero terms is
the size of the indexing finset. -/
theorem sum_add_card_filter_eq_card_of_le_one
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (hle : ∀ x ∈ S, f x ≤ 1) :
    (∑ x ∈ S, f x) + (S.filter fun x => f x = 0).card = S.card := by
  classical
  rw [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x ∈ S, (f x + if f x = 0 then 1 else 0)) =
        ∑ _x ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      have := hle x hx
      by_cases hzero : f x = 0 <;> simp [hzero] <;> omega
    _ = S.card := by simp

/-- Equal-size shores with cross-degree at most one have equal numbers of
vertices with no cross-neighbor. -/
theorem card_filter_no_cross_neighbor_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcard : A.card = B.card)
    (hleA : ∀ a ∈ A, (G.neighborFinset a ∩ B).card ≤ 1)
    (hleB : ∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ 1) :
    (A.filter fun a => (G.neighborFinset a ∩ B).card = 0).card =
      (B.filter fun b => (G.neighborFinset b ∩ A).card = 0).card := by
  have hA := sum_add_card_filter_eq_card_of_le_one A
    (fun a => (G.neighborFinset a ∩ B).card) hleA
  have hB := sum_add_card_filter_eq_card_of_le_one B
    (fun b => (G.neighborFinset b ∩ A).card) hleB
  have hinc := sum_card_neighbor_inter_comm G A B
  omega

/-- The directed miss count from one high-root branch to another. -/
def highBranchMissCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  ((secondLayerBranch G v s).filter fun a =>
    (G.neighborFinset a ∩ secondLayerBranch G v t).card = 0).card

/-- Vertices of a branch incident to an internal branch edge.  Since a
`C₄`-free branch has maximum degree one, these are precisely the matched
vertices of its induced matching. -/
def highBranchMatchedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  ((secondLayerBranch G v s).filter fun a =>
    (G.neighborFinset a ∩ secondLayerBranch G v s).card = 1).card

/-- The induced degree inside a branch is the cardinality used in
`highBranchMatchedCount`. -/
theorem degree_induce_secondLayerBranch_eq_card_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (s : {z : V // z ∈ G.neighborSet v})
    (a : secondLayerBranch G v s) :
    (G.induce (secondLayerBranch G v s)).degree a =
      (G.neighborFinset a.1 ∩ secondLayerBranch G v s).card := by
  classical
  rw [← (G.induce (secondLayerBranch G v s)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun b _ => b.1)
  · intro b hb
    have hab : G.Adj a.1 b.1 := by
      exact ((G.induce (secondLayerBranch G v s)).mem_neighborFinset a b).mp hb
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset a.1 b.1).mpr hab, b.2⟩
  · intro b hb c hc hbc
    exact Subtype.ext hbc
  · intro q hq
    let b : secondLayerBranch G v s :=
      ⟨q, (Finset.mem_inter.mp hq).2⟩
    refine ⟨b, ?_, rfl⟩
    apply ((G.induce (secondLayerBranch G v s)).mem_neighborFinset a b).mpr
    change G.Adj a.1 q
    exact (G.mem_neighborFinset a.1 q).mp (Finset.mem_inter.mp hq).1

/-- The internally matched vertices of every high-root branch occur in
pairs, so their count is even. -/
theorem even_highBranchMatchedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s : {z : V // z ∈ G.neighborSet v}) :
    Even (highBranchMatchedCount G v s) := by
  classical
  let B := secondLayerBranch G v s
  let H := G.induce B
  let P := (Finset.univ : Finset B).filter fun a => H.degree a ≠ 0
  have hle : ∀ a : B, H.degree a ≤ 1 := by
    intro a
    exact degree_induce_secondLayerBranch_le_one G hfree v s a
  have hsum : ∑ a : B, H.degree a = P.card := by
    calc
      (∑ a : B, H.degree a) =
          ∑ a : B, if H.degree a ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : H.degree a = 0
        · simp [ha]
        · simp [ha]
          have := hle a
          omega
      _ = P.card := by
        simpa [P] using
          (Finset.sum_boole (R := ℕ) (fun a : B => H.degree a ≠ 0)
            (Finset.univ : Finset B))
  have hPeven : Even P.card := by
    have hhand := H.sum_degrees_eq_twice_card_edges
    change (∑ a : B, H.degree a) = 2 * H.edgeFinset.card at hhand
    rw [hsum] at hhand
    exact ⟨H.edgeFinset.card, by omega⟩
  have hmatchedEq : highBranchMatchedCount G v s = P.card := by
    rw [highBranchMatchedCount]
    apply Finset.card_bij (fun a ha =>
      (⟨a, (Finset.mem_filter.mp ha).1⟩ : B))
    · intro a ha
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
      have hdeg : H.degree (⟨a, (Finset.mem_filter.mp ha).1⟩ : B) = 1 := by
        change (G.induce (secondLayerBranch G v s)).degree
          (⟨a, (Finset.mem_filter.mp ha).1⟩ :
            secondLayerBranch G v s) = 1
        rw [degree_induce_secondLayerBranch_eq_card_inter]
        exact (Finset.mem_filter.mp ha).2
      omega
    · intro a ha b hb hab
      exact congrArg Subtype.val hab
    · intro a ha
      have haNonzero : H.degree a ≠ 0 := by
        simpa [P] using ha
      have haOne :
          (G.neighborFinset a.1 ∩ secondLayerBranch G v s).card = 1 := by
        have hdegOne : H.degree a = 1 := by
          have := hle a
          omega
        change (G.neighborFinset a.1 ∩
          secondLayerBranch G v s).card = 1
        rw [← degree_induce_secondLayerBranch_eq_card_inter]
        exact hdegOne
      refine ⟨a.1, Finset.mem_filter.mpr ⟨a.2, haOne⟩, ?_⟩
      rfl
  rw [hmatchedEq]
  exact hPeven

/-- Equal-sized high-root branches have symmetric directed miss counts. -/
theorem highBranchMissCount_comm_of_equal_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s t : {z : V // z ∈ G.neighborSet v})
    (hcard : (secondLayerBranch G v s).card =
      (secondLayerBranch G v t).card) :
    highBranchMissCount G v s t = highBranchMissCount G v t s := by
  apply card_filter_no_cross_neighbor_eq G
    (secondLayerBranch G v s) (secondLayerBranch G v t) hcard
  · intro a ha
    have hat : a ≠ t.1 := by
      intro hat
      subst a
      exact (Finset.mem_sdiff.mp ha).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr t.2)
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v a t hat
  · intro b hb
    have hbs : b ≠ s.1 := by
      intro hbs
      subst b
      exact (Finset.mem_sdiff.mp hb).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr s.2)
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v b s hbs

/-- At a square-order high root all branch sizes are `d-2`, so the miss
matrix is symmetric without an extra cardinality hypothesis. -/
theorem squareOrder_highBranchMissCount_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    highBranchMissCount G v s t = highBranchMissCount G v t s := by
  apply highBranchMissCount_comm_of_equal_card G hfree s t
  rw [card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
      G hd hv hneigh hlocal s,
    card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
      G hd hv hneigh hlocal t]

/-- Arithmetic core of the dirty row-sum identity.  On `d+1` branches, if
all branch counts are zero or one, their total is `d-1`, and the paired
branch count is zero, then the number of missing far branches is exactly the
count in the vertex's own branch. -/
theorem card_far_misses_eq_self_of_branch_sum
    {P : Type*} [Fintype P] [DecidableEq P]
    {d : ℕ} (hPcard : Fintype.card P = d + 1)
    (s t : P) (hst : s ≠ t) (f : P → ℕ)
    (hle : ∀ u, f u ≤ 1) (hsum : ∑ u : P, f u = d - 1)
    (htzero : f t = 0) :
    ((((Finset.univ : Finset P).erase s).erase t).filter fun u =>
      f u = 0).card = f s := by
  let M : Finset P := ((Finset.univ.erase s).erase t)
  have hMcard : M.card = d - 1 := by
    dsimp [M]
    rw [Finset.card_erase_of_mem (by simp [hst.symm] :
      t ∈ (Finset.univ : Finset P).erase s)]
    rw [Finset.card_erase_of_mem (by simp : s ∈ (Finset.univ : Finset P))]
    rw [Finset.card_univ, hPcard]
    omega
  have hsMem : s ∈ (Finset.univ : Finset P) := by simp
  have htMem : t ∈ (Finset.univ : Finset P).erase s := by simp [hst.symm]
  have hsErase := Finset.sum_erase_add
    (Finset.univ : Finset P) f hsMem
  have htErase := Finset.sum_erase_add
    ((Finset.univ : Finset P).erase s) f htMem
  have hsumM : (∑ u ∈ M, f u) + f s = d - 1 := by
    have ht : (∑ u ∈ M, f u) =
        ∑ u ∈ (Finset.univ : Finset P).erase s, f u := by
      dsimp [M]
      rw [← htErase, htzero, add_zero]
    calc
      (∑ u ∈ M, f u) + f s =
          (∑ u ∈ (Finset.univ : Finset P).erase s, f u) + f s := by rw [ht]
      _ = ∑ u : P, f u := hsErase
      _ = d - 1 := hsum
  have haccount := sum_add_card_filter_eq_card_of_le_one M f (by
    intro u _
    exact hle u)
  dsimp [M] at haccount ⊢
  dsimp [M] at hMcard
  omega

/-- Double-count a Boolean relation between two finsets. -/
theorem sum_card_filter_relation_comm
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (T : Finset B) (R : A → B → Prop)
    [DecidableRel R] :
    (∑ a ∈ S, (T.filter fun b => R a b).card) =
      ∑ b ∈ T, (S.filter fun a => R a b).card := by
  classical
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_bij (fun p _ => ⟨p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp ⊢
    exact ⟨hp.2.1, hp.1, hp.2.2⟩
  · intro p hp q hq hpq
    cases p
    cases q
    cases hpq
    rfl
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp
    refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_filter]
      exact ⟨hp.2.1, hp.1, hp.2.2⟩
    · cases p
      rfl

/-- At a saturated high root, the parent edge accounts for one degree and
the second-layer branches account for every other neighbor of an outer
vertex. -/
theorem sum_card_neighbors_inter_highBranches_eq_degree_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} {v : V}
    (hexternal : externalRepairCandidates G v = ∅)
    (s : {z : V // z ∈ G.neighborSet v})
    (a : V) (ha : a ∈ secondLayerBranch G v s)
    (hadegree : G.degree a = d) :
    (∑ w : {z : V // z ∈ G.neighborSet v},
      (G.neighborFinset a ∩ secondLayerBranch G v w).card) = d - 1 := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  have haOutside : a ∉ insert v (G.neighborFinset v) :=
    (Finset.mem_sdiff.mp ha).2
  have hparentAdj : G.Adj a s.1 := by
    have := (Finset.mem_sdiff.mp ha).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hneighbors : G.neighborFinset a =
      insert s.1 (G.neighborFinset a ∩ secondLayer G v) := by
    ext q
    constructor
    · intro hq
      have haq : G.Adj a q := (G.mem_neighborFinset a q).mp hq
      have hcover : q ∈ (Finset.univ : Finset V) := by simp
      have hpartition :=
        closedNeighborhood_union_secondLayer_union_external_eq_univ G v
      rw [← hpartition, hexternal] at hcover
      simp only [Finset.map_empty, Finset.union_empty, Finset.mem_union,
        Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hcover
      rcases hcover with (rfl | hqNv) | hqSecond
      · exact (haOutside (by
          simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
          exact Or.inr haq.symm)).elim
      · let r : P := ⟨q, hqNv⟩
        have haBranchR : a ∈ secondLayerBranch G v r := by
          apply Finset.mem_sdiff.mpr
          exact ⟨(G.mem_neighborFinset q a).mpr haq.symm, haOutside⟩
        have hrs : r = s := by
          by_contra hrs
          have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
            (by simp : r ∈ (Finset.univ : Finset P))
            (by simp : s ∈ (Finset.univ : Finset P)) hrs
          exact (Finset.disjoint_left.mp hdisj) haBranchR ha
        exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hrs))
      · exact Finset.mem_insert.mpr (Or.inr
          (Finset.mem_inter.mpr ⟨hq, hqSecond⟩))
    · intro hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact (G.mem_neighborFinset a s.1).mpr hparentAdj
      · exact (Finset.mem_inter.mp hq).1
  have hsNotSecond : s.1 ∉ secondLayer G v := by
    intro hs
    rw [secondLayer] at hs
    rcases Finset.mem_biUnion.mp hs with ⟨w, _, hsw⟩
    exact (Finset.mem_sdiff.mp hsw).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr s.2)
  have hbranchDisj := secondLayerBranch_pairwiseDisjoint G hfree v
  have hinter : G.neighborFinset a ∩ secondLayer G v =
      Finset.univ.biUnion fun w : P =>
        G.neighborFinset a ∩ secondLayerBranch G v w := by
    ext q
    constructor
    · intro hq
      have hqa := (Finset.mem_inter.mp hq).1
      rw [secondLayer] at hq
      rcases Finset.mem_biUnion.mp (Finset.mem_inter.mp hq).2 with
        ⟨w, _, hqw⟩
      exact Finset.mem_biUnion.mpr ⟨w, by simp,
        Finset.mem_inter.mpr ⟨hqa, hqw⟩⟩
    · intro hq
      rcases Finset.mem_biUnion.mp hq with ⟨w, _, hqw⟩
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hqw).1,
        Finset.mem_biUnion.mpr ⟨w, by simp,
          (Finset.mem_inter.mp hqw).2⟩⟩
  have hinterDisj :
      (↑(Finset.univ : Finset P) : Set P).PairwiseDisjoint
        (fun w => G.neighborFinset a ∩ secondLayerBranch G v w) := by
    intro w _ z _ hwz
    change Disjoint
      (G.neighborFinset a ∩ secondLayerBranch G v w)
      (G.neighborFinset a ∩ secondLayerBranch G v z)
    rw [Finset.disjoint_left]
    intro q hqw hqz
    exact (Finset.disjoint_left.mp
      (hbranchDisj (by simp) (by simp) hwz))
        (Finset.mem_inter.mp hqw).2 (Finset.mem_inter.mp hqz).2
  have hcardNeighbors :
      (G.neighborFinset a).card =
        1 + (G.neighborFinset a ∩ secondLayer G v).card := by
    calc
      (G.neighborFinset a).card =
          (insert s.1 (G.neighborFinset a ∩ secondLayer G v)).card :=
        congrArg Finset.card hneighbors
      _ = 1 + (G.neighborFinset a ∩ secondLayer G v).card := by
        rw [Finset.card_insert_of_notMem]
        · omega
        · intro hs
          exact hsNotSecond (Finset.mem_inter.mp hs).2
  rw [G.card_neighborFinset_eq_degree, hadegree, hinter,
    Finset.card_biUnion hinterDisj] at hcardNeighbors
  rw [hcardNeighbors]
  rw [Nat.add_sub_cancel_left]

/-- **Pointwise dirty conservation.**  For an outer degree-`d` vertex in
branch `s`, the number of far branches it misses is exactly its degree inside
its own branch (zero or one). -/
theorem card_farBranch_misses_eq_internalDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} {v : V}
    (hv : G.degree v = d + 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1)
    (a : V) (ha : a ∈ secondLayerBranch G v s)
    (hadegree : G.degree a = d) :
    ((((Finset.univ.erase s).erase t).filter fun u =>
      (G.neighborFinset a ∩ secondLayerBranch G v u).card = 0).card) =
      (G.neighborFinset a ∩ secondLayerBranch G v s).card := by
  let P := {z : V // z ∈ G.neighborSet v}
  let f : P → ℕ := fun u =>
    (G.neighborFinset a ∩ secondLayerBranch G v u).card
  have hPcard : Fintype.card P = d + 1 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  have hstne : s ≠ t := fun h => G.loopless.irrefl s.1
    (congrArg Subtype.val h ▸ hst)
  have hle : ∀ u : P, f u ≤ 1 := by
    intro u
    have hau : a ≠ u.1 := by
      intro hau
      exact (Finset.mem_sdiff.mp ha).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr (hau ▸ u.2))
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v a u hau
  have hsum : ∑ u : P, f u = d - 1 := by
    exact sum_card_neighbors_inter_highBranches_eq_degree_sub_one
      G hfree hexternal s a ha hadegree
  have htzero : f t = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact not_adj_between_secondLayerBranches_of_adj_roots
      G hfree v s t hst ⟨a, ha⟩ ⟨q, (Finset.mem_inter.mp hq).2⟩
        ((G.mem_neighborFinset a q).mp (Finset.mem_inter.mp hq).1)
  exact card_far_misses_eq_self_of_branch_sum
    hPcard s t hstne f hle hsum htzero

/-- **Dirty row-sum identity.**  Summing directed misses from a branch over
all far branches gives exactly the number of internally matched vertices in
the source branch. -/
theorem sum_far_highBranchMissCount_eq_matchedCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} {v : V}
    (hv : G.degree v = d + 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1)
    (houterDegree : ∀ {a : V}, a ∈ secondLayerBranch G v s →
      G.degree a = d) :
    (∑ u ∈ ((Finset.univ.erase s).erase t),
      highBranchMissCount G v s u) = highBranchMatchedCount G v s := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  let M : Finset P := (Finset.univ.erase s).erase t
  let B := secondLayerBranch G v s
  let R : V → P → Prop := fun a u =>
    (G.neighborFinset a ∩ secondLayerBranch G v u).card = 0
  have hdouble := sum_card_filter_relation_comm B M R
  have hpoint : ∀ a ∈ B, (M.filter fun u => R a u).card =
      (G.neighborFinset a ∩ B).card := by
    intro a ha
    simpa [P, M, B, R] using
      card_farBranch_misses_eq_internalDegree
        G hfree hv hexternal s t hst a ha (houterDegree ha)
  have hinternalLe : ∀ a ∈ B,
      (G.neighborFinset a ∩ B).card ≤ 1 := by
    intro a ha
    have has : a ≠ s.1 := by
      intro has
      subst a
      exact (Finset.mem_sdiff.mp ha).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr s.2)
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v a s has
  have hsumInternal : (∑ a ∈ B, (G.neighborFinset a ∩ B).card) =
      highBranchMatchedCount G v s := by
    calc
      (∑ a ∈ B, (G.neighborFinset a ∩ B).card) =
          ∑ a ∈ B,
            if (G.neighborFinset a ∩ B).card = 1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have hle := hinternalLe a ha
        by_cases hone : (G.neighborFinset a ∩ B).card = 1
        · simp [hone]
        · have hzero : (G.neighborFinset a ∩ B).card = 0 := by omega
          simp [hone, hzero]
      _ = (B.filter fun a =>
          (G.neighborFinset a ∩ B).card = 1).card := by
        rw [← Finset.sum_filter]
        simp
      _ = highBranchMatchedCount G v s := by
        rfl
  dsimp [M] at hdouble
  change (∑ u ∈ ((Finset.univ.erase s).erase t),
    (B.filter fun a => R a u).card) = highBranchMatchedCount G v s
  rw [← hdouble]
  calc
    (∑ a ∈ B, (((Finset.univ.erase s).erase t).filter fun u =>
        R a u).card) =
        ∑ a ∈ B, (G.neighborFinset a ∩ B).card := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hpoint a ha
    _ = highBranchMatchedCount G v s := hsumInternal

/-- **Paired-branch saver inequality.**  Every internally unmatched vertex
of one branch needs a distinct matched saver for its fan into the paired
branch.  Consequently the source branch size is at most the sum of the two
matched counts. -/
theorem card_branch_le_add_matchedCounts_of_paired
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1) :
    (secondLayerBranch G v s).card ≤
      highBranchMatchedCount G v s + highBranchMatchedCount G v t := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  let M : Finset P := (Finset.univ.erase s).erase t
  let Bs := secondLayerBranch G v s
  let Bt := secondLayerBranch G v t
  let unmatched : Finset V := Bs.filter fun a =>
    (G.neighborFinset a ∩ Bs).card = 0
  let saver : Finset V := M.biUnion fun u =>
    (secondLayerBranch G v u).filter fun q =>
      (G.neighborFinset q ∩ Bt).card = 0
  have hstne : s ≠ t := fun h => G.loopless.irrefl s.1
    (congrArg Subtype.val h ▸ hst)
  have hbranchDisj := secondLayerBranch_pairwiseDisjoint G hfree v
  have hsaverDisj : (↑M : Set P).PairwiseDisjoint (fun u =>
      (secondLayerBranch G v u).filter fun q =>
        (G.neighborFinset q ∩ Bt).card = 0) := by
    intro u hu w hw huw
    change Disjoint
      ((secondLayerBranch G v u).filter fun q =>
        (G.neighborFinset q ∩ Bt).card = 0)
      ((secondLayerBranch G v w).filter fun q =>
        (G.neighborFinset q ∩ Bt).card = 0)
    rw [Finset.disjoint_left]
    intro q hqu hqw
    exact (Finset.disjoint_left.mp
      (hbranchDisj (by simp) (by simp) huw))
        (Finset.mem_filter.mp hqu).1 (Finset.mem_filter.mp hqw).1
  have hsaverCard : saver.card = highBranchMatchedCount G v t := by
    rw [show saver = M.biUnion (fun u =>
        (secondLayerBranch G v u).filter fun q =>
          (G.neighborFinset q ∩ Bt).card = 0) by rfl,
      Finset.card_biUnion hsaverDisj]
    calc
      (∑ u ∈ M, ((secondLayerBranch G v u).filter fun q =>
          (G.neighborFinset q ∩ Bt).card = 0).card) =
          ∑ u ∈ M, highBranchMissCount G v u t := by rfl
      _ = ∑ u ∈ M, highBranchMissCount G v t u := by
        apply Finset.sum_congr rfl
        intro u _
        exact highBranchMissCount_comm_of_equal_card G hfree u t (by
          rw [card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
              G (by omega) hv hneigh hlocal u,
            card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
              G (by omega) hv hneigh hlocal t])
      _ = highBranchMatchedCount G v t := by
        have hrow := sum_far_highBranchMissCount_eq_matchedCount
          G hfree hv hexternal t s hst.symm (by
            intro a ha
            apply houterDegree
            rw [secondLayer]
            exact Finset.mem_biUnion.mpr ⟨t, by simp, ha⟩)
        have herase : ((Finset.univ : Finset P).erase s).erase t =
            ((Finset.univ : Finset P).erase t).erase s := by
          ext u
          simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          tauto
        change (∑ u ∈ ((Finset.univ : Finset P).erase s).erase t,
          highBranchMissCount G v t u) = highBranchMatchedCount G v t
        rw [herase]
        exact hrow
  have hunmatchedExistsSaver : ∀ a ∈ unmatched,
      (G.neighborFinset a ∩ saver).Nonempty := by
    intro a haU
    have haBs : a ∈ Bs := (Finset.mem_filter.mp haU).1
    have haInternalZero : (G.neighborFinset a ∩ Bs).card = 0 :=
      (Finset.mem_filter.mp haU).2
    have haSecond : a ∈ secondLayer G v := by
      rw [secondLayer]
      exact Finset.mem_biUnion.mpr ⟨s, by simp, haBs⟩
    have hmiss := card_farBranch_misses_eq_internalDegree
      G hfree hv hexternal s t hst a haBs (houterDegree haSecond)
    rw [haInternalZero] at hmiss
    have hfirst : ∀ u : {u : P // u ∈ M},
        (G.neighborFinset a ∩ secondLayerBranch G v u.1).card = 1 := by
      intro u
      have hle : (G.neighborFinset a ∩
          secondLayerBranch G v u.1).card ≤ 1 := by
        have hau : a ≠ u.1.1 := by
          intro hau
          exact (Finset.mem_sdiff.mp haBs).2 (by
            simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
            exact Or.inr (hau ▸ u.1.2))
        exact card_neighborFinset_inter_secondLayerBranch_le_one
          G hfree v a u.1 hau
      by_contra hne
      have hzero : (G.neighborFinset a ∩
          secondLayerBranch G v u.1).card = 0 := by omega
      have huFilter : u.1 ∈ (M.filter fun w =>
          (G.neighborFinset a ∩ secondLayerBranch G v w).card = 0) :=
        Finset.mem_filter.mpr ⟨u.2, hzero⟩
      have hempty : (M.filter fun w =>
          (G.neighborFinset a ∩ secondLayerBranch G v w).card = 0) = ∅ :=
        Finset.card_eq_zero.mp (by simpa [M, Bs] using hmiss)
      rw [hempty] at huFilter
      exact Finset.notMem_empty _ huFilter
    by_contra hnone
    have hinterEmpty : G.neighborFinset a ∩ saver = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hnone
    have hsecond : ∀ u : {u : P // u ∈ M},
        ∀ q ∈ G.neighborFinset a ∩ secondLayerBranch G v u.1,
          (G.neighborFinset q ∩ secondLayerBranch G v t).card = 1 := by
      intro u q hq
      have hle : (G.neighborFinset q ∩
          secondLayerBranch G v t).card ≤ 1 := by
        have hqt : q ≠ t.1 := by
          intro hqt
          subst q
          exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hq).2).2 (by
            simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
            exact Or.inr t.2)
        exact card_neighborFinset_inter_secondLayerBranch_le_one
          G hfree v q t hqt
      by_contra hne
      have hzero : (G.neighborFinset q ∩
          secondLayerBranch G v t).card = 0 := by omega
      have hqSaver : q ∈ saver := by
        apply Finset.mem_biUnion.mpr
        refine ⟨u.1, u.2, ?_⟩
        exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hq).2, hzero⟩
      have hqInter : q ∈ G.neighborFinset a ∩ saver :=
        Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hq).1, hqSaver⟩
      rw [hinterEmpty] at hqInter
      exact Finset.notMem_empty _ hqInter
    exact false_of_squareOrder_pairedBranch_fullFan
      G hfree hd hv hneigh hlocal s t hst a haBs hfirst hsecond
  let chooseSaver : {a // a ∈ unmatched} → V := fun a =>
    (hunmatchedExistsSaver a.1 a.2).choose
  have hchooseSaverMem : ∀ a : {a // a ∈ unmatched},
      chooseSaver a ∈ G.neighborFinset a.1 ∩ saver := by
    intro a
    exact (hunmatchedExistsSaver a.1 a.2).choose_spec
  let chooseSaverSubtype : {a // a ∈ unmatched} → {q // q ∈ saver} := fun a =>
    ⟨chooseSaver a, (Finset.mem_inter.mp (hchooseSaverMem a)).2⟩
  have hchooseInjective : Function.Injective chooseSaverSubtype := by
    intro a b hab
    apply Subtype.ext
    by_contra habv
    have hqeq : chooseSaver a = chooseSaver b :=
      congrArg Subtype.val hab
    have hqa : G.Adj (chooseSaver a) a.1 := by
      have := (Finset.mem_inter.mp (hchooseSaverMem a)).1
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
    have hqb : G.Adj (chooseSaver a) b.1 := by
      have := (Finset.mem_inter.mp (hchooseSaverMem b)).1
      rw [← hqeq] at this
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
    have hsa : G.Adj s.1 a.1 := by
      have haBs := (Finset.mem_filter.mp a.2).1
      exact (G.mem_neighborFinset s.1 a.1).mp
        (Finset.mem_sdiff.mp haBs).1
    have hsb : G.Adj s.1 b.1 := by
      have hbBs := (Finset.mem_filter.mp b.2).1
      exact (G.mem_neighborFinset s.1 b.1).mp
        (Finset.mem_sdiff.mp hbBs).1
    have hqs : chooseSaver a ≠ s.1 := by
      intro hqs
      have hqSaver := (Finset.mem_inter.mp (hchooseSaverMem a)).2
      rcases Finset.mem_biUnion.mp hqSaver with ⟨u, _, hqu⟩
      have hqBranch := (Finset.mem_filter.mp hqu).1
      exact (Finset.mem_sdiff.mp hqBranch).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr (hqs ▸ s.2))
    exact hfree (containsC4_of_two_common habv hqs
      hqa hqb hsa hsb)
  have hUle : unmatched.card ≤ saver.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective chooseSaverSubtype hchooseInjective
  have hinternalLe : ∀ a ∈ Bs,
      (G.neighborFinset a ∩ Bs).card ≤ 1 := by
    intro a ha
    have has : a ≠ s.1 := by
      intro has
      subst a
      exact (Finset.mem_sdiff.mp ha).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr s.2)
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v a s has
  have hpartition : unmatched.card + highBranchMatchedCount G v s = Bs.card := by
    have hfilters := Finset.card_filter_add_card_filter_not
      (s := Bs) (p := fun a =>
        (G.neighborFinset a ∩ Bs).card = 0)
    have hnotEq : (Bs.filter fun a =>
        ¬(G.neighborFinset a ∩ Bs).card = 0) =
        Bs.filter fun a => (G.neighborFinset a ∩ Bs).card = 1 := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, hzero⟩
        have hle := hinternalLe a ha
        exact ⟨ha, by omega⟩
      · rintro ⟨ha, hone⟩
        exact ⟨ha, by omega⟩
    rw [hnotEq] at hfilters
    simpa [unmatched, Bs, highBranchMatchedCount] using hfilters
  rw [hsaverCard] at hUle
  dsimp [unmatched, Bs] at hUle hpartition ⊢
  omega

/-- At square order the paired saver inequality reads
`d - 2 ≤ M_s + M_t`. -/
theorem squareOrder_sub_two_le_add_matchedCounts_of_paired
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1) :
    d - 2 ≤ highBranchMatchedCount G v s + highBranchMatchedCount G v t := by
  have hsave := card_branch_le_add_matchedCounts_of_paired
    G hfree hd hv hneigh hlocal hexternal houterDegree s t hst
  rw [card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
    G (by omega) hv hneigh hlocal s] at hsave
  exact hsave

/-- For odd `d`, both matched counts are even, so the paired lower bound
rounds up from the odd number `d-2` to `d-1`. -/
theorem squareOrder_sub_one_le_add_matchedCounts_of_paired_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d) (hodd : Odd d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1) :
    d - 1 ≤ highBranchMatchedCount G v s + highBranchMatchedCount G v t := by
  have hbase := squareOrder_sub_two_le_add_matchedCounts_of_paired
    G hfree hd hv hneigh hlocal hexternal houterDegree s t hst
  have hevenS := even_highBranchMatchedCount G hfree s
  have hevenT := even_highBranchMatchedCount G hfree t
  rcases hodd with ⟨k, hk⟩
  rcases hevenS with ⟨m, hm⟩
  rcases hevenT with ⟨n, hn⟩
  omega

end

end Erdos85
