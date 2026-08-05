import Proofs.CycleDoubleCoverPort.NashWilliams3

/-
# Cycle Double Cover port, step 4 (part 4): Kaiser's improvement step and
# the Nash-Williams--Tutte theorem

VENDORED FILE — adapted from upstream `openai/cdc-lean`.

Final slice of the port of upstream `CDCLean/NashWilliams.lean` (3,657 lines);
see #43629 for part 1 and `NashWilliams2.lean` / `NashWilliams3.lean` for parts
2 and 3. This part covers upstream lines ~2570-3653: Kaiser's counting equality,
necessity of the partition condition, the superfluous-edge and level machinery,
Kaiser's improvement step, and the headline theorem

  `nashWilliamsTutte : G.HasTreePacking k ↔ G.SatisfiesTreePackingCondition k`

which completes step 4 of the port.

## Provenance, attribution and licensing — READ BEFORE RESTATING

Upstream: https://github.com/openai/cdc-lean, file `CDCLean/NashWilliams.lean`,
pinned at Lean `v4.31.0` / Mathlib `9a9483a92959bc92bd6a60176dd1fe597298c1f8`
— the same pin this repository uses. Original authorship is upstream's.

Like `NashWilliams3.lean` (and unlike parts 1 and 2, which are independent
re-derivations with no upstream text copied), **this file vendors upstream proof
scripts**, adapted only for our namespace `CycleDoubleCover` and for the fact
that a few declarations (`classFiberEquiv`, `quotientSigmaEquiv`,
`sum_card_setoid_classes`, `packing_index_unique`, `coloringOfPacking`,
`colorClass_coloringOfPacking`, `satisfiesTreePackingCondition_mono`) already
landed in part 1 and are therefore not restated here.

`openai/cdc-lean` carries **no license file**. That means default copyright —
all rights reserved. It is *not* public domain, and the absence of a license is
not a grant: publishing a repository does not waive copyright, and GitHub's ToS
grants only viewing and forking, not reproduction or adaptation. A permissive
licence was requested upstream on 2026-07-12 (openai/cdc-lean#4); there was no
response and the upstream issue tracker has since been disabled.

This file is vendored under the operator's explicit **risk acceptance** recorded
on #37507 (comment of 2026-08-03), which permits vendoring with attribution. It
is an accepted risk, not a determination that reuse is permitted. If upstream
ever objects, this file and `NashWilliams3.lean` are the units of removal.

## Ported in this part

`crossingClass_card_eq_of_spanningTree_of_internal`,
`quotient_card_sub_one_le_crossingClass_card`,
`quotient_card_sub_one_le_crossingEdges_card`,
`satisfiesTreePackingCondition_of_hasTreePacking`,
`hasSuperfluousEdge_of_condition_of_disconnected`,
`exists_lower_level_tree_edge_of_superfluous`,
`exists_lower_level_tree_edge_on_path_of_superfluous`, `finiteLevelValue`,
`finiteLevelValue_spec`, `finiteLevelValue_eq_of_level`,
`exists_firstDisconnectedColor_of_finiteLevel`,
`finiteLevel_of_partitions_eq_upto`,
`exists_min_level_tree_edge_on_path_of_superfluous`,
`exists_min_level_tree_edge_on_path_anchored_of_superfluous`,
`kaiserPartition_eq_upto_of_min_exchange`, `HasSuperfluousLevel`,
`minSuperfluousLevel`, `minSuperfluousLevel_spec`, `minSuperfluousLevel_le`,
`HasKaiserImprovementStep`, `hasKaiserImprovementStep_of_condition`,
`exists_connected_residual_of_kaiser_step`, `hasTreePacking_of_kaiser_steps`,
`hasTreePacking_of_condition`, `nashWilliamsTutte`.

With this file, upstream `CDCLean/NashWilliams.lean` is fully ported: step 4 of
#37507 is complete. Steps 5-8 (FlowCount/SixFlow, JaegerKilpatrick,
CubicLabeling/CubicTheorem, Main) remain.

There are no `sorry`s, no `native_decide`, and no `axiom` declarations here.
This file does **not** discharge `CycleDoubleCover.cycleDoubleCover_of_bridgeless`;
that is done in
`CycleDoubleCoverPort/Main.lean`, the last file of the port.
-/

namespace CycleDoubleCover

namespace FiniteGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

omit [DecidableEq V] in
/-- Kaiser's counting equality: a spanning tree that is connected inside every
partition class has exactly one fewer crossing edge than there are classes. -/
theorem crossingClass_card_eq_of_spanningTree_of_internal [Nonempty V]
    (S : Finset E) (P : Setoid V)
    (hTree : G.IsSpanningTree S) (hInt : G.InternallyConnected S P) :
    (G.crossingClass S P).card = Nat.card (Quotient P) - 1 := by
  classical
  letI : Nonempty (Quotient P) := Nonempty.map (Quotient.mk P) inferInstance
  choose F hFsub hFcard using
    fun q : Quotient P =>
      G.exists_internal_tree_subset S P (Quotient.out q) hInt
  have hpair :
      (↑(Finset.univ : Finset (Quotient P)) : Set (Quotient P)).PairwiseDisjoint F := by
    intro q _ r _ hqr
    apply Finset.disjoint_left.2
    intro e heq her
    have heq' := hFsub q heq
    have her' := hFsub r her
    have hq := ((mem_insideEdges (G := G)).mp heq').2.1
    have hr := ((mem_insideEdges (G := G)).mp her').2.1
    have hrel : P.r (Quotient.out q) (Quotient.out r) :=
      P.trans (P.symm hq) hr
    apply hqr
    calc
      q = Quotient.mk P (Quotient.out q) := (Quotient.out_eq q).symm
      _ = Quotient.mk P (Quotient.out r) := Quotient.sound hrel
      _ = r := Quotient.out_eq r
  let I : Finset E := Finset.univ.biUnion F
  have hIcard : I.card = ∑ q : Quotient P, (F q).card := by
    simpa [I] using Finset.card_biUnion hpair
  have hcrossI : Disjoint (G.crossingClass S P) I := by
    apply Finset.disjoint_left.2
    intro e heCross heI
    rcases Finset.mem_biUnion.mp heI with ⟨q, _, heq⟩
    have heq' := hFsub q heq
    have hi := (mem_insideEdges (G := G)).mp heq'
    exact ((mem_crossingClass (G := G)).mp heCross).2
      (P.trans hi.2.1 (P.symm hi.2.2))
  have hUnionSub : G.crossingClass S P ∪ I ⊆ S := by
    intro e he
    rcases Finset.mem_union.mp he with heCross | heI
    · exact ((mem_crossingClass (G := G)).mp heCross).1
    · rcases Finset.mem_biUnion.mp heI with ⟨q, _, heq⟩
      exact ((mem_insideEdges (G := G)).mp (hFsub q heq)).1
  have hsum :
      (∑ q : Quotient P, (F q).card) + Nat.card (Quotient P) =
        Fintype.card V := by
    calc
      (∑ q : Quotient P, (F q).card) + Nat.card (Quotient P) =
          (∑ q : Quotient P, (F q).card) + ∑ q : Quotient P, 1 := by
        simp [Nat.card_eq_fintype_card]
      _ = ∑ q : Quotient P, ((F q).card + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ q : Quotient P,
          Nat.card {v : V // P.r v (Quotient.out q)} := by
        apply Finset.sum_congr rfl
        intro q _
        exact hFcard q
      _ = Fintype.card V := sum_card_setoid_classes (V := V) P
  have hupper :
      (G.crossingClass S P).card + ∑ q : Quotient P, (F q).card ≤ S.card := by
    calc
      (G.crossingClass S P).card + ∑ q : Quotient P, (F q).card =
          (G.crossingClass S P ∪ I).card := by
        rw [← hIcard]
        exact (Finset.card_union_of_disjoint hcrossI).symm
      _ ≤ S.card := Finset.card_le_card hUnionSub
  have hlow :
      Nat.card (Quotient P) - 1 ≤ (G.crossingClass S P).card := by
    let Q := G.quotientGraph S P
    obtain ⟨T, hTuniv, hTtree⟩ :=
      Q.exists_isSpanningTree_subset_of_connects Finset.univ
        (G.quotientGraph_connected_of_connects S P hTree.1)
    have hTle : T.card ≤ (Finset.univ :
        Finset {e : E // e ∈ G.crossingClass S P}).card :=
      Finset.card_le_card hTuniv
    have hcard : T.card + 1 = Nat.card (Quotient P) := by
      simpa [Q, Nat.card_eq_fintype_card] using hTtree.2
    have hTcard : T.card = Nat.card (Quotient P) - 1 := by omega
    rw [← hTcard]
    simpa using hTle
  have hpos : 0 < Nat.card (Quotient P) := Nat.card_pos
  have hTreeCard := hTree.2
  have hupper' :
      (G.crossingClass S P).card ≤ Nat.card (Quotient P) - 1 := by
    omega
  exact le_antisymm hupper' hlow

omit [DecidableEq V] in
/-- Every connected edge set has at least one crossing edge per non-root quotient
class.  This is the elementary lower-bound half of the partition count: contract the
partition classes and take a spanning tree in the contracted multigraph. -/
theorem quotient_card_sub_one_le_crossingClass_card [Nonempty V]
    (S : Finset E) (P : Setoid V) (hS : G.Connects S) :
    Nat.card (Quotient P) - 1 ≤ (G.crossingClass S P).card := by
  classical
  letI : Nonempty (Quotient P) := Nonempty.map (Quotient.mk P) inferInstance
  let Q := G.quotientGraph S P
  obtain ⟨T, hTuniv, hTtree⟩ :=
    Q.exists_isSpanningTree_subset_of_connects Finset.univ
      (G.quotientGraph_connected_of_connects S P hS)
  have hTle : T.card ≤ (Finset.univ :
      Finset {e : E // e ∈ G.crossingClass S P}).card :=
    Finset.card_le_card hTuniv
  have hcard : T.card + 1 = Nat.card (Quotient P) := by
    simpa [Q, Nat.card_eq_fintype_card] using hTtree.2
  have hTcard : T.card = Nat.card (Quotient P) - 1 := by omega
  rw [← hTcard]
  simpa using hTle

omit [DecidableEq V] in
theorem quotient_card_sub_one_le_crossingEdges_card [Nonempty V]
    (S : Finset E) (P : Setoid V) (hS : G.Connects S) :
    Nat.card (Quotient P) - 1 ≤ (G.crossingEdges P).card := by
  exact (G.quotient_card_sub_one_le_crossingClass_card S P hS).trans
    (Finset.card_le_card (G.crossingClass_subset_crossingEdges S P))

omit [DecidableEq V] in
/-- The easy direction of Nash-Williams--Tutte: disjoint spanning trees supply disjoint
crossing-edge sets for every partition. -/
theorem satisfiesTreePackingCondition_of_hasTreePacking [Nonempty V] {k : ℕ}
    (hpack : G.HasTreePacking k) :
    G.SatisfiesTreePackingCondition k := by
  classical
  rcases hpack with ⟨T, htree, hdisj⟩
  intro P
  let C : Fin k → Finset E := fun i => G.crossingClass (T i) P
  have hCsub : ∀ i : Fin k, C i ⊆ G.crossingEdges P := by
    intro i
    exact G.crossingClass_subset_crossingEdges (T i) P
  have hpair :
      (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint C := by
    intro i _ j _ hij
    apply Finset.disjoint_left.2
    intro e hei hej
    have heiT : e ∈ T i := ((mem_crossingClass (G := G)).mp hei).1
    have hejT : e ∈ T j := ((mem_crossingClass (G := G)).mp hej).1
    exact (Finset.disjoint_left.mp (hdisj i j hij) heiT hejT).elim
  have hlow : ∀ i : Fin k,
      Nat.card (Quotient P) - 1 ≤ (C i).card := by
    intro i
    exact G.quotient_card_sub_one_le_crossingClass_card (T i) P (htree i).1
  let U : Finset E := Finset.univ.biUnion C
  have hUsub : U ⊆ G.crossingEdges P := by
    intro e he
    rcases Finset.mem_biUnion.mp he with ⟨i, _, hei⟩
    exact hCsub i hei
  calc
    k * (Nat.card (Quotient P) - 1) =
        ∑ i : Fin k, (Nat.card (Quotient P) - 1) := by simp
    _ ≤ ∑ i : Fin k, (C i).card := by
      exact Finset.sum_le_sum fun i _ => hlow i
    _ = U.card := by
      symm
      simpa [U] using (Finset.card_biUnion hpair)
    _ ≤ (G.crossingEdges P).card := Finset.card_le_card hUsub

omit [DecidableEq V] in
/-- At a stable Kaiser partition, the partition inequality forces a cyclic residual
edge crossing that partition; hence that edge has a finite level and is superfluous. -/
theorem hasSuperfluousEdge_of_condition_of_disconnected [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)}
    (hprefix : G.PrefixTrees χ)
    (hdisc : ¬ G.Connects (residualClass χ))
    (hcond : G.SatisfiesTreePackingCondition (k + 1)) :
    G.HasSuperfluousEdge χ := by
  classical
  obtain ⟨n, hstable⟩ := G.exists_stable_kaiserPartition χ
  let P := G.kaiserPartition χ n
  have hInt : ∀ i : Fin (k + 1),
      G.InternallyConnected (colorClass χ i) P := by
    intro i
    exact G.internallyConnected_of_stable hstable i
  have hprefixCross : ∀ i : Fin k,
      (G.crossingClass (colorClass χ i.castSucc) P).card =
        Nat.card (Quotient P) - 1 := by
    intro i
    exact G.crossingClass_card_eq_of_spanningTree_of_internal
      (colorClass χ i.castSucc) P (hprefix i) (hInt i.castSucc)
  have hprefixSum :
      (∑ i : Fin k,
        (G.crossingClass (colorClass χ i.castSucc) P).card) =
        k * (Nat.card (Quotient P) - 1) := by
    simp_rw [hprefixCross]
    simp
  have hcondP := hcond P
  have htotal := G.crossingEdges_card_eq_sum_crossingClass χ P
  rw [htotal, Fin.sum_univ_castSucc, hprefixSum] at hcondP
  change (k + 1) * (Nat.card (Quotient P) - 1) ≤
      k * (Nat.card (Quotient P) - 1) +
        (G.crossingClass (residualClass χ) P).card at hcondP
  have hresge :
      Nat.card (Quotient P) - 1 ≤
        (G.crossingClass (residualClass χ) P).card := by
    have hcancel :
        k * (Nat.card (Quotient P) - 1) + (Nat.card (Quotient P) - 1) ≤
          k * (Nat.card (Quotient P) - 1) +
            (G.crossingClass (residualClass χ) P).card := by
      simpa [Nat.add_mul] using hcondP
    exact Nat.le_of_add_le_add_left hcancel
  let Q := G.quotientGraph (residualClass χ) P
  have hQdisc : ¬ Q.Connects Finset.univ := by
    intro hQ
    apply hdisc
    exact G.connects_of_internal_of_quotient_connects
      (residualClass χ) P (hInt (Fin.last k)) hQ
  letI : Nonempty (Quotient P) := Nonempty.map (Quotient.mk P) inferInstance
  have hcardQ :
      Fintype.card (Quotient P) - 1 ≤
        (Finset.univ :
          Finset {e : E // e ∈ G.crossingClass (residualClass χ) P}).card := by
    simpa [Nat.card_eq_fintype_card] using hresge
  obtain ⟨e, heQ⟩ := Q.exists_cyclic_of_disconnected_of_card_ge
    Finset.univ hQdisc hcardQ
  have hecyc : G.IsCyclicEdge (residualClass χ) e.1 :=
    G.cyclicEdge_of_quotient_cyclic_of_internal (hInt (Fin.last k)) heQ
  have hnotP :
      ¬ P.r (G.endAt e.1 0) (G.endAt e.1 1) :=
    ((mem_crossingClass (G := G)).mp e.2).2
  obtain ⟨m, hm⟩ := G.exists_finiteLevel_of_not_rel (χ := χ) hnotP
  exact ⟨e.1, m, hecyc, hm⟩

/-- The first exchange choice in Kaiser: a superfluous residual edge of level m
finds a prefix-tree edge on the corresponding tree path whose level is smaller. -/
theorem exists_lower_level_tree_edge_of_superfluous [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {m : ℕ}
    (hprefix : G.PrefixTrees χ)
    (hsuper : G.IsSuperfluousAt χ e m) :
    ∃ i : Fin k, ∃ e' : E, ∃ j : ℕ,
      e' ∈ colorClass χ i.castSucc ∧
        j < m ∧ G.HasFiniteLevel χ e' j := by
  classical
  let P := G.kaiserPartition χ m
  have hlev := hsuper.2
  have heRes : e ∈ residualClass χ := hsuper.1.1
  have hsome : ∃ c : Fin (k + 1),
      G.firstDisconnectedColor χ P = some c := by
    cases hopt : G.firstDisconnectedColor χ P with
    | none =>
        exfalso
        apply hlev.2
        change (G.refineOnce χ P).r (G.endAt e 0) (G.endAt e 1)
        rw [refineOnce, hopt]
        exact hlev.1
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hsome
  have hnotRoute :
      ¬ G.ReachableIn (G.insideEdges (colorClass χ c) P (G.endAt e 0))
        (G.endAt e 0) (G.endAt e 1) := by
    intro hroute
    apply hlev.2
    change (G.refineOnce χ P).r (G.endAt e 0) (G.endAt e 1)
    rw [refineOnce, hc]
    exact ⟨hlev.1, hroute⟩
  have hcLast : c ≠ Fin.last k := by
    intro hlast
    subst c
    apply hnotRoute
    have heInside :
        e ∈ G.insideEdges (residualClass χ) P (G.endAt e 0) := by
      apply (mem_insideEdges (G := G)).mpr
      exact ⟨heRes, P.refl _, P.symm hlev.1⟩
    have heInside' :
        e ∈ G.insideEdges (colorClass χ (Fin.last k)) P (G.endAt e 0) := by
      simpa [residualClass] using heInside
    apply SimpleGraph.Adj.reachable
    rw [G.supportGraph_adj_iff
      (G.insideEdges (colorClass χ (Fin.last k)) P (G.endAt e 0))
      (G.endAt e 0) (G.endAt e 1)]
    exact ⟨G.loopless e, e, heInside', Or.inl ⟨rfl, rfl⟩⟩
  rcases Fin.eq_castSucc_or_eq_last c with ⟨i, rfl⟩ | rfl
  · have hreach :
        (G.supportGraph (colorClass χ i.castSucc)).Reachable
          (G.endAt e 0) (G.endAt e 1) :=
      (hprefix i).1.preconnected _ _
    apply hreach.elim_path
    intro p
    obtain ⟨e', he'T, he'path, he'cross⟩ :=
      G.exists_crossing_tree_edge_of_not_internal_reachable p hnotRoute
    obtain ⟨j, hj⟩ :=
      G.exists_finiteLevel_of_not_rel (χ := χ) (n := m) he'cross
    have hjm : j < m := by
      by_contra hnot
      have hmj : m ≤ j := Nat.le_of_not_gt hnot
      apply he'cross
      exact G.kaiserPartition_refines_of_le χ hmj hj.1
    exact ⟨i, e', j, he'T, hjm, hj⟩
  · exact (hcLast rfl).elim

/-- The same exchange choice, retaining the fundamental tree path needed for the
actual recoloring. -/
theorem exists_lower_level_tree_edge_on_path_of_superfluous [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {m : ℕ}
    (hprefix : G.PrefixTrees χ)
    (hsuper : G.IsSuperfluousAt χ e m) :
    ∃ i : Fin k, ∃ e' : E, ∃ j : ℕ,
      ∃ p : (G.supportGraph (colorClass χ i.castSucc)).Path
          (G.endAt e 0) (G.endAt e 1),
        e' ∈ colorClass χ i.castSucc ∧
          G.symEdge e' ∈ p.1.edges ∧
          j < m ∧ G.HasFiniteLevel χ e' j := by
  classical
  let P := G.kaiserPartition χ m
  have hlev := hsuper.2
  have heRes : e ∈ residualClass χ := hsuper.1.1
  have hsome : ∃ c : Fin (k + 1),
      G.firstDisconnectedColor χ P = some c := by
    cases hopt : G.firstDisconnectedColor χ P with
    | none =>
        exfalso
        apply hlev.2
        change (G.refineOnce χ P).r (G.endAt e 0) (G.endAt e 1)
        rw [refineOnce, hopt]
        exact hlev.1
    | some c => exact ⟨c, rfl⟩
  obtain ⟨c, hc⟩ := hsome
  have hnotRoute :
      ¬ G.ReachableIn (G.insideEdges (colorClass χ c) P (G.endAt e 0))
        (G.endAt e 0) (G.endAt e 1) := by
    intro hroute
    apply hlev.2
    change (G.refineOnce χ P).r (G.endAt e 0) (G.endAt e 1)
    rw [refineOnce, hc]
    exact ⟨hlev.1, hroute⟩
  have hcLast : c ≠ Fin.last k := by
    intro hlast
    subst c
    apply hnotRoute
    have heInside :
        e ∈ G.insideEdges (residualClass χ) P (G.endAt e 0) := by
      apply (mem_insideEdges (G := G)).mpr
      exact ⟨heRes, P.refl _, P.symm hlev.1⟩
    have heInside' :
        e ∈ G.insideEdges (colorClass χ (Fin.last k)) P (G.endAt e 0) := by
      simpa [residualClass] using heInside
    apply SimpleGraph.Adj.reachable
    rw [G.supportGraph_adj_iff
      (G.insideEdges (colorClass χ (Fin.last k)) P (G.endAt e 0))
      (G.endAt e 0) (G.endAt e 1)]
    exact ⟨G.loopless e, e, heInside', Or.inl ⟨rfl, rfl⟩⟩
  rcases Fin.eq_castSucc_or_eq_last c with ⟨i, rfl⟩ | rfl
  · have hreach :
        (G.supportGraph (colorClass χ i.castSucc)).Reachable
          (G.endAt e 0) (G.endAt e 1) :=
      (hprefix i).1.preconnected _ _
    apply hreach.elim_path
    intro p
    obtain ⟨e', he'T, he'path, he'cross⟩ :=
      G.exists_crossing_tree_edge_of_not_internal_reachable p hnotRoute
    obtain ⟨j, hj⟩ :=
      G.exists_finiteLevel_of_not_rel (χ := χ) (n := m) he'cross
    have hjm : j < m := by
      by_contra hnot
      have hmj : m ≤ j := Nat.le_of_not_gt hnot
      apply he'cross
      exact G.kaiserPartition_refines_of_le χ hmj hj.1
    exact ⟨i, e', j, p, he'T, he'path, hjm, hj⟩
  · exact (hcLast rfl).elim

noncomputable def finiteLevelValue {k : ℕ} (χ : E → Fin k) (e : E) : ℕ := by
  classical
  exact if h : ∃ m, G.HasFiniteLevel χ e m then Nat.find h else 0

omit [DecidableEq V] [DecidableEq E] in
theorem finiteLevelValue_spec {k : ℕ} {χ : E → Fin k} {e : E}
    (h : ∃ m, G.HasFiniteLevel χ e m) :
    G.HasFiniteLevel χ e (G.finiteLevelValue χ e) := by
  classical
  unfold finiteLevelValue
  rw [dif_pos h]
  exact Nat.find_spec h

omit [DecidableEq V] [DecidableEq E] in
theorem finiteLevelValue_eq_of_level {k : ℕ} {χ : E → Fin k} {e : E} {m : ℕ}
    (hm : G.HasFiniteLevel χ e m) :
    G.finiteLevelValue χ e = m :=
  G.finiteLevel_unique (G.finiteLevelValue_spec ⟨m, hm⟩) hm

omit [DecidableEq V] [DecidableEq E] in
theorem exists_firstDisconnectedColor_of_finiteLevel {k : ℕ}
    {χ : E → Fin k} {e : E} {j : ℕ}
    (hj : G.HasFiniteLevel χ e j) :
    ∃ c : Fin k,
      G.firstDisconnectedColor χ (G.kaiserPartition χ j) = some c := by
  cases hc : G.firstDisconnectedColor χ (G.kaiserPartition χ j) with
  | some c => exact ⟨c, rfl⟩
  | none =>
      have hstable := G.kaiserPartition_stable_after hc
      exfalso
      apply hj.2
      have hnext := hstable 1
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (hnext ▸ hj.1)

omit [DecidableEq V] [DecidableEq E] in
theorem finiteLevel_of_partitions_eq_upto {k : ℕ}
    {χ χ' : E → Fin k} {e : E} {n j : ℕ}
    (hEq : ∀ t : ℕ, t ≤ j →
      G.kaiserPartition χ' t = G.kaiserPartition χ t)
    (hnj : n < j)
    (hn : G.HasFiniteLevel χ e n) :
    G.HasFiniteLevel χ' e n := by
  constructor
  · rw [hEq n (Nat.le_of_lt hnj)]
    exact hn.1
  · rw [hEq (n + 1) (Nat.succ_le_of_lt hnj)]
    exact hn.2

/-- Choose the exchanged tree edge with minimum finite level on the fundamental
path.  Consequently every tree edge on that path has both ends in its level-j
class. -/
theorem exists_min_level_tree_edge_on_path_of_superfluous [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {m : ℕ}
    (hprefix : G.PrefixTrees χ)
    (hsuper : G.IsSuperfluousAt χ e m) :
    ∃ i : Fin k, ∃ e' : E, ∃ j : ℕ,
      ∃ p : (G.supportGraph (colorClass χ i.castSucc)).Path
          (G.endAt e 0) (G.endAt e 1),
        e' ∈ colorClass χ i.castSucc ∧
          G.symEdge e' ∈ p.1.edges ∧
          j < m ∧ G.HasFiniteLevel χ e' j ∧
          ∀ f ∈ colorClass χ i.castSucc, G.symEdge f ∈ p.1.edges →
            (G.kaiserPartition χ j).r (G.endAt f 0) (G.endAt f 1) := by
  classical
  obtain ⟨i, e₀, j₀, p, he₀T, he₀path, hj₀m, hj₀⟩ :=
    G.exists_lower_level_tree_edge_on_path_of_superfluous hprefix hsuper
  let A : Finset E :=
    (colorClass χ i.castSucc).filter fun f =>
      G.symEdge f ∈ p.1.edges ∧ ∃ n, G.HasFiniteLevel χ f n
  have hA : A.Nonempty := by
    have he₀Fin : ∃ n, G.HasFiniteLevel χ e₀ n := ⟨j₀, hj₀⟩
    exact ⟨e₀, Finset.mem_filter.mpr
      ⟨he₀T, he₀path, he₀Fin⟩⟩
  obtain ⟨e', he'A, he'min⟩ :=
    Finset.exists_min_image A (G.finiteLevelValue χ) hA
  have he'A' := Finset.mem_filter.mp he'A
  let j := G.finiteLevelValue χ e'
  have hj : G.HasFiniteLevel χ e' j :=
    G.finiteLevelValue_spec he'A'.2.2
  have hjle : j ≤ j₀ := by
    have he₀A : e₀ ∈ A := by
      have he₀Fin : ∃ n, G.HasFiniteLevel χ e₀ n := ⟨j₀, hj₀⟩
      exact Finset.mem_filter.mpr ⟨he₀T, he₀path, he₀Fin⟩
    have hmin := he'min e₀ he₀A
    simpa [j, G.finiteLevelValue_eq_of_level hj₀] using hmin
  have hjm : j < m := lt_of_le_of_lt hjle hj₀m
  refine ⟨i, e', j, p, he'A'.1, he'A'.2.1, hjm, hj, ?_⟩
  intro f hfT hfpath
  by_contra hnot
  obtain ⟨n, hn⟩ :=
    G.exists_finiteLevel_of_not_rel (χ := χ) (n := j) hnot
  have hnj : n < j := by
    by_contra hnotlt
    have hjn : j ≤ n := Nat.le_of_not_gt hnotlt
    apply hnot
    exact G.kaiserPartition_refines_of_le χ hjn hn.1
  have hfA : f ∈ A := by
    exact Finset.mem_filter.mpr ⟨hfT, hfpath, ⟨n, hn⟩⟩
  have hjleN := he'min f hfA
  have hjeq : G.finiteLevelValue χ e' = j := rfl
  have hneq : G.finiteLevelValue χ f = n :=
    G.finiteLevelValue_eq_of_level hn
  rw [hjeq, hneq] at hjleN
  exact (Nat.not_lt_of_ge hjleN hnj)

theorem exists_min_level_tree_edge_on_path_anchored_of_superfluous
    [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {m : ℕ}
    (hprefix : G.PrefixTrees χ)
    (hsuper : G.IsSuperfluousAt χ e m) :
    ∃ i : Fin k, ∃ e' : E, ∃ j : ℕ,
      ∃ p : (G.supportGraph (colorClass χ i.castSucc)).Path
          (G.endAt e 0) (G.endAt e 1),
        e' ∈ colorClass χ i.castSucc ∧
          G.symEdge e' ∈ p.1.edges ∧
          j < m ∧ G.HasFiniteLevel χ e' j ∧
          ∀ f ∈ colorClass χ i.castSucc, G.symEdge f ∈ p.1.edges →
            (G.kaiserPartition χ j).r (G.endAt f 0) (G.endAt e 0) ∧
              (G.kaiserPartition χ j).r (G.endAt f 1) (G.endAt e 0) := by
  obtain ⟨i, e', j, p, he'T, he'path, hjm, hj, hno⟩ :=
    G.exists_min_level_tree_edge_on_path_of_superfluous hprefix hsuper
  refine ⟨i, e', j, p, he'T, he'path, hjm, hj, ?_⟩
  intro f hfT hfpath
  exact G.path_edge_ends_rel_start_of_no_crossing p.1 hno hfpath

/-- Kaiser's claim: after exchanging a minimum-level edge on the fundamental
cycle, the deterministic partition sequence is unchanged through that level. -/
theorem kaiserPartition_eq_upto_of_min_exchange [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {m : ℕ}
    {i : Fin k} {e' : E} {j : ℕ}
    {p : (G.supportGraph (colorClass χ i.castSucc)).Path
      (G.endAt e 0) (G.endAt e 1)}
    (hprefix : G.PrefixTrees χ)
    (hsuper : G.IsSuperfluousAt χ e m)
    (hmin : ∀ f n, G.IsSuperfluousAt χ f n → m ≤ n)
    (he'T : e' ∈ colorClass χ i.castSucc)
    (he'path : G.symEdge e' ∈ p.1.edges)
    (hjm : j < m)
    (hj : G.HasFiniteLevel χ e' j)
    (hpath : ∀ f ∈ colorClass χ i.castSucc, G.symEdge f ∈ p.1.edges →
      (G.kaiserPartition χ j).r (G.endAt f 0) (G.endAt e 0) ∧
        (G.kaiserPartition χ j).r (G.endAt f 1) (G.endAt e 0)) :
    ∀ t : ℕ, t ≤ j →
      G.kaiserPartition (swapColor χ e e') t =
        G.kaiserPartition χ t := by
  classical
  have heRes : e ∈ residualClass χ := hsuper.1.1
  have hχe : χ e = Fin.last k := mem_colorClass.mp heRes
  have hχe' : χ e' = i.castSucc := mem_colorClass.mp he'T
  have hcol : χ e ≠ χ e' := by
    rw [hχe, hχe']
    exact (Fin.castSucc_ne_last i).symm
  have hee' : e ≠ e' := by
    intro h
    subst e'
    exact hcol rfl
  have htreeClass :
      colorClass (swapColor χ e e') i.castSucc =
        (colorClass χ i.castSucc).erase e' ∪ {e} := by
    simpa [hχe, hχe'] using colorClass_swap_right χ hee' hcol
  have hresClass :
      residualClass (swapColor χ e e') =
        (residualClass χ).erase e ∪ {e'} :=
    residualClass_swap_of_residual_of_tree heRes he'T
  intro t htj
  induction t with
  | zero => simp [kaiserPartition]
  | succ t ih =>
      have htltj : t < j := Nat.lt_of_succ_le htj
      have htj' : t ≤ j := Nat.le_of_lt htltj
      have hpart : G.kaiserPartition (swapColor χ e e') t =
          G.kaiserPartition χ t := ih htj'
      let P := G.kaiserPartition χ t
      have hsome : ∃ c : Fin (k + 1),
          G.firstDisconnectedColor χ P = some c := by
        cases hc : G.firstDisconnectedColor χ P with
        | some c => exact ⟨c, rfl⟩
        | none =>
            have hstable := G.kaiserPartition_stable_after hc
            have htjle : t ≤ j := Nat.le_of_lt htltj
            have hjEq : G.kaiserPartition χ j = P := by
              have h := hstable (j - t)
              simpa [P, Nat.add_sub_of_le htjle] using h
            have htj1le : t ≤ j + 1 := le_trans htjle (Nat.le_succ _)
            have hj1Eq : G.kaiserPartition χ (j + 1) = P := by
              have h := hstable (j + 1 - t)
              simpa [P, Nat.add_sub_of_le htj1le] using h
            exfalso
            apply hj.2
            rw [hj1Eq, ← hjEq]
            exact hj.1
      obtain ⟨c, hc⟩ := hsome
      have htm : t < m := lt_trans htltj hjm
      have hRefine : ∀ d : Fin (k + 1), d ≤ c →
          G.refineSetoid P (colorClass (swapColor χ e e') d) =
            G.refineSetoid P (colorClass χ d) := by
        intro d hdc
        by_cases hdi : d = i.castSucc
        · subst d
          rw [htreeClass]
          have heRel :
              P.r (G.endAt e 0) (G.endAt e 1) :=
            G.kaiserPartition_refines_of_le χ (Nat.le_of_lt htm)
              hsuper.2.1
          have hpathP : ∀ f ∈ colorClass χ i.castSucc,
              G.symEdge f ∈ p.1.edges →
                P.r (G.endAt f 0) (G.endAt e 0) ∧
                  P.r (G.endAt f 1) (G.endAt e 0) := by
            intro f hfT hfpath
            have hf := hpath f hfT hfpath
            exact ⟨G.kaiserPartition_refines_of_le χ htj' hf.1,
              G.kaiserPartition_refines_of_le χ htj' hf.2⟩
          exact G.refineSetoid_exchange_eq_of_path_internal
            (hprefix i) he'T p he'path heRel hpathP
        · by_cases hdlast : d = Fin.last k
          · subst d
            have hcLast : c = Fin.last k := by
              exact le_antisymm (Fin.le_last c) hdc
            have hnext :
                G.kaiserPartition χ (t + 1) =
                  G.refineSetoid P (residualClass χ) := by
              change G.refineOnce χ P = _
              rw [refineOnce, hc, hcLast]
              rfl
            have he'AtNext :
                (G.kaiserPartition χ (t + 1)).r
                  (G.endAt e' 0) (G.endAt e' 1) :=
              G.kaiserPartition_refines_of_le χ htj hj.1
            rw [hnext] at he'AtNext
            have he'Route :
                G.ReachableIn
                  (G.insideEdges ((residualClass χ).erase e) P (G.endAt e' 0))
                  (G.endAt e' 0) (G.endAt e' 1) :=
              G.reachableIn_inside_erase_of_min_superfluous
                hsuper hmin htm he'AtNext.2
            change G.refineSetoid P (residualClass (swapColor χ e e')) =
              G.refineSetoid P (residualClass χ)
            rw [hresClass]
            calc
              G.refineSetoid P ((residualClass χ).erase e ∪ {e'}) =
                  G.refineSetoid P ((residualClass χ).erase e) :=
                G.refineSetoid_union_singleton_eq_of_internal_reachable
                  he'Route
              _ = G.refineSetoid P (residualClass χ) :=
                G.refineSetoid_residual_erase_eq_of_min_superfluous
                  hsuper hmin htm
          · have hdNeE : d ≠ χ e := by
              rw [hχe]
              exact hdlast
            have hdNeE' : d ≠ χ e' := by
              rw [hχe']
              exact hdi
            rw [colorClass_swap_other χ hee' hdNeE hdNeE']
      have hbad : ¬ G.InternallyConnected (colorClass χ c) P :=
        G.firstDisconnectedColor_spec hc
      have hbad' :
          ¬ G.InternallyConnected (colorClass (swapColor χ e e') c) P := by
        intro h
        apply hbad
        exact (G.internallyConnected_iff_of_refineSetoid_eq
          (hRefine c le_rfl)).mp h
      have hbefore' : ∀ d : Fin (k + 1), d < c →
          G.InternallyConnected (colorClass (swapColor χ e e') d) P := by
        intro d hdc
        have hd := G.firstDisconnectedColor_internal_of_lt hc hdc
        exact (G.internallyConnected_iff_of_refineSetoid_eq
          (hRefine d (le_of_lt hdc))).mpr hd
      have hc' :
          G.firstDisconnectedColor (swapColor χ e e') P = some c :=
        G.firstDisconnectedColor_eq_some_of_spec hbad' hbefore'
      change G.refineOnce (swapColor χ e e')
          (G.kaiserPartition (swapColor χ e e') t) =
        G.refineOnce χ (G.kaiserPartition χ t)
      rw [hpart]
      change G.refineOnce (swapColor χ e e') P = G.refineOnce χ P
      unfold refineOnce
      rw [hc', hc]
      exact hRefine c le_rfl

def HasSuperfluousLevel {k : ℕ} (χ : E → Fin (k + 1)) (m : ℕ) : Prop :=
  ∃ e : E, G.IsSuperfluousAt χ e m

noncomputable def minSuperfluousLevel {k : ℕ} (χ : E → Fin (k + 1)) : ℕ := by
  classical
  exact if h : ∃ m, G.HasSuperfluousLevel χ m then Nat.find h else 0

omit [DecidableEq V] in
theorem minSuperfluousLevel_spec {k : ℕ} {χ : E → Fin (k + 1)}
    (h : G.HasSuperfluousEdge χ) :
    G.HasSuperfluousLevel χ (G.minSuperfluousLevel χ) := by
  classical
  unfold minSuperfluousLevel
  have hex : ∃ m, G.HasSuperfluousLevel χ m := by
    rcases h with ⟨e, m, hem⟩
    exact ⟨m, e, hem⟩
  rw [dif_pos hex]
  exact Nat.find_spec hex

omit [DecidableEq V] in
theorem minSuperfluousLevel_le {k : ℕ} {χ : E → Fin (k + 1)} {m : ℕ}
    (hm : G.HasSuperfluousLevel χ m) :
    G.minSuperfluousLevel χ ≤ m := by
  classical
  unfold minSuperfluousLevel
  have hex : ∃ n, G.HasSuperfluousLevel χ n := ⟨m, hm⟩
  rw [dif_pos hex]
  exact Nat.find_min' hex hm

/-- The one graph-theoretic improvement furnished by the middle part of Kaiser's proof:
from a disconnected residual class one can swap two edges and either reduce its component
count or keep that count while lowering the first superfluous level. -/
def HasKaiserImprovementStep (k : ℕ) : Prop :=
  ∀ χ : E → Fin (k + 1), G.PrefixTrees χ →
    ¬ G.Connects (residualClass χ) →
      ∃ χ' : E → Fin (k + 1), G.PrefixTrees χ' ∧
        (G.residualComponents χ' < G.residualComponents χ ∨
          G.residualComponents χ' = G.residualComponents χ ∧
            G.minSuperfluousLevel χ' < G.minSuperfluousLevel χ)

/-- The local exchange argument in Kaiser's proof supplies the improvement step
from the Nash-Williams partition inequality. -/
theorem hasKaiserImprovementStep_of_condition [Nonempty V] {k : ℕ}
    (hcond : G.SatisfiesTreePackingCondition (k + 1)) :
    G.HasKaiserImprovementStep k := by
  classical
  intro χ hprefix hdisc
  have hsup : G.HasSuperfluousEdge χ :=
    G.hasSuperfluousEdge_of_condition_of_disconnected hprefix hdisc hcond
  let m := G.minSuperfluousLevel χ
  obtain ⟨e, hsuper⟩ := G.minSuperfluousLevel_spec hsup
  have hmin : ∀ f n, G.IsSuperfluousAt χ f n → m ≤ n := by
    intro f n hfn
    exact G.minSuperfluousLevel_le ⟨f, hfn⟩
  obtain ⟨i, e', j, p, he'T, he'path, hjm, hj, hpath⟩ :=
    G.exists_min_level_tree_edge_on_path_anchored_of_superfluous hprefix hsuper
  let χ' := swapColor χ e e'
  have hprefix' : G.PrefixTrees χ' :=
    G.prefixTrees_swap_of_path_edge hprefix hsuper.1.1 he'T p he'path
  refine ⟨χ', hprefix', ?_⟩
  by_cases hj0 : j = 0
  · left
    subst j
    exact G.residualComponents_swap_lt_of_cyclic_of_not_reachable
      hsuper.1.1 he'T hsuper.1
      (G.not_reachable_residual_of_level_zero hprefix hdisc hj)
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have he'Reach :
        G.ReachableIn (residualClass χ)
          (G.endAt e' 0) (G.endAt e' 1) :=
      G.reachable_residual_of_positive_level hprefix hdisc hjpos hj
    have hcomp :
        G.residualComponents χ' = G.residualComponents χ :=
      G.residualComponents_swap_eq_of_cyclic_of_reachable
        hsuper.1.1 he'T hsuper.1 he'Reach
    have he'Cyc :
        G.IsCyclicEdge (residualClass χ') e' :=
      G.cyclicEdge_swap_of_cyclic_of_reachable
        hsuper.1.1 he'T hsuper.1 he'Reach
    have hEq : ∀ t : ℕ, t ≤ j →
        G.kaiserPartition χ' t = G.kaiserPartition χ t :=
      G.kaiserPartition_eq_upto_of_min_exchange
        hprefix hsuper hmin he'T he'path hjm hj hpath
    right
    refine ⟨hcomp, ?_⟩
    obtain ⟨c, hc⟩ :=
      G.exists_firstDisconnectedColor_of_finiteLevel hj
    let P := G.kaiserPartition χ j
    have hcNeTree : c ≠ i.castSucc := by
      intro hci
      apply hj.2
      change (G.refineOnce χ P).r (G.endAt e' 0) (G.endAt e' 1)
      rw [refineOnce, hc, hci]
      refine ⟨hj.1, ?_⟩
      apply SimpleGraph.Adj.reachable
      rw [G.supportGraph_adj_iff
        (G.insideEdges (colorClass χ i.castSucc) P (G.endAt e' 0))
        (G.endAt e' 0) (G.endAt e' 1)]
      exact ⟨G.loopless e', e',
        (mem_insideEdges (G := G)).mpr
          ⟨he'T, P.refl _, P.symm hj.1⟩,
        Or.inl ⟨rfl, rfl⟩⟩
    by_cases hcLast : c = Fin.last k
    · subst c
      have he'ReachErase :
          G.ReachableIn ((residualClass χ).erase e)
            (G.endAt e' 0) (G.endAt e' 1) :=
        G.reachableIn_erase_of_cyclic hsuper.1 he'Reach
      have hnotRoute :
          ¬ G.ReachableIn
            (G.insideEdges ((residualClass χ).erase e) P (G.endAt e' 0))
            (G.endAt e' 0) (G.endAt e' 1) := by
        intro hroute
        apply hj.2
        change (G.refineOnce χ P).r (G.endAt e' 0) (G.endAt e' 1)
        rw [refineOnce, hc]
        refine ⟨hj.1, ?_⟩
        apply G.reachableIn_mono _ hroute
        intro f hf
        have hf' := (mem_insideEdges (G := G)).mp hf
        apply (mem_insideEdges (G := G)).mpr
        exact ⟨Finset.mem_of_mem_erase hf'.1, hf'.2.1, hf'.2.2⟩
      apply he'ReachErase.elim_path
      intro q
      obtain ⟨f, hf, hfpath, hfCross⟩ :=
        G.exists_crossing_tree_edge_of_not_internal_reachable q hnotRoute
      obtain ⟨n, hn⟩ :=
        G.exists_finiteLevel_of_not_rel (χ := χ) (n := j) hfCross
      have hnj : n < j := by
        by_contra hnot
        have hjn : j ≤ n := Nat.le_of_not_gt hnot
        apply hfCross
        exact G.kaiserPartition_refines_of_le χ hjn hn.1
      have hn' : G.HasFiniteLevel χ' f n :=
        G.finiteLevel_of_partitions_eq_upto hEq hnj hn
      have hee' : e ≠ e' := by
        intro h
        subst e'
        have hlast : χ e = Fin.last k := mem_colorClass.mp hsuper.1.1
        have htree : χ e = i.castSucc := mem_colorClass.mp he'T
        exact (Fin.castSucc_ne_last i).symm (hlast.symm.trans htree)
      have hresClass :
          residualClass χ' = (residualClass χ).erase e ∪ {e'} :=
        residualClass_swap_of_residual_of_tree hsuper.1.1 he'T
      have he'NotRes : e' ∉ residualClass χ := by
        intro he'R
        exact (Finset.disjoint_left.mp
          (colorClass_disjoint χ (Fin.castSucc_ne_last i)) he'T he'R).elim
      have herase :
          (residualClass χ').erase e' = (residualClass χ).erase e := by
        rw [hresClass]
        ext g
        simp [hee'.symm, he'NotRes]
      have hq' :
          ∃ q' : (G.supportGraph ((residualClass χ').erase e')).Path
              (G.endAt e' 0) (G.endAt e' 1),
            G.symEdge f ∈ q'.1.edges := by
        rw [herase]
        exact ⟨q, hfpath⟩
      obtain ⟨q', hfpath'⟩ := hq'
      have hf' : f ∈ (residualClass χ').erase e' := by
        rw [herase]
        exact hf
      have hfCyc :
          G.IsCyclicEdge (residualClass χ') f :=
        G.cyclicEdge_of_mem_path_of_cyclic_edge he'Cyc q' hf' hfpath'
      have hnewSuper : G.IsSuperfluousAt χ' f n := ⟨hfCyc, hn'⟩
      have hle : G.minSuperfluousLevel χ' ≤ n :=
        G.minSuperfluousLevel_le ⟨f, hnewSuper⟩
      exact lt_of_le_of_lt hle (lt_trans hnj hjm)
    · have htreeClass :
          colorClass χ' i.castSucc =
            (colorClass χ i.castSucc).erase e' ∪ {e} := by
        have hχe : χ e = Fin.last k := mem_colorClass.mp hsuper.1.1
        have hχe' : χ e' = i.castSucc := mem_colorClass.mp he'T
        have hcol : χ e ≠ χ e' := by
          rw [hχe, hχe']
          exact (Fin.castSucc_ne_last i).symm
        have hee' : e ≠ e' := by
          intro h
          subst e'
          exact hcol rfl
        simpa [χ', hχe, hχe'] using colorClass_swap_right χ hee' hcol
      have hRefine : ∀ d : Fin (k + 1), d ≤ c →
          G.refineSetoid P (colorClass χ' d) =
            G.refineSetoid P (colorClass χ d) := by
        intro d hdc
        by_cases hdi : d = i.castSucc
        · subst d
          rw [htreeClass]
          have heRel :
              P.r (G.endAt e 0) (G.endAt e 1) :=
            G.kaiserPartition_refines_of_le χ (Nat.le_of_lt hjm)
              hsuper.2.1
          exact G.refineSetoid_exchange_eq_of_path_internal
            (hprefix i) he'T p he'path heRel hpath
        · by_cases hdlast : d = Fin.last k
          · subst d
            exfalso
            apply hcLast
            exact le_antisymm (Fin.le_last c) hdc
          · have hχe : χ e = Fin.last k := mem_colorClass.mp hsuper.1.1
            have hχe' : χ e' = i.castSucc := mem_colorClass.mp he'T
            have hcol : χ e ≠ χ e' := by
              rw [hχe, hχe']
              exact (Fin.castSucc_ne_last i).symm
            have hee' : e ≠ e' := by
              intro h
              subst e'
              exact hcol rfl
            have hdNeE : d ≠ χ e := by simpa [hχe] using hdlast
            have hdNeE' : d ≠ χ e' := by simpa [hχe'] using hdi
            rw [colorClass_swap_other χ hee' hdNeE hdNeE']
      have hbad : ¬ G.InternallyConnected (colorClass χ c) P :=
        G.firstDisconnectedColor_spec hc
      have hbad' : ¬ G.InternallyConnected (colorClass χ' c) P := by
        intro h
        apply hbad
        exact (G.internallyConnected_iff_of_refineSetoid_eq
          (hRefine c le_rfl)).mp h
      have hbefore' : ∀ d : Fin (k + 1), d < c →
          G.InternallyConnected (colorClass χ' d) P := by
        intro d hdc
        exact (G.internallyConnected_iff_of_refineSetoid_eq
          (hRefine d (le_of_lt hdc))).mpr
          (G.firstDisconnectedColor_internal_of_lt hc hdc)
      have hc' : G.firstDisconnectedColor χ' P = some c :=
        G.firstDisconnectedColor_eq_some_of_spec hbad' hbefore'
      have hnext :
          G.kaiserPartition χ' (j + 1) =
            G.kaiserPartition χ (j + 1) := by
        change G.refineOnce χ' (G.kaiserPartition χ' j) =
          G.refineOnce χ (G.kaiserPartition χ j)
        rw [hEq j le_rfl]
        change G.refineOnce χ' P = G.refineOnce χ P
        unfold refineOnce
        rw [hc', hc]
        exact hRefine c le_rfl
      have hj' : G.HasFiniteLevel χ' e' j := by
        constructor
        · rw [hEq j le_rfl]
          exact hj.1
        · rw [hnext]
          exact hj.2
      have hle : G.minSuperfluousLevel χ' ≤ j :=
        G.minSuperfluousLevel_le ⟨e', he'Cyc, hj'⟩
      exact lt_of_le_of_lt hle hjm

omit [DecidableEq V] in
/-- Kaiser's lexicographic extremal choice: an improvement step rules out a disconnected
residual class.  This is the finite-descent shell of the short proof. -/
theorem exists_connected_residual_of_kaiser_step [Nonempty V] {k : ℕ}
    (hex : ∃ χ : E → Fin (k + 1), G.PrefixTrees χ)
    (hstep : G.HasKaiserImprovementStep k) :
    ∃ χ : E → Fin (k + 1), G.PrefixTrees χ ∧ G.Connects (residualClass χ) := by
  classical
  let A : Finset (E → Fin (k + 1)) := Finset.univ.filter G.PrefixTrees
  have hA : A.Nonempty := by
    rcases hex with ⟨χ, hχ⟩
    exact ⟨χ, by simp [A, hχ]⟩
  obtain ⟨χ₀, hχ₀A, hχ₀min⟩ :=
    Finset.exists_min_image A G.residualComponents hA
  let B : Finset (E → Fin (k + 1)) :=
    A.filter fun χ ↦ G.residualComponents χ = G.residualComponents χ₀
  have hB : B.Nonempty := ⟨χ₀, by simp [B, hχ₀A]⟩
  obtain ⟨χ, hχB, hχmin⟩ :=
    Finset.exists_min_image B G.minSuperfluousLevel hB
  have hχA : χ ∈ A := (Finset.mem_filter.mp hχB).1
  have hprefix : G.PrefixTrees χ := by simpa [A] using hχA
  have hcompEq : G.residualComponents χ = G.residualComponents χ₀ := by
    exact (Finset.mem_filter.mp hχB).2
  by_cases hconn : G.Connects (residualClass χ)
  · exact ⟨χ, hprefix, hconn⟩
  · rcases hstep χ hprefix hconn with ⟨χ', hprefix', himprove | himprove⟩
    · have hχ'A : χ' ∈ A := by simp [A, hprefix']
      have hle := hχ₀min χ' hχ'A
      rw [← hcompEq] at hle
      exact False.elim (Nat.not_lt_of_ge hle himprove)
    · have hχ'A : χ' ∈ A := by simp [A, hprefix']
      have hχ'B : χ' ∈ B := by
        simp [B, hχ'A, himprove.1, hcompEq]
      have hle := hχmin χ' hχ'B
      exact False.elim (Nat.not_lt_of_ge hle himprove.2)

/-- Once Kaiser's improvement lemma is available, the induction on the number of colors
produces an actual packing.  The remaining theorem below is deliberately separated from the
long local exchange argument so that the latter can be audited independently. -/
theorem hasTreePacking_of_kaiser_steps [Nonempty V]
    (hstep : ∀ k : ℕ, G.HasKaiserImprovementStep k) :
    ∀ k : ℕ, G.HasTreePacking k := by
  intro k
  induction k with
  | zero =>
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i; exact Fin.elim0 i
      · intro i; exact Fin.elim0 i
  | succ k ih =>
      rcases ih with ⟨T, htrees, hdisj⟩
      let χ : E → Fin (k + 1) := coloringOfPacking T
      have hprefix : G.PrefixTrees χ := by
        intro i
        rw [show colorClass χ i.castSucc = T i by
          exact colorClass_coloringOfPacking hdisj i]
        exact htrees i
      obtain ⟨χ', hprefix', hconn⟩ :=
        G.exists_connected_residual_of_kaiser_step ⟨χ, hprefix⟩ (hstep k)
      obtain ⟨R, hRsub, hRtree⟩ :=
        G.exists_isSpanningTree_subset_of_connects (residualClass χ') hconn
      let U : Fin (k + 1) → Finset E :=
        Fin.lastCases R (fun i => colorClass χ' i.castSucc)
      refine ⟨U, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simpa [U] using hprefix' j
        · simpa [U] using hRtree
      · intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
          · simpa [U] using colorClass_disjoint χ' hij
          · apply Finset.disjoint_left.2
            intro e hea heR
            have hea' : e ∈ colorClass χ' a.castSucc := by simpa [U] using hea
            have heR' : e ∈ R := by simpa [U] using heR
            have heLast : e ∈ residualClass χ' := hRsub heR'
            exact (Finset.disjoint_left.mp
              (colorClass_disjoint χ' (Fin.castSucc_ne_last a)) hea' heLast).elim
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
          · apply Finset.disjoint_left.2
            intro e heR heb
            have heR' : e ∈ R := by simpa [U] using heR
            have heb' : e ∈ colorClass χ' b.castSucc := by simpa [U] using heb
            have heLast : e ∈ residualClass χ' := hRsub heR'
            exact (Finset.disjoint_left.mp
              (colorClass_disjoint χ' (Fin.castSucc_ne_last b)) heb' heLast).elim
          · exact (hij rfl).elim

/-- Sufficiency in the Nash-Williams--Tutte theorem, obtained by applying the
Kaiser improvement step at each inductive stage. -/
theorem hasTreePacking_of_condition [Nonempty V] :
    ∀ k : ℕ, G.SatisfiesTreePackingCondition k → G.HasTreePacking k := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ k ih =>
      intro hcond
      have hcondPrev : G.SatisfiesTreePackingCondition k :=
        G.satisfiesTreePackingCondition_mono (Nat.le_succ k) hcond
      rcases ih hcondPrev with ⟨T, htrees, hdisj⟩
      let χ : E → Fin (k + 1) := coloringOfPacking T
      have hprefix : G.PrefixTrees χ := by
        intro i
        rw [show colorClass χ i.castSucc = T i by
          exact colorClass_coloringOfPacking hdisj i]
        exact htrees i
      obtain ⟨χ', hprefix', hconn⟩ :=
        G.exists_connected_residual_of_kaiser_step ⟨χ, hprefix⟩
          (G.hasKaiserImprovementStep_of_condition hcond)
      obtain ⟨R, hRsub, hRtree⟩ :=
        G.exists_isSpanningTree_subset_of_connects (residualClass χ') hconn
      let U : Fin (k + 1) → Finset E :=
        Fin.lastCases R (fun i => colorClass χ' i.castSucc)
      refine ⟨U, ?_, ?_⟩
      · intro i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · simpa [U] using hprefix' j
        · simpa [U] using hRtree
      · intro i j hij
        rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
          · simpa [U] using colorClass_disjoint χ' hij
          · apply Finset.disjoint_left.2
            intro e hea heR
            have hea' : e ∈ colorClass χ' a.castSucc := by simpa [U] using hea
            have heR' : e ∈ R := by simpa [U] using heR
            have heLast : e ∈ residualClass χ' := hRsub heR'
            exact (Finset.disjoint_left.mp
              (colorClass_disjoint χ' (Fin.castSucc_ne_last a)) hea' heLast).elim
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
          · apply Finset.disjoint_left.2
            intro e heR heb
            have heR' : e ∈ R := by simpa [U] using heR
            have heb' : e ∈ colorClass χ' b.castSucc := by simpa [U] using heb
            have heLast : e ∈ residualClass χ' := hRsub heR'
            exact (Finset.disjoint_left.mp
              (colorClass_disjoint χ' (Fin.castSucc_ne_last b)) heb' heLast).elim
          · exact (hij rfl).elim

/-- Nash-Williams--Tutte spanning-tree packing theorem for finite loopless
multigraphs. -/
theorem nashWilliamsTutte [Nonempty V] (k : ℕ) :
    G.HasTreePacking k ↔ G.SatisfiesTreePackingCondition k := by
  constructor
  · exact G.satisfiesTreePackingCondition_of_hasTreePacking
  · exact G.hasTreePacking_of_condition k

end FiniteGraph

end CycleDoubleCover
