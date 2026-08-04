import Proofs.CycleDoubleCoverPort.NashWilliams2

/-
# Cycle Double Cover port, step 4 (part 3): the local-exchange layer

VENDORED FILE — adapted from upstream `openai/cdc-lean`.

Third slice of the port of upstream `CDCLean/NashWilliams.lean` (3,657 lines);
see #43629 for part 1 and `NashWilliams2.lean` for part 2. This part covers
upstream lines ~1348-2528: walk-transport lemmas for internal routes, the
fundamental-cycle exchange (`connects_exchange_of_path_edge` and the whole
`*_exchange_of_path_edge` family), the effect of a colour swap on the residual
class and its component count, and the extraction of a tree inside a single
partition class.

## Provenance, attribution and licensing — READ BEFORE RESTATING

Upstream: https://github.com/openai/cdc-lean, file `CDCLean/NashWilliams.lean`,
pinned at Lean `v4.31.0` / Mathlib `9a9483a92959bc92bd6a60176dd1fe597298c1f8`
— the same pin this repository uses. Original authorship is upstream's.

Unlike `NashWilliams.lean` (part 1) and `NashWilliams2.lean` (part 2), which are
independent re-derivations with no upstream text copied, **this file vendors
upstream proof scripts** (adapted only for our namespace `CycleDoubleCover`).

`openai/cdc-lean` carries **no license file**. That means default copyright —
all rights reserved. It is *not* public domain, and the absence of a license is
not a grant: publishing a repository does not waive copyright, and GitHub's ToS
grants only viewing and forking, not reproduction or adaptation. A permissive
licence was requested upstream on 2026-07-12 (openai/cdc-lean#4); there was no
response and the upstream issue tracker has since been disabled.

This file is vendored under the operator's explicit **risk acceptance** recorded
on #37507 (comment of 2026-08-03), which permits vendoring with attribution. It
is an accepted risk, not a determination that reuse is permitted. If upstream
ever objects, this file is the unit of removal.

## Ported in this part

`reachableIn_inside_of_walk_of_no_crossing`,
`exists_crossing_tree_edge_of_not_internal_reachable`,
`rel_of_reachableIn_inside`, `path_edge_ends_rel_start_of_no_crossing`,
`connects_exchange_of_path_edge`, `isSpanningTree_exchange_of_path_edge`,
`reachableIn_inside_exchange_of_path_edge_of_new_support`,
`reachableIn_inside_exchange_of_path_edge`, `reachableIn_exchange_of_path_edge`,
`cyclicEdge_of_mem_path_of_cyclic_edge`,
`reachableIn_inside_erase_of_min_superfluous`, `reachableIn_of_adj_reachable`,
`refineSetoid_residual_erase_eq_of_min_superfluous`,
`refineSetoid_union_singleton_eq_of_internal_reachable`,
`refineSetoid_exchange_eq_of_path_internal`, `prefixTrees_swap_of_path_edge`,
`reachableIn_union_singleton_iff_of_reachable`,
`reachableIn_erase_union_singleton_iff_of_cyclic_of_reachable`,
`connectedComponent_card_eq_of_reachable_iff`,
`residualComponents_eq_of_reachable_iff`,
`connectedComponent_card_lt_of_union_singleton_of_not_reachable`,
`residualClass_swap_of_residual_of_tree`,
`residualComponents_swap_eq_of_cyclic_of_reachable`,
`cyclicEdge_swap_of_cyclic_of_reachable`,
`residualComponents_swap_lt_of_cyclic_of_not_reachable`,
`not_reachable_residual_of_level_zero`, `reachable_residual_of_positive_level`,
`exists_internal_tree_subset`.

## Still deferred (later parts of step 4)

`crossingClass_card_eq_of_spanningTree_of_internal`,
`quotient_card_sub_one_le_crossingClass_card`,
`quotient_card_sub_one_le_crossingEdges_card`,
`satisfiesTreePackingCondition_of_hasTreePacking`,
`hasSuperfluousEdge_of_condition_of_disconnected`, the
`exists_*_level_tree_edge_*` family, `finiteLevelValue*`,
`kaiserPartition_eq_upto_of_min_exchange`, `HasSuperfluousLevel`,
`minSuperfluousLevel*`, `HasKaiserImprovementStep`,
`hasKaiserImprovementStep_of_condition`,
`exists_connected_residual_of_kaiser_step`, `hasTreePacking_of_kaiser_steps`,
`hasTreePacking_of_condition` and the headline `nashWilliamsTutte`.

There are no `sorry`s, no `native_decide`, and no `axiom` declarations here.
-/

namespace CycleDoubleCover

namespace FiniteGraph

open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

omit [DecidableEq V] [DecidableEq E] in
/-- If every genuine tree edge used by a support walk is internal to a partition,
then the walk gives an internal route in the multigraph. -/
theorem reachableIn_inside_of_walk_of_no_crossing
    {T : Finset E} {P : Setoid V} {a u v : V}
    (p : (G.supportGraph T).Walk u v) (hua : P.r u a)
    (hno : ∀ f ∈ T, G.symEdge f ∈ p.edges →
      P.r (G.endAt f 0) (G.endAt f 1)) :
    G.ReachableIn (G.insideEdges T P a) u v := by
  classical
  induction p generalizing a with
  | nil =>
      exact SimpleGraph.Reachable.refl _
  | @cons u w v hadj p ih =>
      rw [G.supportGraph_adj_iff T u w] at hadj
      rcases hadj with ⟨huwne, f, hfT, hends | hends⟩
      · have hsym : G.symEdge f = s(u, w) :=
          Sym2.eq_iff.mpr (Or.inl ⟨hends.1, hends.2⟩)
        have hfedge : G.symEdge f ∈ (SimpleGraph.Walk.cons
            (by
              rw [G.supportGraph_adj_iff T u w]
              exact ⟨huwne, f, hfT, Or.inl hends⟩) p).edges := by
          simp [hsym]
        have hfw := hno f hfT hfedge
        have huw : P.r u w := by simpa [hends.1, hends.2] using hfw
        have hwa : P.r w a := P.trans (P.symm huw) hua
        have hfInside : f ∈ G.insideEdges T P a := by
          apply (mem_insideEdges (G := G)).mpr
          exact ⟨hfT, by simpa [hends.1] using hua,
            by simpa [hends.2] using hwa⟩
        have hadjInside :
            (G.supportGraph (G.insideEdges T P a)).Adj u w := by
          rw [G.supportGraph_adj_iff (G.insideEdges T P a) u w]
          exact ⟨huwne, f, hfInside, Or.inl hends⟩
        have htail : ∀ g ∈ T, G.symEdge g ∈ p.edges →
            P.r (G.endAt g 0) (G.endAt g 1) := by
          intro g hgT hgedge
          apply hno g hgT
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
          exact Or.inr hgedge
        exact (SimpleGraph.Adj.reachable hadjInside).trans (ih hwa htail)
      · have hsym : G.symEdge f = s(u, w) :=
          Sym2.eq_iff.mpr (Or.inr ⟨hends.1, hends.2⟩)
        have hfedge : G.symEdge f ∈ (SimpleGraph.Walk.cons
            (by
              rw [G.supportGraph_adj_iff T u w]
              exact ⟨huwne, f, hfT, Or.inr hends⟩) p).edges := by
          simp [hsym]
        have hfw := hno f hfT hfedge
        have huw : P.r u w := by
          simpa [hends.1, hends.2] using P.symm hfw
        have hwa : P.r w a := P.trans (P.symm huw) hua
        have hfInside : f ∈ G.insideEdges T P a := by
          apply (mem_insideEdges (G := G)).mpr
          exact ⟨hfT, by simpa [hends.1] using hwa,
            by simpa [hends.2] using hua⟩
        have hadjInside :
            (G.supportGraph (G.insideEdges T P a)).Adj u w := by
          rw [G.supportGraph_adj_iff (G.insideEdges T P a) u w]
          exact ⟨huwne, f, hfInside, Or.inr hends⟩
        have htail : ∀ g ∈ T, G.symEdge g ∈ p.edges →
            P.r (G.endAt g 0) (G.endAt g 1) := by
          intro g hgT hgedge
          apply hno g hgT
          simp only [SimpleGraph.Walk.edges_cons, List.mem_cons]
          exact Or.inr hgedge
        exact (SimpleGraph.Adj.reachable hadjInside).trans (ih hwa htail)

omit [DecidableEq E] in
theorem exists_crossing_tree_edge_of_not_internal_reachable
    {T : Finset E} {P : Setoid V} {u v : V}
    (p : (G.supportGraph T).Walk u v)
    (hnot : ¬ G.ReachableIn (G.insideEdges T P u) u v) :
    ∃ f ∈ T, G.symEdge f ∈ p.edges ∧
      ¬ P.r (G.endAt f 0) (G.endAt f 1) := by
  classical
  by_contra hnone
  push Not at hnone
  apply hnot
  exact G.reachableIn_inside_of_walk_of_no_crossing p (P.refl u)
    (fun f hfT hfedge => hnone f hfT hfedge)

omit [DecidableEq V] [DecidableEq E] in
theorem rel_of_reachableIn_inside {S : Finset E} {P : Setoid V}
    {a u v : V} (hua : P.r u a)
    (h : G.ReachableIn (G.insideEdges S P a) u v) :
    P.r v a := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact hua
  | @cons x y z hxy p ih =>
      rw [G.supportGraph_adj_iff (G.insideEdges S P a) x y] at hxy
      rcases hxy with ⟨_, f, hf, hends | hends⟩
      · have hf' := (mem_insideEdges (G := G)).mp hf
        apply ih
        simpa [hends.2] using hf'.2.2
      · have hf' := (mem_insideEdges (G := G)).mp hf
        apply ih
        simpa [hends.1] using hf'.2.1

omit [DecidableEq E] in
/-- If every edge of a support walk is internal to P, then every genuine edge on
the walk has both ends in the class of the walk's first vertex. -/
theorem path_edge_ends_rel_start_of_no_crossing
    {T : Finset E} {P : Setoid V} {u v : V}
    (p : (G.supportGraph T).Walk u v)
    (hno : ∀ f ∈ T, G.symEdge f ∈ p.edges →
      P.r (G.endAt f 0) (G.endAt f 1))
    {f : E} (hfedge : G.symEdge f ∈ p.edges) :
    P.r (G.endAt f 0) u ∧ P.r (G.endAt f 1) u := by
  have h0supp : G.endAt f 0 ∈ p.support :=
    p.mem_support_of_mem_edges hfedge (by simp [symEdge])
  have h1supp : G.endAt f 1 ∈ p.support :=
    p.mem_support_of_mem_edges hfedge (by simp [symEdge])
  have hroute0 :
      G.ReachableIn (G.insideEdges T P u) u (G.endAt f 0) := by
    apply G.reachableIn_inside_of_walk_of_no_crossing
      (p.takeUntil (G.endAt f 0) h0supp) (P.refl u)
    intro g hgT hgedge
    apply hno g hgT
    exact p.edges_takeUntil_subset_edges h0supp hgedge
  have hroute1 :
      G.ReachableIn (G.insideEdges T P u) u (G.endAt f 1) := by
    apply G.reachableIn_inside_of_walk_of_no_crossing
      (p.takeUntil (G.endAt f 1) h1supp) (P.refl u)
    intro g hgT hgedge
    apply hno g hgT
    exact p.edges_takeUntil_subset_edges h1supp hgedge
  exact ⟨G.rel_of_reachableIn_inside (P.refl u) hroute0,
    G.rel_of_reachableIn_inside (P.refl u) hroute1⟩

/-- Removing an edge on the tree path between the ends of a new edge and adding the
new edge preserves connectedness.  This is the multiedge form of the fundamental
cycle exchange. -/
theorem connects_exchange_of_path_edge [Nonempty V]
    {T : Finset E} {e e' : E}
    (hT : G.IsSpanningTree T) (he' : e' ∈ T)
    (p : (G.supportGraph T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : G.symEdge e' ∈ p.1.edges) :
    G.Connects (T.erase e' ∪ {e}) := by
  classical
  let H := G.supportGraph T
  let z := G.symEdge e'
  let zs : Finset (Sym2 V) := {z}
  let D := H.deleteEdges (zs : Set (Sym2 V))
  let K := D ⊔ SimpleGraph.edge (G.endAt e 0) (G.endAt e 1)
  have hHtree : H.IsTree := by
    simpa [H] using G.supportGraph_isTree_of_spanningTree hT
  have hzH : z ∈ H.edgeFinset := by
    dsimp [H]
    rw [G.edgeFinset_supportGraph T]
    exact Finset.mem_image.mpr ⟨e', he', rfl⟩
  have hnreach :
      ¬ D.Reachable (G.endAt e 0) (G.endAt e 1) := by
    intro hreach
    apply hreach.elim_path
    intro q
    let qH : H.Path (G.endAt e 0) (G.endAt e 1) :=
      ⟨q.1.mapLe (SimpleGraph.deleteEdges_le _), q.2.mapLe _⟩
    have hEqWalk : qH.1 = p.1 :=
      (hHtree.existsUnique_path _ _).unique qH.2 p.2
    have hEq : qH = p := Subtype.ext hEqWalk
    have hzqH : z ∈ qH.1.edges := by
      rw [hEq]
      exact he'path
    have hzq : z ∈ q.1.edges := by
      simp [qH, SimpleGraph.Walk.edges_mapLe_eq_edges] at hzqH
      exact hzqH
    have hzD : z ∈ D.edgeSet := q.1.edges_subset_edgeSet hzq
    have hzD' : z ∈ H.edgeSet ∧ z ∉ (zs : Set (Sym2 V)) := by
      simpa [D, SimpleGraph.deleteEdges] using hzD
    exact hzD'.2 (by simp [zs])
  have hDacyc : D.IsAcyclic :=
    isAcyclic_of_le (V := V) (SimpleGraph.deleteEdges_le _) hHtree.isAcyclic
  have hKacyc : K.IsAcyclic := by
    exact hDacyc.sup_edge_of_not_reachable hnreach
  have hDcard : D.edgeFinset.card = H.edgeFinset.card - 1 := by
    have hDel :
        D.edgeFinset = H.edgeFinset \ zs := by
      simp [D, SimpleGraph.edgeFinset_deleteEdges]
    rw [hDel]
    have hzs : zs ⊆ H.edgeFinset := by
      simpa [zs] using hzH
    rw [Finset.card_sdiff_of_subset hzs]
    simp [zs]
  have hnotAdj : ¬ D.Adj (G.endAt e 0) (G.endAt e 1) := by
    intro h
    exact hnreach h.reachable
  have hKcard : K.edgeFinset.card = H.edgeFinset.card := by
    have hsup : K.edgeFinset.card = D.edgeFinset.card + 1 := by
      simpa [K] using
        (SimpleGraph.card_edgeFinset_sup_edge D hnotAdj (G.loopless e))
    rw [hsup, hDcard]
    have hpos : 0 < H.edgeFinset.card := Finset.card_pos.mpr ⟨z, hzH⟩
    omega
  obtain ⟨F, hKF, _, hFtree⟩ :=
    SimpleGraph.connected_top.exists_isTree_le_of_le_of_isAcyclic
      (H := K) le_top hKacyc
  have hKsubF : K.edgeFinset ⊆ F.edgeFinset :=
    SimpleGraph.edgeFinset_mono hKF
  have hcardEq : K.edgeFinset.card = F.edgeFinset.card := by
    have hHcard := hHtree.card_edgeFinset
    have hFcard := hFtree.card_edgeFinset
    omega
  have hEF : K.edgeFinset = F.edgeFinset :=
    Finset.eq_of_subset_of_card_le hKsubF (by omega)
  have hFK : F ≤ K := by
    rw [← SimpleGraph.edgeFinset_subset_edgeFinset]
    rw [← hEF]
  have hKconn : K.Connected := hFtree.connected.mono hFK
  have hDelSub : D ≤ G.supportGraph (T.erase e' ∪ {e}) := by
    intro x y hxy
    dsimp [D] at hxy
    rw [SimpleGraph.deleteEdges_adj] at hxy
    have hxyH := hxy.1
    have hnotz : s(x, y) ≠ z := by simpa [zs] using hxy.2
    change (G.supportGraph T).Adj x y at hxyH
    rw [G.supportGraph_adj_iff T x y] at hxyH
    rcases hxyH with ⟨hxyne, f, hfT, hends | hends⟩
    · have hsym : G.symEdge f = s(x, y) :=
        Sym2.eq_iff.mpr (Or.inl ⟨hends.1, hends.2⟩)
      have hfe' : f ≠ e' := by
        intro h
        subst f
        exact hnotz hsym.symm
      rw [G.supportGraph_adj_iff (T.erase e' ∪ {e}) x y]
      exact ⟨hxyne, f,
        Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hfe', hfT⟩)),
        Or.inl hends⟩
    · have hsym : G.symEdge f = s(x, y) :=
        Sym2.eq_iff.mpr (Or.inr ⟨hends.1, hends.2⟩)
      have hfe' : f ≠ e' := by
        intro h
        subst f
        exact hnotz hsym.symm
      rw [G.supportGraph_adj_iff (T.erase e' ∪ {e}) x y]
      exact ⟨hxyne, f,
        Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hfe', hfT⟩)),
        Or.inr hends⟩
  have hEdgeSub :
      SimpleGraph.edge (G.endAt e 0) (G.endAt e 1) ≤
        G.supportGraph (T.erase e' ∪ {e}) := by
    rw [SimpleGraph.edge_le_iff]
    right
    rw [G.supportGraph_adj_iff (T.erase e' ∪ {e}) (G.endAt e 0) (G.endAt e 1)]
    exact ⟨G.loopless e, e,
      Finset.mem_union.mpr (Or.inr (by simp)), Or.inl ⟨rfl, rfl⟩⟩
  have hKSub : K ≤ G.supportGraph (T.erase e' ∪ {e}) := by
    exact sup_le hDelSub hEdgeSub
  exact hKconn.mono hKSub

/-- The fundamental-cycle exchange preserves the spanning-tree cardinality as well as
connectedness. -/
theorem isSpanningTree_exchange_of_path_edge [Nonempty V]
    {T : Finset E} {e e' : E}
    (hT : G.IsSpanningTree T) (he : e ∉ T) (he' : e' ∈ T)
    (p : (G.supportGraph T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : G.symEdge e' ∈ p.1.edges) :
    G.IsSpanningTree (T.erase e' ∪ {e}) := by
  refine ⟨G.connects_exchange_of_path_edge hT he' p he'path, ?_⟩
  have hcardErase : (T.erase e').card = T.card - 1 := by
    simp [he']
  have heNotErase : e ∉ T.erase e' := by
    intro heT
    exact he (Finset.mem_of_mem_erase heT)
  rw [Finset.card_union_of_disjoint]
  · have hpos : 0 < T.card := Finset.card_pos.mpr ⟨e', he'⟩
    have hTcard := hT.2
    rw [Finset.card_singleton, hcardErase]
    omega
  · exact Finset.disjoint_singleton_right.mpr heNotErase

/-- When the new edge is genuinely new in the simple support of its fundamental
path, that cycle supplies an internal replacement route for the removed edge. -/
theorem reachableIn_inside_exchange_of_path_edge_of_new_support
    {T : Finset E} {P : Setoid V} {u : V} {e e' : E}
    (he' : e' ∈ T)
    (p : (G.supportGraph T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : G.symEdge e' ∈ p.1.edges)
    (hnew : G.symEdge e ∉ p.1.edges)
    (he0 : P.r (G.endAt e 0) u) (he1 : P.r (G.endAt e 1) u)
    (hpath : ∀ f ∈ T, G.symEdge f ∈ p.1.edges →
      P.r (G.endAt f 0) u ∧ P.r (G.endAt f 1) u) :
    G.ReachableIn
      (G.insideEdges (T.erase e' ∪ {e}) P u)
      (G.endAt e' 0) (G.endAt e' 1) := by
  classical
  let U := G.insideEdges (T ∪ {e}) P u
  have hpEdges : ∀ z ∈ p.1.edges, z ∈ (G.supportGraph U).edgeSet := by
    intro z hz
    have hzT : z ∈ (G.supportGraph T).edgeSet :=
      p.1.edges_subset_edgeSet hz
    obtain ⟨f, hfT, hfz⟩ :=
      G.exists_edge_of_mem_supportGraph_edgeSet T hzT
    have hfInt := hpath f hfT (hfz ▸ hz)
    have hfU : f ∈ U := by
      apply (mem_insideEdges (G := G)).mpr
      exact ⟨Finset.mem_union_left _ hfT, hfInt.1, hfInt.2⟩
    rw [← SimpleGraph.mem_edgeFinset]
    rw [G.edgeFinset_supportGraph U]
    exact Finset.mem_image.mpr ⟨f, hfU, hfz⟩
  let pU : (G.supportGraph U).Path (G.endAt e 0) (G.endAt e 1) :=
    ⟨p.1.transfer _ hpEdges, p.2.transfer _⟩
  have hpUEdges : pU.1.edges = p.1.edges := by
    simp [pU]
  have heU : e ∈ U := by
    apply (mem_insideEdges (G := G)).mpr
    exact ⟨Finset.mem_union_right _ (by simp), he0, he1⟩
  have heAdj :
      (G.supportGraph U).Adj (G.endAt e 0) (G.endAt e 1) := by
    rw [G.supportGraph_adj_iff U (G.endAt e 0) (G.endAt e 1)]
    exact ⟨G.loopless e, e, heU, Or.inl ⟨rfl, rfl⟩⟩
  let c : (G.supportGraph U).Walk (G.endAt e 1) (G.endAt e 1) :=
    pU.1.cons heAdj.symm
  have hc : c.IsCycle := by
    rw [SimpleGraph.Walk.cons_isCycle_iff]
    refine ⟨pU.2, ?_⟩
    simpa [hpUEdges, symEdge, Sym2.eq_swap] using hnew
  have hzcycle : G.symEdge e' ∈ c.edges := by
    simp [c, hpUEdges, he'path]
  have he'Int := hpath e' he' he'path
  have he'U : e' ∈ U := by
    apply (mem_insideEdges (G := G)).mpr
    exact ⟨Finset.mem_union_left _ he', he'Int.1, he'Int.2⟩
  have he'Adj :
      (G.supportGraph U).Adj (G.endAt e' 0) (G.endAt e' 1) := by
    rw [G.supportGraph_adj_iff U (G.endAt e' 0) (G.endAt e' 1)]
    exact ⟨G.loopless e', e', he'U, Or.inl ⟨rfl, rfl⟩⟩
  have hdelReach :
      ((G.supportGraph U).deleteEdges ({G.symEdge e'} : Set (Sym2 V))).Reachable
        (G.endAt e' 0) (G.endAt e' 1) := by
    have hcycle :=
      (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
        (G := G.supportGraph U) (v := G.endAt e' 0) (w := G.endAt e' 1)).2
        ⟨G.endAt e 1, c, hc, hzcycle⟩
    exact hcycle.2
  have hDelSub :
      (G.supportGraph U).deleteEdges ({G.symEdge e'} : Set (Sym2 V)) ≤
        G.supportGraph (G.insideEdges (T.erase e' ∪ {e}) P u) := by
    intro x y hxy
    rw [SimpleGraph.deleteEdges_adj] at hxy
    have hxyU := hxy.1
    have hnotz : s(x, y) ≠ G.symEdge e' := by simpa using hxy.2
    rw [G.supportGraph_adj_iff U x y] at hxyU
    rcases hxyU with ⟨hxyne, f, hfU, hends | hends⟩
    · have hfU' := (mem_insideEdges (G := G)).mp hfU
      rcases Finset.mem_union.mp hfU'.1 with hfT | hfE
      · have hsym : G.symEdge f = s(x, y) :=
          Sym2.eq_iff.mpr (Or.inl ⟨hends.1, hends.2⟩)
        have hfe' : f ≠ e' := by
          intro h
          subst f
          exact hnotz hsym.symm
        rw [G.supportGraph_adj_iff
          (G.insideEdges (T.erase e' ∪ {e}) P u) x y]
        exact ⟨hxyne, f,
          (mem_insideEdges (G := G)).mpr
            ⟨Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hfe', hfT⟩),
              hfU'.2.1, hfU'.2.2⟩,
          Or.inl hends⟩
      · have hfe : f = e := by simpa using hfE
        subst f
        rw [G.supportGraph_adj_iff
          (G.insideEdges (T.erase e' ∪ {e}) P u) x y]
        exact ⟨hxyne, e,
          (mem_insideEdges (G := G)).mpr
            ⟨Finset.mem_union_right _ (by simp), hfU'.2.1, hfU'.2.2⟩,
          Or.inl hends⟩
    · have hfU' := (mem_insideEdges (G := G)).mp hfU
      rcases Finset.mem_union.mp hfU'.1 with hfT | hfE
      · have hsym : G.symEdge f = s(x, y) :=
          Sym2.eq_iff.mpr (Or.inr ⟨hends.1, hends.2⟩)
        have hfe' : f ≠ e' := by
          intro h
          subst f
          exact hnotz hsym.symm
        rw [G.supportGraph_adj_iff
          (G.insideEdges (T.erase e' ∪ {e}) P u) x y]
        exact ⟨hxyne, f,
          (mem_insideEdges (G := G)).mpr
            ⟨Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hfe', hfT⟩),
              hfU'.2.1, hfU'.2.2⟩,
          Or.inr hends⟩
      · have hfe : f = e := by simpa using hfE
        subst f
        rw [G.supportGraph_adj_iff
          (G.insideEdges (T.erase e' ∪ {e}) P u) x y]
        exact ⟨hxyne, e,
          (mem_insideEdges (G := G)).mpr
            ⟨Finset.mem_union_right _ (by simp), hfU'.2.1, hfU'.2.2⟩,
          Or.inr hends⟩
  exact hdelReach.mono hDelSub

/-- The internal replacement route also covers the parallel-edge case, where the new
edge already has the simple support of the one-edge fundamental path. -/
theorem reachableIn_inside_exchange_of_path_edge [Nonempty V]
    {T : Finset E} {P : Setoid V} {u : V} {e e' : E}
    (hT : G.IsSpanningTree T) (he' : e' ∈ T)
    (p : (G.supportGraph T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : G.symEdge e' ∈ p.1.edges)
    (he0 : P.r (G.endAt e 0) u) (he1 : P.r (G.endAt e 1) u)
    (hpath : ∀ f ∈ T, G.symEdge f ∈ p.1.edges →
      P.r (G.endAt f 0) u ∧ P.r (G.endAt f 1) u) :
    G.ReachableIn
      (G.insideEdges (T.erase e' ∪ {e}) P u)
      (G.endAt e' 0) (G.endAt e' 1) := by
  by_cases hnew : G.symEdge e ∉ p.1.edges
  · exact G.reachableIn_inside_exchange_of_path_edge_of_new_support
      he' p he'path hnew he0 he1 hpath
  · push Not at hnew
    let H := G.supportGraph T
    have hHtree : H.IsTree := by
      simpa [H] using G.supportGraph_isTree_of_spanningTree hT
    have heEdge : G.symEdge e ∈ H.edgeSet :=
      p.1.edges_subset_edgeSet hnew
    have heAdj : H.Adj (G.endAt e 0) (G.endAt e 1) := by
      rw [← H.mem_edgeSet]
      simpa [H, symEdge] using heEdge
    let q : H.Path (G.endAt e 0) (G.endAt e 1) :=
      SimpleGraph.Path.singleton heAdj
    have hpq : p.1 = q.1 :=
      (hHtree.existsUnique_path _ _).unique p.2 q.2
    have hqEdges : q.1.edges = [G.symEdge e] := by
      simp [q, symEdge]
    have hsym : G.symEdge e' = G.symEdge e := by
      have : G.symEdge e' ∈ q.1.edges := by simpa [hpq] using he'path
      simpa [hqEdges] using this
    have hends :
        (G.endAt e 0 = G.endAt e' 0 ∧ G.endAt e 1 = G.endAt e' 1) ∨
          (G.endAt e 0 = G.endAt e' 1 ∧ G.endAt e 1 = G.endAt e' 0) := by
      simpa [symEdge] using (Sym2.eq_iff.mp hsym.symm)
    have heInside :
        e ∈ G.insideEdges (T.erase e' ∪ {e}) P u := by
      apply (mem_insideEdges (G := G)).mpr
      exact ⟨Finset.mem_union_right _ (by simp), he0, he1⟩
    apply SimpleGraph.Adj.reachable
    rw [G.supportGraph_adj_iff
      (G.insideEdges (T.erase e' ∪ {e}) P u)
      (G.endAt e' 0) (G.endAt e' 1)]
    refine ⟨G.loopless e', e, heInside, ?_⟩
    rcases hends with hends | hends
    · exact Or.inl ⟨hends.1, hends.2⟩
    · exact Or.inr ⟨hends.1, hends.2⟩

/-- A path plus a new edge gives a replacement route for any edge on the path.
This version does not assume that the old edge set is a tree. -/
theorem reachableIn_exchange_of_path_edge
    {T : Finset E} {e e' : E}
    (he' : e' ∈ T)
    (p : (G.supportGraph T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : G.symEdge e' ∈ p.1.edges) :
    G.ReachableIn (T.erase e' ∪ {e}) (G.endAt e' 0) (G.endAt e' 1) := by
  classical
  by_cases hnew : G.symEdge e ∉ p.1.edges
  · have hroute :=
      G.reachableIn_inside_exchange_of_path_edge_of_new_support
        (P := (⊤ : Setoid V)) (u := G.endAt e 0)
        he' p he'path hnew (by simp) (by simp)
        (by intro f hfT hfpath; exact ⟨by simp, by simp⟩)
    simpa [G.insideEdges_top] using hroute
  · push Not at hnew
    have hlen : p.1.length = 1 := by
      apply p.2.length_eq_one_of_mem_edges
      simpa [symEdge] using hnew
    have hpEdges : p.1.edges = [G.symEdge e] := by
      have hpEq := p.2.eq_adj_toWalk_of_mem_edges (by
        simpa [symEdge] using hnew)
      rw [hpEq]
      simp [symEdge]
    have hsym : G.symEdge e' = G.symEdge e := by
      simpa [hpEdges] using he'path
    have hends :
        (G.endAt e 0 = G.endAt e' 0 ∧ G.endAt e 1 = G.endAt e' 1) ∨
          (G.endAt e 0 = G.endAt e' 1 ∧ G.endAt e 1 = G.endAt e' 0) := by
      simpa [symEdge] using (Sym2.eq_iff.mp hsym.symm)
    apply SimpleGraph.Adj.reachable
    rw [G.supportGraph_adj_iff (T.erase e' ∪ {e})
      (G.endAt e' 0) (G.endAt e' 1)]
    refine ⟨G.loopless e', e, Finset.mem_union_right _ (by simp), ?_⟩
    rcases hends with hends | hends
    · exact Or.inl ⟨hends.1, hends.2⟩
    · exact Or.inr ⟨hends.1, hends.2⟩

/-- Every genuine edge on a path which, together with a cyclic edge, closes a
cycle is itself cyclic. -/
theorem cyclicEdge_of_mem_path_of_cyclic_edge
    {S : Finset E} {e f : E}
    (heCyc : G.IsCyclicEdge S e)
    (p : (G.supportGraph (S.erase e)).Path
      (G.endAt e 0) (G.endAt e 1))
    (hf : f ∈ S.erase e)
    (hfpath : G.symEdge f ∈ p.1.edges) :
    G.IsCyclicEdge S f := by
  have hroute :
      G.ReachableIn ((S.erase e).erase f ∪ {e})
        (G.endAt f 0) (G.endAt f 1) :=
    G.reachableIn_exchange_of_path_edge
      hf p hfpath
  have hsub : (S.erase e).erase f ∪ {e} ⊆ S.erase f := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · have hx' := Finset.mem_erase.mp hx
      exact Finset.mem_erase.mpr
        ⟨hx'.1, Finset.mem_of_mem_erase hx'.2⟩
    · have hxe : x = e := by simpa using hx
      subst x
      have hef : e ≠ f := by
        intro h
        subst f
        exact (Finset.mem_erase.mp hf).1 rfl
      exact Finset.mem_erase.mpr ⟨hef, heCyc.1⟩
  exact ⟨Finset.mem_of_mem_erase hf, G.reachableIn_mono hsub hroute⟩

/-- Below the minimum superfluous level, deleting the chosen residual cyclic
edge cannot disconnect any current partition class.  Otherwise an edge on the
escaping cycle route would be a lower-level superfluous edge. -/
theorem reachableIn_inside_erase_of_min_superfluous [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {m t : ℕ} {u v : V}
    (hsuper : G.IsSuperfluousAt χ e m)
    (hmin : ∀ f n, G.IsSuperfluousAt χ f n → m ≤ n)
    (htm : t < m)
    (h : G.ReachableIn
      (G.insideEdges (residualClass χ) (G.kaiserPartition χ t) u) u v) :
    G.ReachableIn
      (G.insideEdges ((residualClass χ).erase e)
        (G.kaiserPartition χ t) u) u v := by
  let P := G.kaiserPartition χ t
  by_cases heInside : e ∈ G.insideEdges (residualClass χ) P u
  · have heInside' := (mem_insideEdges (G := G)).mp heInside
    have heRoute :
        G.ReachableIn
          (G.insideEdges ((residualClass χ).erase e) P u)
          (G.endAt e 0) (G.endAt e 1) := by
      by_contra hnot
      have hnot' :
          ¬ G.ReachableIn
            (G.insideEdges ((residualClass χ).erase e) P (G.endAt e 0))
            (G.endAt e 0) (G.endAt e 1) := by
        intro hroute
        apply hnot
        rw [← G.insideEdges_eq_of_rel heInside'.2.1]
        exact hroute
      apply hsuper.1.2.elim_path
      intro p
      obtain ⟨f, hf, hfpath, hfCross⟩ :=
        G.exists_crossing_tree_edge_of_not_internal_reachable p hnot'
      have hfCyc :
          G.IsCyclicEdge (residualClass χ) f :=
        G.cyclicEdge_of_mem_path_of_cyclic_edge hsuper.1 p hf hfpath
      obtain ⟨n, hn⟩ :=
        G.exists_finiteLevel_of_not_rel (χ := χ) (n := t) hfCross
      have hnt : n < t := by
        by_contra hnotlt
        have htn : t ≤ n := Nat.le_of_not_gt hnotlt
        apply hfCross
        exact G.kaiserPartition_refines_of_le χ htn hn.1
      have hmn := hmin f n ⟨hfCyc, hn⟩
      omega
    have heCycInside :
        G.IsCyclicEdge
          (G.insideEdges (residualClass χ) P u) e := by
      refine ⟨heInside, ?_⟩
      rw [← G.insideEdges_erase]
      exact heRoute
    have h' := G.reachableIn_erase_of_cyclic heCycInside h
    rw [← G.insideEdges_erase] at h'
    exact h'
  · rw [G.insideEdges_erase, Finset.erase_eq_self.mpr heInside]
    exact h

omit [DecidableEq V] [DecidableEq E] in
/-- If every edge of T can already be traversed inside S, then every T-walk
can be traversed inside S. -/
theorem reachableIn_of_adj_reachable {S T : Finset E} {u v : V}
    (hstep : ∀ {x y : V}, (G.supportGraph T).Adj x y →
      G.ReachableIn S x y)
    (h : G.ReachableIn T u v) :
    G.ReachableIn S u v := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy p ih =>
      exact (hstep hxy).trans ih

theorem refineSetoid_residual_erase_eq_of_min_superfluous [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {m t : ℕ}
    (hsuper : G.IsSuperfluousAt χ e m)
    (hmin : ∀ f n, G.IsSuperfluousAt χ f n → m ≤ n)
    (htm : t < m) :
    G.refineSetoid (G.kaiserPartition χ t) ((residualClass χ).erase e) =
      G.refineSetoid (G.kaiserPartition χ t) (residualClass χ) := by
  apply Setoid.ext
  intro u v
  change ((G.kaiserPartition χ t).r u v ∧
      G.ReachableIn
        (G.insideEdges ((residualClass χ).erase e)
          (G.kaiserPartition χ t) u) u v) ↔
    ((G.kaiserPartition χ t).r u v ∧
      G.ReachableIn
        (G.insideEdges (residualClass χ)
          (G.kaiserPartition χ t) u) u v)
  constructor
  · rintro ⟨huv, h⟩
    have hsub :
        G.insideEdges ((residualClass χ).erase e)
            (G.kaiserPartition χ t) u ⊆
          G.insideEdges (residualClass χ)
            (G.kaiserPartition χ t) u := by
      intro f hf
      have hf' := (mem_insideEdges (G := G)).mp hf
      exact (mem_insideEdges (G := G)).mpr
        ⟨Finset.mem_of_mem_erase hf'.1, hf'.2.1, hf'.2.2⟩
    exact ⟨huv, G.reachableIn_mono hsub h⟩
  · rintro ⟨huv, h⟩
    exact ⟨huv, G.reachableIn_inside_erase_of_min_superfluous
      hsuper hmin htm h⟩

omit [DecidableEq V] in
/-- Adding an edge whose ends are already internally connected in their P-class
does not alter refinement by that edge set. -/
theorem refineSetoid_union_singleton_eq_of_internal_reachable
    {S : Finset E} {P : Setoid V} {e : E}
    (hreach :
      G.ReachableIn (G.insideEdges S P (G.endAt e 0))
        (G.endAt e 0) (G.endAt e 1)) :
    G.refineSetoid P (S ∪ {e}) = G.refineSetoid P S := by
  apply Setoid.ext
  intro u v
  change (P.r u v ∧ G.ReachableIn (G.insideEdges (S ∪ {e}) P u) u v) ↔
    (P.r u v ∧ G.ReachableIn (G.insideEdges S P u) u v)
  have hiff :
      G.ReachableIn (G.insideEdges (S ∪ {e}) P u) u v ↔
        G.ReachableIn (G.insideEdges S P u) u v := by
    constructor
    · apply G.reachableIn_of_adj_reachable
      intro x y hxy
      rw [G.supportGraph_adj_iff (G.insideEdges (S ∪ {e}) P u) x y] at hxy
      rcases hxy with ⟨hxyne, f, hf, hends | hends⟩
      · have hf' := (mem_insideEdges (G := G)).mp hf
        rcases Finset.mem_union.mp hf'.1 with hfS | hfE
        · apply SimpleGraph.Adj.reachable
          rw [G.supportGraph_adj_iff (G.insideEdges S P u) x y]
          exact ⟨hxyne, f,
            (mem_insideEdges (G := G)).mpr ⟨hfS, hf'.2.1, hf'.2.2⟩,
            Or.inl hends⟩
        · have hfe : f = e := by simpa using hfE
          subst f
          have hEq :=
            G.insideEdges_eq_of_rel (S := S) (P := P) hf'.2.1
          have hroute :
              G.ReachableIn (G.insideEdges S P u)
                (G.endAt e 0) (G.endAt e 1) := by
            rw [← hEq]
            exact hreach
          simpa [ReachableIn, hends.1, hends.2] using hroute
      · have hf' := (mem_insideEdges (G := G)).mp hf
        rcases Finset.mem_union.mp hf'.1 with hfS | hfE
        · apply SimpleGraph.Adj.reachable
          rw [G.supportGraph_adj_iff (G.insideEdges S P u) x y]
          exact ⟨hxyne, f,
            (mem_insideEdges (G := G)).mpr ⟨hfS, hf'.2.1, hf'.2.2⟩,
            Or.inr hends⟩
        · have hfe : f = e := by simpa using hfE
          subst f
          have hEq :=
            G.insideEdges_eq_of_rel (S := S) (P := P) hf'.2.1
          have hroute :
              G.ReachableIn (G.insideEdges S P u)
                (G.endAt e 0) (G.endAt e 1) := by
            rw [← hEq]
            exact hreach
          simpa [ReachableIn, hends.1, hends.2] using hroute.symm
    · intro h
      have hsub :
          G.insideEdges S P u ⊆ G.insideEdges (S ∪ {e}) P u := by
        intro f hf
        have hf' := (mem_insideEdges (G := G)).mp hf
        exact (mem_insideEdges (G := G)).mpr
          ⟨Finset.mem_union_left _ hf'.1, hf'.2.1, hf'.2.2⟩
      exact G.reachableIn_mono hsub h
  constructor
  · rintro ⟨huv, h⟩
    exact ⟨huv, hiff.mp h⟩
  · rintro ⟨huv, h⟩
    exact ⟨huv, hiff.mpr h⟩

/-- If the whole fundamental path lies in one P-class, exchanging along it does
not change the refinement made by that tree color. -/
theorem refineSetoid_exchange_eq_of_path_internal [Nonempty V]
    {T : Finset E} {P : Setoid V} {e e' : E}
    (hT : G.IsSpanningTree T) (he' : e' ∈ T)
    (p : (G.supportGraph T).Path (G.endAt e 0) (G.endAt e 1))
    (he'path : G.symEdge e' ∈ p.1.edges)
    (heRel : P.r (G.endAt e 0) (G.endAt e 1))
    (hpath : ∀ f ∈ T, G.symEdge f ∈ p.1.edges →
      P.r (G.endAt f 0) (G.endAt e 0) ∧
        P.r (G.endAt f 1) (G.endAt e 0)) :
    G.refineSetoid P (T.erase e' ∪ {e}) = G.refineSetoid P T := by
  apply Setoid.ext
  intro u v
  change (P.r u v ∧
      G.ReachableIn (G.insideEdges (T.erase e' ∪ {e}) P u) u v) ↔
    (P.r u v ∧ G.ReachableIn (G.insideEdges T P u) u v)
  have hreach :
      G.ReachableIn (G.insideEdges (T.erase e' ∪ {e}) P u) u v ↔
        G.ReachableIn (G.insideEdges T P u) u v := by
    constructor
    · apply G.reachableIn_of_adj_reachable
      intro x y hxy
      rw [G.supportGraph_adj_iff
        (G.insideEdges (T.erase e' ∪ {e}) P u) x y] at hxy
      rcases hxy with ⟨hxyne, f, hf, hends | hends⟩
      · have hf' := (mem_insideEdges (G := G)).mp hf
        rcases Finset.mem_union.mp hf'.1 with hfT | hfE
        · have hfT' : f ∈ T := Finset.mem_of_mem_erase hfT
          apply SimpleGraph.Adj.reachable
          rw [G.supportGraph_adj_iff (G.insideEdges T P u) x y]
          exact ⟨hxyne, f,
            (mem_insideEdges (G := G)).mpr ⟨hfT', hf'.2.1, hf'.2.2⟩,
            Or.inl hends⟩
        · have hfe : f = e := by simpa using hfE
          subst f
          have hno : ∀ g ∈ T, G.symEdge g ∈ p.1.edges →
              P.r (G.endAt g 0) (G.endAt g 1) := by
            intro g hgT hgpath
            have hg := hpath g hgT hgpath
            exact P.trans hg.1 (P.symm hg.2)
          have hroute :
              G.ReachableIn (G.insideEdges T P u)
                (G.endAt e 0) (G.endAt e 1) :=
            G.reachableIn_inside_of_walk_of_no_crossing p hf'.2.1 hno
          simpa [ReachableIn, hends.1, hends.2] using hroute
      · have hf' := (mem_insideEdges (G := G)).mp hf
        rcases Finset.mem_union.mp hf'.1 with hfT | hfE
        · have hfT' : f ∈ T := Finset.mem_of_mem_erase hfT
          apply SimpleGraph.Adj.reachable
          rw [G.supportGraph_adj_iff (G.insideEdges T P u) x y]
          exact ⟨hxyne, f,
            (mem_insideEdges (G := G)).mpr ⟨hfT', hf'.2.1, hf'.2.2⟩,
            Or.inr hends⟩
        · have hfe : f = e := by simpa using hfE
          subst f
          have hno : ∀ g ∈ T, G.symEdge g ∈ p.1.edges →
              P.r (G.endAt g 0) (G.endAt g 1) := by
            intro g hgT hgpath
            have hg := hpath g hgT hgpath
            exact P.trans hg.1 (P.symm hg.2)
          have hroute :
              G.ReachableIn (G.insideEdges T P u)
                (G.endAt e 0) (G.endAt e 1) :=
            G.reachableIn_inside_of_walk_of_no_crossing p hf'.2.1 hno
          simpa [ReachableIn, hends.1, hends.2] using hroute.symm
    · apply G.reachableIn_of_adj_reachable
      intro x y hxy
      rw [G.supportGraph_adj_iff (G.insideEdges T P u) x y] at hxy
      rcases hxy with ⟨hxyne, f, hf, hends | hends⟩
      · have hf' := (mem_insideEdges (G := G)).mp hf
        by_cases hfe' : f = e'
        · subst f
          have he'Path := hpath e' he' he'path
          have he0u : P.r (G.endAt e 0) u :=
            P.trans (P.symm he'Path.1) hf'.2.1
          have he1u : P.r (G.endAt e 1) u :=
            P.trans (P.symm heRel) he0u
          have hpathU : ∀ g ∈ T, G.symEdge g ∈ p.1.edges →
              P.r (G.endAt g 0) u ∧ P.r (G.endAt g 1) u := by
            intro g hgT hgpath
            have hg := hpath g hgT hgpath
            exact ⟨P.trans hg.1 he0u, P.trans hg.2 he0u⟩
          have hroute :=
            G.reachableIn_inside_exchange_of_path_edge hT he' p he'path
              he0u he1u hpathU
          simpa [ReachableIn, hends.1, hends.2] using hroute
        · apply SimpleGraph.Adj.reachable
          rw [G.supportGraph_adj_iff
            (G.insideEdges (T.erase e' ∪ {e}) P u) x y]
          exact ⟨hxyne, f,
            (mem_insideEdges (G := G)).mpr
              ⟨Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hfe', hf'.1⟩),
                hf'.2.1, hf'.2.2⟩,
            Or.inl hends⟩
      · have hf' := (mem_insideEdges (G := G)).mp hf
        by_cases hfe' : f = e'
        · subst f
          have he'Path := hpath e' he' he'path
          have he0u : P.r (G.endAt e 0) u :=
            P.trans (P.symm he'Path.1) hf'.2.1
          have he1u : P.r (G.endAt e 1) u :=
            P.trans (P.symm heRel) he0u
          have hpathU : ∀ g ∈ T, G.symEdge g ∈ p.1.edges →
              P.r (G.endAt g 0) u ∧ P.r (G.endAt g 1) u := by
            intro g hgT hgpath
            have hg := hpath g hgT hgpath
            exact ⟨P.trans hg.1 he0u, P.trans hg.2 he0u⟩
          have hroute :=
            G.reachableIn_inside_exchange_of_path_edge hT he' p he'path
              he0u he1u hpathU
          simpa [ReachableIn, hends.1, hends.2] using hroute.symm
        · apply SimpleGraph.Adj.reachable
          rw [G.supportGraph_adj_iff
            (G.insideEdges (T.erase e' ∪ {e}) P u) x y]
          exact ⟨hxyne, f,
            (mem_insideEdges (G := G)).mpr
              ⟨Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hfe', hf'.1⟩),
                hf'.2.1, hf'.2.2⟩,
            Or.inr hends⟩
  constructor
  · rintro ⟨huv, h⟩
    exact ⟨huv, hreach.mp h⟩
  · rintro ⟨huv, h⟩
    exact ⟨huv, hreach.mpr h⟩

/-- Recoloring a residual edge with the color of a tree edge preserves all prefix
trees when the tree edge lies on the fundamental path of the residual edge. -/
theorem prefixTrees_swap_of_path_edge [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {i : Fin k} {e e' : E}
    (hprefix : G.PrefixTrees χ)
    (heRes : e ∈ residualClass χ)
    (he'T : e' ∈ colorClass χ i.castSucc)
    (p : (G.supportGraph (colorClass χ i.castSucc)).Path
      (G.endAt e 0) (G.endAt e 1))
    (he'path : G.symEdge e' ∈ p.1.edges) :
    G.PrefixTrees (swapColor χ e e') := by
  have hχe : χ e = Fin.last k := by
    exact mem_colorClass.mp heRes
  have hχe' : χ e' = i.castSucc := mem_colorClass.mp he'T
  have hcol : χ e ≠ χ e' := by
    rw [hχe, hχe']
    exact (Fin.castSucc_ne_last i).symm
  have hee' : e ≠ e' := by
    intro h
    subst e'
    exact hcol rfl
  intro a
  by_cases hai : a = i
  · subst a
    rw [show colorClass (swapColor χ e e') i.castSucc =
        (colorClass χ i.castSucc).erase e' ∪ {e} by
      simpa [hχe, hχe'] using colorClass_swap_right χ hee' hcol]
    apply G.isSpanningTree_exchange_of_path_edge
      (hprefix i) _ he'T p he'path
    intro heT
    exact (Finset.disjoint_left.mp
      (colorClass_disjoint χ (Fin.castSucc_ne_last i))
      heT heRes).elim
  · have hneLast : a.castSucc ≠ χ e := by
      rw [hχe]
      exact Fin.castSucc_ne_last a
    have hneTree : a.castSucc ≠ χ e' := by
      rw [hχe']
      exact fun h => hai (Fin.castSucc_injective _ h)
    rw [colorClass_swap_other χ hee' hneLast hneTree]
    exact hprefix a

omit [DecidableEq V] in
/-- Adding an edge whose ends were already connected does not change the component
partition. -/
theorem reachableIn_union_singleton_iff_of_reachable {S : Finset E} {e : E}
    (he : G.ReachableIn S (G.endAt e 0) (G.endAt e 1))
    (u v : V) :
    G.ReachableIn (S ∪ {e}) u v ↔ G.ReachableIn S u v := by
  constructor
  · apply G.reachableIn_of_adj_reachable
    intro x y hxy
    rw [G.supportGraph_adj_iff (S ∪ {e}) x y] at hxy
    rcases hxy with ⟨hxyne, f, hf, hends | hends⟩
    · rcases Finset.mem_union.mp hf with hfS | hfE
      · exact SimpleGraph.Adj.reachable <| by
          rw [G.supportGraph_adj_iff S x y]
          exact ⟨hxyne, f, hfS, Or.inl hends⟩
      · have hfe : f = e := by simpa using hfE
        subst f
        simpa [ReachableIn, hends.1, hends.2] using he
    · rcases Finset.mem_union.mp hf with hfS | hfE
      · exact SimpleGraph.Adj.reachable <| by
          rw [G.supportGraph_adj_iff S x y]
          exact ⟨hxyne, f, hfS, Or.inr hends⟩
      · have hfe : f = e := by simpa using hfE
        subst f
        have hrev := he.symm
        simpa [ReachableIn, hends.1, hends.2] using hrev
  · intro h
    exact h.mono (G.supportGraph_mono (by intro f hf; exact Finset.mem_union_left _ hf))

omit [DecidableEq V] in
/-- Deleting a cyclic edge and then adding an edge internal to the old components
leaves all reachability relations unchanged. -/
theorem reachableIn_erase_union_singleton_iff_of_cyclic_of_reachable
    {S : Finset E} {e f : E}
    (he : G.IsCyclicEdge S e)
    (hf : G.ReachableIn S (G.endAt f 0) (G.endAt f 1))
    (u v : V) :
    G.ReachableIn (S.erase e ∪ {f}) u v ↔ G.ReachableIn S u v := by
  have hf' : G.ReachableIn (S.erase e) (G.endAt f 0) (G.endAt f 1) :=
    G.reachableIn_erase_of_cyclic he hf
  rw [G.reachableIn_union_singleton_iff_of_reachable hf']
  constructor
  · intro h
    exact h.mono (G.supportGraph_mono (Finset.erase_subset _ _))
  · exact G.reachableIn_erase_of_cyclic he

omit [DecidableEq V] [DecidableEq E] in
/-- Pointwise equality of reachability gives equality of connected-component
cardinalities for arbitrary edge sets. -/
theorem connectedComponent_card_eq_of_reachable_iff
    {S T : Finset E}
    (h : ∀ u v : V, G.ReachableIn S u v ↔ G.ReachableIn T u v) :
    Nat.card (G.supportGraph S).ConnectedComponent =
      Nat.card (G.supportGraph T).ConnectedComponent := by
  let e :
      Quotient (G.supportGraph S).reachableSetoid ≃
        Quotient (G.supportGraph T).reachableSetoid :=
    Quotient.congr (Equiv.refl V) (by
      intro u v
      change (G.supportGraph S).Reachable u v ↔
        (G.supportGraph T).Reachable u v
      exact h u v)
  exact Nat.card_congr e

omit [DecidableEq V] [DecidableEq E] in
/-- Pointwise equality of reachability gives equality of the numbers of connected
components. -/
theorem residualComponents_eq_of_reachable_iff {k : ℕ}
    {χ χ' : E → Fin (k + 1)}
    (h : ∀ u v : V,
      G.ReachableIn (residualClass χ') u v ↔
        G.ReachableIn (residualClass χ) u v) :
    G.residualComponents χ' = G.residualComponents χ := by
  change Nat.card (G.supportGraph (residualClass χ')).ConnectedComponent =
    Nat.card (G.supportGraph (residualClass χ)).ConnectedComponent
  exact G.connectedComponent_card_eq_of_reachable_iff h

omit [DecidableEq V] in
/-- Adding an edge between two distinct components strictly decreases the number of
components. -/
theorem connectedComponent_card_lt_of_union_singleton_of_not_reachable
    {S : Finset E} {e : E}
    (hnot : ¬ G.ReachableIn S (G.endAt e 0) (G.endAt e 1)) :
    Nat.card (G.supportGraph (S ∪ {e})).ConnectedComponent <
      Nat.card (G.supportGraph S).ConnectedComponent := by
  let H := G.supportGraph S
  let H' := G.supportGraph (S ∪ {e})
  have hle : H ≤ H' := by
    exact G.supportGraph_mono (by
      intro f hf
      exact Finset.mem_union_left _ hf)
  let f : H.ConnectedComponent → H'.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hle)
  have hsurj : Function.Surjective f :=
    SimpleGraph.ConnectedComponent.surjective_map_ofLE hle
  have hlecard :
      Nat.card H'.ConnectedComponent ≤ Nat.card H.ConnectedComponent :=
    Nat.card_le_card_of_surjective f hsurj
  apply lt_of_le_of_ne hlecard
  intro hEq
  have hbij : Function.Bijective f := by
    apply (Nat.bijective_iff_surjective_and_card f).2
    exact ⟨hsurj, hEq.symm⟩
  have hsame :
      H'.connectedComponentMk (G.endAt e 0) =
        H'.connectedComponentMk (G.endAt e 1) := by
    apply SimpleGraph.ConnectedComponent.sound
    apply SimpleGraph.Adj.reachable
    dsimp [H']
    rw [G.supportGraph_adj_iff (S ∪ {e}) (G.endAt e 0) (G.endAt e 1)]
    exact ⟨G.loopless e, e, Finset.mem_union_right _ (by simp),
      Or.inl ⟨rfl, rfl⟩⟩
  have hmap :
      f (H.connectedComponentMk (G.endAt e 0)) =
        f (H.connectedComponentMk (G.endAt e 1)) := by
    simpa [f] using hsame
  have hold :
      H.connectedComponentMk (G.endAt e 0) =
        H.connectedComponentMk (G.endAt e 1) :=
    hbij.1 hmap
  apply hnot
  exact SimpleGraph.ConnectedComponent.exact hold

theorem residualClass_swap_of_residual_of_tree {k : ℕ}
    {χ : E → Fin (k + 1)} {i : Fin k} {e e' : E}
    (heRes : e ∈ residualClass χ)
    (he'T : e' ∈ colorClass χ i.castSucc) :
    residualClass (swapColor χ e e') =
      (residualClass χ).erase e ∪ {e'} := by
  have hχe : χ e = Fin.last k := mem_colorClass.mp heRes
  have hχe' : χ e' = i.castSucc := mem_colorClass.mp he'T
  have hcol : χ e ≠ χ e' := by
    rw [hχe, hχe']
    exact (Fin.castSucc_ne_last i).symm
  have hee' : e ≠ e' := by
    intro h
    subst e'
    exact hcol rfl
  simpa [residualClass, hχe] using
    (colorClass_swap_left χ hee' hcol)

omit [DecidableEq V] in
theorem residualComponents_swap_eq_of_cyclic_of_reachable {k : ℕ}
    {χ : E → Fin (k + 1)} {i : Fin k} {e e' : E}
    (heRes : e ∈ residualClass χ)
    (he'T : e' ∈ colorClass χ i.castSucc)
    (heCyc : G.IsCyclicEdge (residualClass χ) e)
    (he'Reach :
      G.ReachableIn (residualClass χ) (G.endAt e' 0) (G.endAt e' 1)) :
    G.residualComponents (swapColor χ e e') =
      G.residualComponents χ := by
  apply G.residualComponents_eq_of_reachable_iff
  intro u v
  rw [residualClass_swap_of_residual_of_tree heRes he'T]
  exact G.reachableIn_erase_union_singleton_iff_of_cyclic_of_reachable
    heCyc he'Reach u v

omit [DecidableEq V] in
/-- In the unchanged-component case, the tree edge moved to the residual color is
itself cyclic: after deleting it, the old residual graph with the old cyclic edge
deleted remains. -/
theorem cyclicEdge_swap_of_cyclic_of_reachable {k : ℕ}
    {χ : E → Fin (k + 1)} {i : Fin k} {e e' : E}
    (heRes : e ∈ residualClass χ)
    (he'T : e' ∈ colorClass χ i.castSucc)
    (heCyc : G.IsCyclicEdge (residualClass χ) e)
    (he'Reach :
      G.ReachableIn (residualClass χ) (G.endAt e' 0) (G.endAt e' 1)) :
    G.IsCyclicEdge (residualClass (swapColor χ e e')) e' := by
  have hχe : χ e = Fin.last k := mem_colorClass.mp heRes
  have hχe' : χ e' = i.castSucc := mem_colorClass.mp he'T
  have hee' : e ≠ e' := by
    intro h
    subst e'
    have : Fin.last k = i.castSucc := hχe.symm.trans hχe'
    exact (Fin.castSucc_ne_last i).symm this
  have he'NotRes : e' ∉ residualClass χ := by
    intro he'R
    exact (Finset.disjoint_left.mp
      (colorClass_disjoint χ (Fin.castSucc_ne_last i)) he'T he'R).elim
  rw [residualClass_swap_of_residual_of_tree heRes he'T]
  constructor
  · simp
  · have herase :
        (((residualClass χ).erase e ∪ {e'}).erase e') =
          (residualClass χ).erase e := by
        ext f
        simp [hee'.symm, he'NotRes]
    rw [herase]
    exact G.reachableIn_erase_of_cyclic heCyc he'Reach

omit [DecidableEq V] in
theorem residualComponents_swap_lt_of_cyclic_of_not_reachable {k : ℕ}
    {χ : E → Fin (k + 1)} {i : Fin k} {e e' : E}
    (heRes : e ∈ residualClass χ)
    (he'T : e' ∈ colorClass χ i.castSucc)
    (heCyc : G.IsCyclicEdge (residualClass χ) e)
    (he'NotReach :
      ¬ G.ReachableIn (residualClass χ) (G.endAt e' 0) (G.endAt e' 1)) :
    G.residualComponents (swapColor χ e e') <
      G.residualComponents χ := by
  have hnotErase :
      ¬ G.ReachableIn ((residualClass χ).erase e)
        (G.endAt e' 0) (G.endAt e' 1) := by
    intro h
    apply he'NotReach
    exact h.mono (G.supportGraph_mono (Finset.erase_subset _ _))
  have hlt :=
    G.connectedComponent_card_lt_of_union_singleton_of_not_reachable hnotErase
  have hEraseEq :
      Nat.card (G.supportGraph ((residualClass χ).erase e)).ConnectedComponent =
        Nat.card (G.supportGraph (residualClass χ)).ConnectedComponent := by
    apply G.connectedComponent_card_eq_of_reachable_iff
    intro u v
    constructor
    · intro h
      exact h.mono (G.supportGraph_mono (Finset.erase_subset _ _))
    · exact G.reachableIn_erase_of_cyclic heCyc
  change Nat.card
      (G.supportGraph (residualClass (swapColor χ e e'))).ConnectedComponent <
    Nat.card (G.supportGraph (residualClass χ)).ConnectedComponent
  rw [residualClass_swap_of_residual_of_tree heRes he'T]
  exact hlt.trans_le hEraseEq.le

omit [DecidableEq V] [DecidableEq E] in
/-- Level zero means that the endpoints lie in different residual components. -/
theorem not_reachable_residual_of_level_zero [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E}
    (hprefix : G.PrefixTrees χ)
    (hdisc : ¬ G.Connects (residualClass χ))
    (hlev : G.HasFiniteLevel χ e 0) :
    ¬ G.ReachableIn (residualClass χ) (G.endAt e 0) (G.endAt e 1) := by
  have hP1 := G.first_partition_is_residual_components χ hprefix hdisc
  intro hreach
  apply hlev.2
  rw [hP1]
  change (⊤ : Setoid V).r (G.endAt e 0) (G.endAt e 1) ∧
    G.ReachableIn (G.insideEdges (residualClass χ) ⊤ (G.endAt e 0))
      (G.endAt e 0) (G.endAt e 1)
  refine ⟨by simp, ?_⟩
  rw [G.insideEdges_top]
  exact hreach

omit [DecidableEq V] [DecidableEq E] in
/-- Every positive-level edge has both ends in one residual component. -/
theorem reachable_residual_of_positive_level [Nonempty V] {k : ℕ}
    {χ : E → Fin (k + 1)} {e : E} {j : ℕ}
    (hprefix : G.PrefixTrees χ)
    (hdisc : ¬ G.Connects (residualClass χ))
    (hj : 0 < j)
    (hlev : G.HasFiniteLevel χ e j) :
    G.ReachableIn (residualClass χ) (G.endAt e 0) (G.endAt e 1) := by
  have hP1 := G.first_partition_is_residual_components χ hprefix hdisc
  have hrel1 :
      (G.kaiserPartition χ 1).r (G.endAt e 0) (G.endAt e 1) :=
    G.kaiserPartition_refines_of_le χ (Nat.succ_le_iff.mpr hj) hlev.1
  rw [hP1] at hrel1
  simpa [G.insideEdges_top] using hrel1.2

omit [DecidableEq V] in
/-- If S is connected inside the P-class of u, then its internal edge objects
contain a tree on that class.  The proof takes a simple tree in the induced support
graph and then chooses one genuine multiedge above each of its edges. -/
theorem exists_internal_tree_subset [Nonempty V] (S : Finset E) (P : Setoid V) (u : V)
    (hS : G.InternallyConnected S P) :
    ∃ T : Finset E,
      T ⊆ G.insideEdges S P u ∧
        T.card + 1 = Nat.card {v : V // P.r v u} := by
  classical
  let s : Set V := {v | P.r v u}
  let H₀ : SimpleGraph V := G.supportGraph (G.insideEdges S P u)
  let Hᵢ : SimpleGraph s := H₀.induce s
  letI : Nonempty s := ⟨⟨u, P.refl u⟩⟩
  have hconn : Hᵢ.Connected := by
    simpa [Hᵢ, H₀, s] using G.inside_induce_connected S P u hS
  obtain ⟨H, hHHᵢ, hHtree⟩ := hconn.exists_isTree_le
  letI : Fintype H.edgeSet := Fintype.ofFinite _
  have hpre : ∀ z : H.edgeFinset,
      ∃ e ∈ G.insideEdges S P u,
        G.symEdge e = Sym2.map (fun v : s => v.1) z.1 := by
    intro z
    rcases z with ⟨z, hz⟩
    induction z using Sym2.inductionOn with
    | _ a b =>
        have hab : H.Adj a b := by
          rw [← H.mem_edgeSet, ← SimpleGraph.mem_edgeFinset]
          exact hz
        have habᵢ : Hᵢ.Adj a b := hHHᵢ hab
        change H₀.Adj a.1 b.1 at habᵢ
        dsimp [H₀] at habᵢ
        rw [G.supportGraph_adj_iff (G.insideEdges S P u) a.1 b.1] at habᵢ
        rcases habᵢ with ⟨_, e, he, hends | hends⟩
        · refine ⟨e, he, ?_⟩
          simp only [symEdge, Sym2.map_mk]
          exact Sym2.eq_iff.mpr (Or.inl ⟨hends.1, hends.2⟩)
        · refine ⟨e, he, ?_⟩
          simp only [symEdge, Sym2.map_mk]
          exact Sym2.eq_iff.mpr (Or.inr ⟨hends.1, hends.2⟩)
  choose f hfS hfEq using hpre
  let T : Finset E := Finset.univ.image f
  have hTS : T ⊆ G.insideEdges S P u := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨z, _, rfl⟩
    exact hfS z
  have hmapinj :
      Function.Injective (Sym2.map (fun v : s => v.1)) := by
    exact (Function.Embedding.subtype (fun v : V => v ∈ s)).sym2Map.injective
  have hfinj : Function.Injective f := by
    intro z w hzw
    apply Subtype.ext
    apply hmapinj
    calc
      Sym2.map (fun v : s => v.1) z.1 = G.symEdge (f z) := (hfEq z).symm
      _ = G.symEdge (f w) := congrArg G.symEdge hzw
      _ = Sym2.map (fun v : s => v.1) w.1 := hfEq w
  have hcard : T.card = H.edgeFinset.card := by
    calc
      T.card = (Finset.univ : Finset H.edgeFinset).card := by
        exact Finset.card_image_of_injective _ hfinj
      _ = H.edgeFinset.card := by simp
  refine ⟨T, hTS, ?_⟩
  rw [hcard]
  change H.edgeFinset.card + 1 = Nat.card s
  rw [Nat.card_eq_fintype_card]
  exact hHtree.card_edgeFinset


end FiniteGraph

end CycleDoubleCover
