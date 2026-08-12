import Proofs.Erdos85ColorSectorPSD
import Proofs.Erdos85SecondOrderColorTrace

/-!
# The degree-six color-sector split

This file connects the component-indexed color sector used by the PSD
argument to the vertex-indexed colored order used by the cubic trace.  The
key point is that triangle-free defect degree two propagates along every
edge, hence throughout every connected component of the second-order defect
graph.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Triangle-free defect degree two propagates across a second-order defect
edge. -/
theorem triangleFree_degree_two_of_secondOrder_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {x y : V} (hxy : (secondOrderDefectGraph G).Adj x y)
    (hx : (triangleFreeEdgeGraph G).degree x = 2) :
    (triangleFreeEdgeGraph G).degree y = 2 := by
  have hxmono := secondOrder_defect_local_monochromatic
    G hfree hd heven hmin hcard x
  have hxyT : (triangleFreeEdgeGraph G).Adj x y := by
    rcases hxmono with hxmono | hxmono
    · have hyMem : y ∈ triangleFreeNeighbors G x := by
        have hDmem : y ∈ (secondOrderDefectGraph G).neighborFinset x :=
          ((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hxy
        rw [secondOrderDefectGraph_neighborFinset] at hDmem
        have hAempty : antipodalNeighbors G x = ∅ :=
          Finset.card_eq_zero.mp hxmono.1
        simpa [hAempty] using hDmem
      simpa [triangleFreeEdgeGraph_adj] using hyMem
    · have hxzero : (triangleFreeEdgeGraph G).degree x = 0 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_neighborFinset]
        exact hxmono.2
      omega
  rcases secondOrder_defect_local_monochromatic
      G hfree hd heven hmin hcard y with hymono | hymono
  · rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact hymono.2
  · have hzero : triangleFreeNeighbors G y = ∅ :=
      Finset.card_eq_zero.mp hymono.2
    have hmem : x ∈ triangleFreeNeighbors G y := by
      simpa [triangleFreeEdgeGraph_adj] using hxyT.symm
    rw [hzero] at hmem
    exact (Finset.notMem_empty x hmem).elim

/-- Triangle-free defect degree two is constant on every reachable class of
the second-order defect graph. -/
theorem triangleFree_degree_two_of_secondOrder_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {x y : V} (hxy : (secondOrderDefectGraph G).Reachable x y)
    (hx : (triangleFreeEdgeGraph G).degree x = 2) :
    (triangleFreeEdgeGraph G).degree y = 2 := by
  have hwalk : Relation.ReflTransGen (secondOrderDefectGraph G).Adj x y :=
    ((secondOrderDefectGraph G).reachable_iff_reflTransGen x y).mp hxy
  have hprop : ∀ {a b : V},
      Relation.ReflTransGen (secondOrderDefectGraph G).Adj a b →
      (triangleFreeEdgeGraph G).degree a = 2 →
      (triangleFreeEdgeGraph G).degree b = 2 := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hbc ih =>
        exact triangleFree_degree_two_of_secondOrder_adj
          G hfree hd heven hmin hcard hbc ih
  exact hprop hwalk hx

/-- A cyclic defect component belongs to the triangle-free color sector iff
one (and therefore every) vertex in it has triangle-free defect degree two. -/
theorem mem_triangleFreeCycleSector_iff_degree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    c ∈ triangleFreeCycleSector G u ↔
      (triangleFreeEdgeGraph G).degree (u c 0) = 2 := by
  constructor
  · intro hc
    have hG : G.Adj (u c 0) (u c 1) := by
      simpa using (mem_triangleFreeCycleSector_iff G u c).mp hc 0
    have hD : (secondOrderDefectGraph G).Adj (u c 0) (u c 1) := by
      rw [← (secondOrderDefectGraph G).mem_neighborFinset, huD]
      simp
    rcases secondOrder_defect_local_monochromatic
        G hfree hd heven hmin hcard (u c 0) with hmono | hmono
    · rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
        triangleFreeEdgeGraph_neighborFinset]
      exact hmono.2
    · have hm := secondOrderDefectGraph_incident_edges_monochromatic
        G hfree hd heven hmin hcard hD hD
      rcases hm with hm | hm
      · have hmem := (antipodalGraph_adj G (u c 0) (u c 1)).mp hm.1
        exact ((mem_antipodalNeighbors G (u c 0) (u c 1)).mp hmem).2.1 hG |>.elim
      · have hzero : triangleFreeNeighbors G (u c 0) = ∅ :=
          Finset.card_eq_zero.mp hmono.2
        have hmem : u c 1 ∈ triangleFreeNeighbors G (u c 0) := by
          simpa [triangleFreeEdgeGraph_adj] using hm.1
        rw [hzero] at hmem
        exact (Finset.notMem_empty _ hmem).elim
  · intro hzero
    rw [mem_triangleFreeCycleSector_iff]
    intro x
    have hcx : (secondOrderDefectGraph G).connectedComponentMk (u c x) = c := by
      apply (ConnectedComponent.mem_supp_iff c (u c x)).mp
      rw [← huRange c]
      exact ⟨x, rfl⟩
    have hc0mem : u c 0 ∈ c.supp := by
      have heq := congrArg (fun S : Set V => u c 0 ∈ S) (huRange c)
      exact heq.mp ⟨0, rfl⟩
    have hc0 : (secondOrderDefectGraph G).connectedComponentMk (u c 0) = c :=
      (ConnectedComponent.mem_supp_iff c (u c 0)).mp hc0mem
    have hreach : (secondOrderDefectGraph G).Reachable (u c 0) (u c x) :=
      ConnectedComponent.eq.mp (hc0.trans hcx.symm)
    have hxdeg := triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach hzero
    have hD : (secondOrderDefectGraph G).Adj (u c x) (u c (x + 1)) := by
      rw [← (secondOrderDefectGraph G).mem_neighborFinset, huD]
      simp
    rcases secondOrder_defect_local_monochromatic
        G hfree hd heven hmin hcard (u c x) with hmono | hmono
    · have hmem : u c (x + 1) ∈ triangleFreeNeighbors G (u c x) := by
        have hDmem : u c (x + 1) ∈
            (secondOrderDefectGraph G).neighborFinset (u c x) :=
          ((secondOrderDefectGraph G).mem_neighborFinset
            (u c x) (u c (x + 1))).mpr hD
        rw [secondOrderDefectGraph_neighborFinset] at hDmem
        have hAempty : antipodalNeighbors G (u c x) = ∅ :=
          Finset.card_eq_zero.mp hmono.1
        simpa [hAempty] using hDmem
      exact (mem_triangleFreeNeighbors G (u c x) (u c (x + 1))).mp hmem |>.1
    · have hxzero : (triangleFreeEdgeGraph G).degree (u c x) = 0 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
          triangleFreeEdgeGraph_neighborFinset]
        exact hmono.2
      omega

/-- The sector test may be made at any vertex of the component. -/
theorem mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (c : (secondOrderDefectGraph G).ConnectedComponent) {v : V}
    (hv : v ∈ c.supp) :
    c ∈ triangleFreeCycleSector G u ↔
      (triangleFreeEdgeGraph G).degree v = 2 := by
  have hvMk : (secondOrderDefectGraph G).connectedComponentMk v = c :=
    (ConnectedComponent.mem_supp_iff c v).mp hv
  have hu0mem : u c 0 ∈ c.supp := by
    have heq := congrArg (fun S : Set V => u c 0 ∈ S) (huRange c)
    exact heq.mp ⟨0, rfl⟩
  have hu0Mk : (secondOrderDefectGraph G).connectedComponentMk (u c 0) = c :=
    (ConnectedComponent.mem_supp_iff c (u c 0)).mp hu0mem
  have hreach : (secondOrderDefectGraph G).Reachable (u c 0) v :=
    ConnectedComponent.eq.mp (hu0Mk.trans hvMk.symm)
  constructor
  · intro hc
    apply triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach
    exact (mem_triangleFreeCycleSector_iff_degree_two
      G hfree hd heven hmin hcard u hu huRange huD c).mp hc
  · intro hvdeg
    apply (mem_triangleFreeCycleSector_iff_degree_two
      G hfree hd heven hmin hcard u hu huRange huD c).mpr
    exact triangleFree_degree_two_of_secondOrder_reachable
      G hfree hd heven hmin hcard hreach.symm hvdeg

/-- The vertex-colored order is exactly the sum of the orders of the
triangle-free cycle components. -/
theorem card_triangleFree_degree_two_eq_sum_sector_orders
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    (Finset.univ.filter fun v : V =>
        (triangleFreeEdgeGraph G).degree v = 2).card =
      ∑ c ∈ triangleFreeCycleSector G u, c.supp.ncard := by
  let S := triangleFreeCycleSector G u
  let U : Finset V := S.biUnion fun c => c.supp.toFinset
  have hsets : (Finset.univ.filter fun v : V =>
      (triangleFreeEdgeGraph G).degree v = 2) = U := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, U,
      Finset.mem_biUnion]
    constructor
    · intro hv
      let c := (secondOrderDefectGraph G).connectedComponentMk v
      have hvc : v ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
      refine ⟨c, ?_, Set.mem_toFinset.mpr hvc⟩
      exact (mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
        G hfree hd heven hmin hcard u hu huRange huD c hvc).mpr hv
    · rintro ⟨c, hc, hvc⟩
      exact (mem_triangleFreeCycleSector_iff_degree_two_of_mem_supp
        G hfree hd heven hmin hcard u hu huRange huD c
        (Set.mem_toFinset.mp hvc)).mp hc
  rw [hsets]
  dsimp [U]
  rw [Finset.card_biUnion]
  · simp [S, Set.ncard_eq_toFinset_card']
  · intro c _ e _ hce
    exact Set.disjoint_toFinset.mpr
      (pairwise_disjoint_supp_connectedComponent (secondOrderDefectGraph G) hce)

/-- At the degree-six exact boundary there are either no triangle-free defect
components or exactly one.  In the latter case its order is a positive
multiple of three (and, of course, at most the total order 33). -/
theorem degreeSix_triangleFreeCycleSector_empty_or_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 6 * (6 - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard) :
    triangleFreeCycleSector G u = ∅ ∨
      ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
        triangleFreeCycleSector G u = {c} ∧
        c.supp.ncard % 3 = 0 ∧ 3 ≤ c.supp.ncard ∧ c.supp.ncard ≤ 33 := by
  let S := triangleFreeCycleSector G u
  have hle : S.card ≤ 1 := degreeSix_triangleFreeCycleSector_card_le_one
    G hfree hmin hcard u hu huRange huD hr
  have hcases : S.card = 0 ∨ S.card = 1 := by omega
  rcases hcases with hzero | hone
  · left
    exact Finset.card_eq_zero.mp hzero
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hone
    right
    refine ⟨c, hc, ?_, hr c, ?_⟩
    · have hcount := card_triangleFree_degree_two_eq_sum_sector_orders
        G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard
        u hu huRange huD
      have hmod := degreeSix_secondOrder_colorOrder_mod_three
        G hfree hmin hcard
      rw [hcount] at hmod
      have hc' : triangleFreeCycleSector G u = {c} := hc
      simpa [hc'] using hmod
    · have hs : c.supp.ncard ≤ Fintype.card V := by
        simpa [Nat.card_eq_fintype_card] using c.supp.ncard_le_card
      norm_num at hcard
      omega

end

end Erdos85
