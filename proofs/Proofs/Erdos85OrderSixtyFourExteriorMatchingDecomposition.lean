import Proofs.Erdos85OrderSixtyFourHMatchingPairFamily
import Proofs.Erdos85OrderSixtyFourExteriorPairGraph

/-! # The exterior-pair graph is the union of six matchings -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The six small defect blocks do not merely supply six disjoint matchings
inside the exterior-pair graph: they exhaust it.  Thus the exterior relation
on H16 remembers its six-color perfect-matching decomposition. -/
theorem orderSixtyFour_seven_components_exteriorPair_iff_matching
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      ∃ μ : Fin 6 → Equiv.Perm c.supp,
        (∀ i, Function.Involutive (μ i)) ∧
        (∀ i u, μ i u ≠ u) ∧
        (∀ i j, i ≠ j → ∀ u, μ i u ≠ μ j u) ∧
        ∀ u v, (exteriorPairGraph G c.supp).Adj u v ↔
          ∃ i : Fin 6, μ i u = v := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, μ, hinvol, hfreePoint, hdisj, hpair⟩ :=
    orderSixtyFour_seven_defect_components_H_matchingPairFamily
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, _htwo, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  have hcc' : c = c' := by
    by_contra hne
    have hc8 := (hsmall c hne).1
    omega
  subst c'
  refine ⟨c, hc16, μ, hinvol, hfreePoint, hdisj, ?_⟩
  intro u v
  constructor
  · rintro ⟨huv, z, hzout, huz, hvz⟩
    have hec : D.connectedComponentMk z ≠ c := by
      intro heq
      apply hzout
      exact (ConnectedComponent.mem_supp_iff c z).mpr heq
    let e : {k : D.ConnectedComponent // k ≠ c} :=
      ⟨D.connectedComponentMk z, hec⟩
    obtain ⟨i, hi⟩ := κ.surjective e
    obtain ⟨x, hxset⟩ := hpair i u
    have hzmem : z ∈ componentNeighborFinset G D (κ i).1 u.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset u.1 z).mpr huz, ?_⟩
      change D.connectedComponentMk z = (κ i).1
      exact congrArg Subtype.val hi.symm
    have hxmem : x.1 ∈ componentNeighborFinset G D (κ i).1 u.1 := by
      apply Finset.mem_filter.mpr
      have hu : u.1 ∈ componentNeighborFinset G D c x.1 := by
        rw [hxset]
        simp
      refine ⟨(G.mem_neighborFinset u.1 x.1).mpr
        ((G.mem_neighborFinset x.1 u.1).mp (Finset.mem_filter.mp hu).1).symm, ?_⟩
      exact (ConnectedComponent.mem_supp_iff (κ i).1 x.1).mp x.2
    have hcard := (hsmall (κ i).1 (κ i).2).2 u.1
    change (componentNeighborFinset G D (κ i).1 u.1).card = 1 at hcard
    have hzx : z = x.1 := by
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      have hza : z = a := by simpa [ha] using hzmem
      have hxa : x.1 = a := by simpa [ha] using hxmem
      exact hza.trans hxa.symm
    have hvmem : v.1 ∈ componentNeighborFinset G D c x.1 := by
      apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset x.1 v.1).mpr ?_, ?_⟩
      · simpa [hzx] using hvz.symm
      · exact (ConnectedComponent.mem_supp_iff c v.1).mp v.2
    rw [hxset] at hvmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvmem
    refine ⟨i, ?_⟩
    rcases hvmem with hvu | hvmu
    · exact False.elim (huv (Subtype.ext hvu.symm))
    · exact Subtype.ext hvmu.symm
  · rintro ⟨i, rfl⟩
    obtain ⟨x, hxset⟩ := hpair i u
    have hxout : x.1 ∉ c.supp := by
      intro hxc
      have hxcomp : D.connectedComponentMk x.1 = c :=
        (ConnectedComponent.mem_supp_iff c x.1).mp hxc
      have hxblock : D.connectedComponentMk x.1 = (κ i).1 :=
        (ConnectedComponent.mem_supp_iff (κ i).1 x.1).mp x.2
      exact (κ i).2 (hxblock.symm.trans hxcomp)
    have hu : u.1 ∈ componentNeighborFinset G D c x.1 := by
      rw [hxset]
      simp
    have hmu : (μ i u).1 ∈ componentNeighborFinset G D c x.1 := by
      rw [hxset]
      simp
    exact ⟨(hfreePoint i u).symm, x.1, hxout,
      ((G.mem_neighborFinset x.1 u.1).mp (Finset.mem_filter.mp hu).1).symm,
      ((G.mem_neighborFinset x.1 (μ i u).1).mp
        (Finset.mem_filter.mp hmu).1).symm⟩

end

end Erdos85
