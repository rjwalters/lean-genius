import Proofs.Erdos85OrderSixtyFourHMatchingPairFamily
import Proofs.Erdos85OrderSixtyFourSixteenPairInjection

/-! # External matching pairs are disjoint from internal H16 pairs -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- None of the 48 pairs selected by the six small blocks is one of the
sixteen pairs selected by a vertex inside H16. -/
theorem orderSixtyFour_seven_defect_components_H_matching_internal_disjoint
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
      ∃ κ : Fin 6 ≃ {k // k ≠ c},
        ∃ μ : Fin 6 → Equiv.Perm c.supp,
          (∀ i, Function.Involutive (μ i)) ∧
          (∀ i u, μ i u ≠ u) ∧
          (∀ i j, i ≠ j → ∀ u, μ i u ≠ μ j u) ∧
          ∀ (i : Fin 6) (u y : c.supp),
            {u.1, (μ i u).1} ≠
              componentNeighborFinset G (secondOrderDefectGraph G) c y.1 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, μ, hinvol, hfreePoint, hdisj, hpair⟩ :=
    orderSixtyFour_seven_defect_components_H_matchingPairFamily
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, hinj'⟩ :=
    orderSixtyFour_seven_defect_components_sixteen_pair_injective
      G hfree hmin hcover hcount
  have hcc' : c = c' := by
    obtain ⟨d, hd16, hsmall⟩ :=
      orderSixtyFour_seven_defect_components_partition
        G hfree hmin hcover hcount
    have hcd : c = d := by
      by_contra hne
      have hc8 := hsmall c hne
      omega
    have hc'd : c' = d := by
      by_contra hne
      have hc'8 := hsmall c' hne
      omega
    exact hcd.trans hc'd.symm
  have hinj : Function.Injective (componentNeighborFinset G D c) := by
    rw [hcc']
    exact hinj'
  refine ⟨c, hc16, κ, μ, hinvol, hfreePoint, hdisj, ?_⟩
  intro i u y heq
  obtain ⟨x, hxpair⟩ := hpair i u
  have hxy : x.1 = y.1 := hinj (hxpair.trans heq)
  have hxcomp : D.connectedComponentMk x.1 = (κ i).1 :=
    (ConnectedComponent.mem_supp_iff (κ i).1 x.1).mp x.2
  have hycomp : D.connectedComponentMk y.1 = c :=
    (ConnectedComponent.mem_supp_iff c y.1).mp y.2
  exact (κ i).2 (by rw [← hxcomp, hxy, hycomp])

end

end Erdos85
