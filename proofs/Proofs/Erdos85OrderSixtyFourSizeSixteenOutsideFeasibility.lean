import Proofs.Erdos85OrderSixtyFourOutsideFeasibility

/-!
# Outside feasibility for any selected sixteen-component

The order-64 feasibility package chooses an existential H16 component,
whereas structural terminal reductions already carry a particular H16.
The seven-component partition makes H16 unique, so the package transports
to that particular component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every sixteen-vertex defect component in the seven-component branch has
the exact outside-pair data consumed by the checked owner certificates. -/
theorem orderSixtyFour_sizeSixteen_outsidePair_feasibility
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    (∀ x : Fin 64,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2) ∧
    Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c) ∧
    Fintype.card {x : Fin 64 // x ∉ c.supp} = 48 ∧
    (exteriorPairGraph G c).edgeSet.ncard = 48 := by
  classical
  obtain ⟨c₀, hc₀, _label, hqcard, hpaircard, hpairinc, _himage,
      _hRreg, hRedges, _hCreg, _hC4, _hcross⟩ :=
    orderSixtyFour_seven_components_outside_feasibility
      G hfree hmin hcover hcount
  obtain ⟨d, _hd, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have heq_of_16 : ∀ {a}, a.supp.ncard = 16 → a = d := by
    intro a ha
    by_contra hne
    have := hsmall a hne
    omega
  have hcc₀ : c = c₀ :=
    (heq_of_16 hc).trans (heq_of_16 hc₀).symm
  subst c₀
  refine ⟨hpaircard, hpairinc, hqcard, ?_⟩
  rw [Set.ncard_eq_toFinset_card']
  have hedgeFinsets :
      (exteriorPairGraph G c).edgeSet.toFinset =
        (exteriorPairGraph G c.supp).edgeFinset := by
    apply Finset.ext
    intro e
    simp only [Set.mem_toFinset, SimpleGraph.mem_edgeFinset]
    rfl
  rw [hedgeFinsets, hRedges]

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeSixteen_outsidePair_feasibility
