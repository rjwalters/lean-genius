import Proofs.Erdos85OrderSixtyFourNearTwinCollisionCrossCount

/-! # Cross-count pressure from three rainbow collision colors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The graph data produced by one propagated codegree-six collision in a
restricted owner factor.  This is precisely the input needed to exclude the
five-component cross profile when the owner differs from the source. -/
def OrderSixtyFourPropagatedOwnerCollision
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ x y p q : source.supp,
    x ≠ y ∧ p ≠ q ∧
    ¬ ((secondOrderDefectGraph G).induce source.supp).Adj x y ∧
    p ∈ ((secondOrderDefectGraph G).induce source.supp).neighborFinset x \
      ((secondOrderDefectGraph G).induce source.supp).neighborFinset y ∧
    (restrictedComponentOwnerGraph G source owner).neighborFinset x =
      (restrictedComponentOwnerGraph G source owner).neighborFinset y ∧
    (restrictedComponentOwnerGraph G source owner).neighborFinset p =
      (restrictedComponentOwnerGraph G source owner).neighborFinset q

/-- One propagated owner collision excludes five cross components for every
off-source owner color. -/
theorem orderSixtyFour_propagatedOwnerCollision_crossCount_ne_five
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    (hso : source ≠ owner)
    (hsource : source.supp.ncard = 16)
    (howner : owner.supp.ncard = 16)
    (hcollision : OrderSixtyFourPropagatedOwnerCollision G source owner) :
    Fintype.card
      (componentCrossBipartiteGraph G source owner).ConnectedComponent ≠ 5 := by
  obtain ⟨x, y, p, q, hxy, hpq, hxyNot, hp, hxyRows, hpqRows⟩ := hcollision
  exact orderSixtyFour_propagatedCollision_crossComponentCount_ne_five
    G hfree hreg source owner hso hsource howner x y p q
      hxy hpq hxyNot hp hxyRows hpqRows

/-- Among three pairwise-distinct rainbow collision colors, at most one can
be the source component.  Therefore at least two of the three corresponding
cross graphs exclude the five-component profile. -/
theorem orderSixtyFour_threeDistinctCollisions_two_crossCounts_ne_five
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (source α β γ : (secondOrderDefectGraph G).ConnectedComponent)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hsource : source.supp.ncard = 16)
    (hαsize : α.supp.ncard = 16)
    (hβsize : β.supp.ncard = 16)
    (hγsize : γ.supp.ncard = 16)
    (hα : OrderSixtyFourPropagatedOwnerCollision G source α)
    (hβ : OrderSixtyFourPropagatedOwnerCollision G source β)
    (hγ : OrderSixtyFourPropagatedOwnerCollision G source γ) :
    let crossCount := fun owner ↦ Fintype.card
      (componentCrossBipartiteGraph G source owner).ConnectedComponent
    (crossCount α ≠ 5 ∧ crossCount β ≠ 5) ∨
      (crossCount α ≠ 5 ∧ crossCount γ ≠ 5) ∨
      (crossCount β ≠ 5 ∧ crossCount γ ≠ 5) := by
  let crossCount := fun owner ↦ Fintype.card
    (componentCrossBipartiteGraph G source owner).ConnectedComponent
  have offSource {owner : (secondOrderDefectGraph G).ConnectedComponent}
      (hso : source ≠ owner) (hsize : owner.supp.ncard = 16)
      (hc : OrderSixtyFourPropagatedOwnerCollision G source owner) :
      crossCount owner ≠ 5 := by
    exact orderSixtyFour_propagatedOwnerCollision_crossCount_ne_five
      G hfree hreg source owner hso hsource hsize hc
  by_cases hsα : source = α
  · right
    right
    refine ⟨offSource (fun hsβ => hαβ (hsα.symm.trans hsβ)) hβsize hβ,
      offSource (fun hsγ => hαγ (hsα.symm.trans hsγ)) hγsize hγ⟩
  · by_cases hsβ : source = β
    · right
      left
      refine ⟨offSource hsα hαsize hα,
        offSource (fun hsγ => hβγ (hsβ.symm.trans hsγ)) hγsize hγ⟩
    · left
      exact ⟨offSource hsα hαsize hα, offSource hsβ hβsize hβ⟩

end

end Erdos85
