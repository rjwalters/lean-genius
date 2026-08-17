import Proofs.Erdos85DegreeTwoTwoTwinBlocksExcludeUniqueFourCycle
import Proofs.Erdos85NearTwinPrivateRowPropagation
import Proofs.Erdos85RoutingOwnerRainbowSelectorTriangle

/-! # A propagated near-twin collision excludes five cross components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If one restricted owner factor has equal rows on a defect near-twin and
on its directed private pair, then the corresponding source/owner cross graph
cannot have five components.  The five-component profile would permit only
one owner `C₄`, whereas the two separated equal-row pairs force two. -/
theorem orderSixtyFour_propagatedCollision_crossComponentCount_ne_five
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
    (x y p q : source.supp)
    (hxy : x ≠ y) (hpq : p ≠ q)
    (hxyNot : ¬ ((secondOrderDefectGraph G).induce source.supp).Adj x y)
    (hp : p ∈
      ((secondOrderDefectGraph G).induce source.supp).neighborFinset x \
        ((secondOrderDefectGraph G).induce source.supp).neighborFinset y)
    (hxyRows :
      (restrictedComponentOwnerGraph G source owner).neighborFinset x =
        (restrictedComponentOwnerGraph G source owner).neighborFinset y)
    (hpqRows :
      (restrictedComponentOwnerGraph G source owner).neighborFinset p =
        (restrictedComponentOwnerGraph G source owner).neighborFinset q) :
    Fintype.card
      (componentCrossBipartiteGraph G source owner).ConnectedComponent ≠ 5 := by
  classical
  intro hfive
  let D := (secondOrderDefectGraph G).induce source.supp
  let F := restrictedComponentOwnerGraph G source owner
  have hFdeg : ∀ z, F.degree z = 2 := by
    intro z
    simpa [F] using
      binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
        G hfree (q := 8) (by norm_num) hreg (by norm_num)
          source owner hsource howner z
  obtain ⟨hunique, hshape⟩ :=
    orderSixtyFour_twoSizeTwoParts_fiveCrossComponents_ownerProfile
      G hfree hreg (by norm_num) source owner hso hsource howner hfive
  have hpData := Finset.mem_sdiff.mp hp
  have hDxp : D.Adj x p := (D.mem_neighborFinset x p).mp hpData.1
  have hxp : x ≠ p := D.ne_of_adj hDxp
  have hyp : y ≠ p := by
    intro h
    subst p
    exact hxyNot hDxp
  have hcross : ¬F.Adj x p := by
    intro hFxp
    have hglobal :
        (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x.1 p.1 :=
      hFxp
    have hnD := componentOwnerGraph_adj_not_secondOrderDefect_adj
      G hfree owner hglobal
    exact hnD (by simpa [D] using hDxp)
  exact degreeTwo_false_of_two_separated_equalNeighbor_pairs_unique_four
    F hFdeg hunique hshape hxy hpq hxp hyp hxyRows hpqRows hcross

end

end Erdos85
