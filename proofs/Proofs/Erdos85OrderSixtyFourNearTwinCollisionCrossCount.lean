import Proofs.Erdos85DegreeTwoTwoTwinBlocksExcludeUniqueFourCycle
import Proofs.Erdos85NearTwinPrivateRowPropagation
import Proofs.Erdos85RoutingOwnerRainbowSelectorTriangle
import Proofs.Erdos85BinarySquareCenteredComponentLaplacian
import Proofs.Erdos85DefectComponentBlockCommute

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

/-- Direct λ=6 interface: an equal owner row at a codegree-six pair already
forces the propagated private collision, so its source/owner cross graph is
not in the five-component profile. -/
theorem orderSixtyFour_nearTwin_rowCollision_crossComponentCount_ne_five
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
    (x y : source.supp) (hxy : x ≠ y)
    (hxyNot : ¬ ((secondOrderDefectGraph G).induce source.supp).Adj x y)
    (hcommon :
      ((((secondOrderDefectGraph G).induce source.supp).neighborFinset x) ∩
        (((secondOrderDefectGraph G).induce source.supp).neighborFinset y)).card = 6)
    (hxyRows :
      (restrictedComponentOwnerGraph G source owner).neighborFinset x =
        (restrictedComponentOwnerGraph G source owner).neighborFinset y) :
    Fintype.card
      (componentCrossBipartiteGraph G source owner).ConnectedComponent ≠ 5 := by
  classical
  let D := (secondOrderDefectGraph G).induce source.supp
  let F := restrictedComponentOwnerGraph G source owner
  have hDreg : ∀ z, D.degree z = 7 := by
    intro z
    simpa [D] using binarySquare_regular_inducedDefectComponent_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) source z
  have hrowsMatrix : ∀ z, F.adjMatrix ℤ x z = F.adjMatrix ℤ y z := by
    intro z
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    have hiff : F.Adj x z ↔ F.Adj y z := by
      rw [← F.mem_neighborFinset, ← F.mem_neighborFinset, hxyRows]
    by_cases hxz : F.Adj x z <;> by_cases hyz : F.Adj y z <;>
      simp_all
  let O := componentOwnerGraph G (secondOrderDefectGraph G) owner
  have hOD : O.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * O.adjMatrix ℤ := by
    simpa [O] using
      binarySquare_regular_componentOwnerGraph_adjMatrix_comm_defect
        G hfree (q := 8) (by norm_num) hreg (by norm_num) owner
          (m_c := 2) (by norm_num; exact howner)
  have hDF : D.adjMatrix ℤ * F.adjMatrix ℤ =
      F.adjMatrix ℤ * D.adjMatrix ℤ := by
    change ((secondOrderDefectGraph G).induce source.supp).adjMatrix ℤ *
        (O.induce source.supp).adjMatrix ℤ =
      (O.induce source.supp).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce source.supp).adjMatrix ℤ
    exact induce_component_adjMatrix_comm_of_comm
      O (secondOrderDefectGraph G) hOD source |>.symm
  obtain ⟨p, q, hpq, hp, _hq, hpqMatrixRows⟩ :=
    sevenRegular_nearTwin_equal_commutingRows_propagate_private
      D hDreg (by simpa [D] using hcommon) (F.adjMatrix ℤ)
        hDF hrowsMatrix
  have hpqRows : F.neighborFinset p = F.neighborFinset q := by
    apply Finset.ext
    intro z
    rw [F.mem_neighborFinset, F.mem_neighborFinset]
    have h := hpqMatrixRows z
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply] at h
    by_cases hpz : F.Adj p z <;> by_cases hqz : F.Adj q z <;>
      simp_all
  exact orderSixtyFour_propagatedCollision_crossComponentCount_ne_five
    G hfree hreg source owner hso hsource howner x y p q hxy hpq hxyNot
      (by simpa [D] using hp) hxyRows hpqRows

/-- Numerical form of the direct λ=6 cross-count obstruction. -/
theorem orderSixtyFour_nearTwin_rowCollision_crossComponentCount_le_four
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
    (x y : source.supp) (hxy : x ≠ y)
    (hxyNot : ¬ ((secondOrderDefectGraph G).induce source.supp).Adj x y)
    (hcommon :
      ((((secondOrderDefectGraph G).induce source.supp).neighborFinset x) ∩
        (((secondOrderDefectGraph G).induce source.supp).neighborFinset y)).card = 6)
    (hxyRows :
      (restrictedComponentOwnerGraph G source owner).neighborFinset x =
        (restrictedComponentOwnerGraph G source owner).neighborFinset y) :
    Fintype.card
      (componentCrossBipartiteGraph G source owner).ConnectedComponent ≤ 4 := by
  have hle5 :=
    orderSixtyFour_twoSizeTwoParts_crossBipartiteComponent_count_le_five
      G hfree hreg (by norm_num) source owner hso hsource howner
  have hne5 :=
    orderSixtyFour_nearTwin_rowCollision_crossComponentCount_ne_five
      G hfree hreg source owner hso hsource howner x y hxy hxyNot
        hcommon hxyRows
  omega

end

end Erdos85
