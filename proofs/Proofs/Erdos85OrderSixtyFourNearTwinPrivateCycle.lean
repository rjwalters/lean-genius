import Proofs.Erdos85NearTwinPrivateCycleTerminal
import Proofs.Erdos85NearTwinOwnerFork
import Proofs.Erdos85DefectComponentBlockCommute

/-! # Graph-facing order-sixty-four private-cycle contradiction -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the order-sixty-four no-rainbow branch, a directed two-step cycle of
codegree-six private pairs inside one defect component is impossible.

The repeated-owner-fork theorem supplies a two-regular owner color whose rows
at `x,y` agree.  Global owner/defect commutation restricts to the component,
so the abstract private-cycle terminal applies.  Hence a component classifier
only has to furnish the displayed induced-defect facts. -/
theorem orderSixtyFour_noRainbow_privateCycle_twoStep_false
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ a, G.degree a = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y z u v : d.supp)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxyNot : ¬ ((secondOrderDefectGraph G).induce d.supp).Adj x y)
    (hxyCommon :
      ((((secondOrderDefectGraph G).induce d.supp).neighborFinset x) ∩
        (((secondOrderDefectGraph G).induce d.supp).neighborFinset y)).card = 6)
    (huXY : u ∈
      ((secondOrderDefectGraph G).induce d.supp).neighborFinset x \
        ((secondOrderDefectGraph G).induce d.supp).neighborFinset y)
    (hvYX : v ∈
      ((secondOrderDefectGraph G).induce d.supp).neighborFinset y \
        ((secondOrderDefectGraph G).induce d.supp).neighborFinset x)
    (huvCommon :
      ((((secondOrderDefectGraph G).induce d.supp).neighborFinset u) ∩
        (((secondOrderDefectGraph G).induce d.supp).neighborFinset v)).card = 6)
    (hyUV : y ∈
      ((secondOrderDefectGraph G).induce d.supp).neighborFinset u \
        ((secondOrderDefectGraph G).induce d.supp).neighborFinset v)
    (hzVU : z ∈
      ((secondOrderDefectGraph G).induce d.supp).neighborFinset v \
        ((secondOrderDefectGraph G).induce d.supp).neighborFinset u)
    (hno : ∀ a b c,
      a ≠ b → a ≠ c → b ≠ c → ¬ routingOwnerRainbow G d a b c) : False := by
  classical
  let D := (secondOrderDefectGraph G).induce d.supp
  obtain ⟨owner, r₁, r₂, _howner, hr, _hr₁, _hr₂,
      hxr₁, hyr₁, hxr₂, hyr₂⟩ :=
    orderSixtyFour_codegreeSix_forces_repeatedOwnerFork
      G hfree hreg hcount d x y hxy hxyNot hxyCommon hno
  let H := restrictedComponentOwnerGraph G d owner
  have hdcard :=
    orderSixtyFour_regular_four_defectComponents_all_orderSixteen
      G hfree hreg hcount d
  have hDreg : ∀ a, D.degree a = 7 := by
    intro a
    simpa [D] using binarySquare_regular_inducedDefectComponent_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d a
  have hHreg : ∀ a, H.degree a = 2 := by
    intro a
    simpa [H] using
      binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
        G hfree (q := 8) (by norm_num) hreg (by norm_num) d owner
          (by simpa using hdcard) (by
            simpa using
              orderSixtyFour_regular_four_defectComponents_all_orderSixteen
                G hfree hreg hcount owner) a
  have hxyRows : H.neighborFinset x = H.neighborFinset y := by
    exact degreeTwo_repeatedFork_neighborFinset_eq
      H hHreg hr hxr₁ hyr₁ hxr₂ hyr₂
  let O := componentOwnerGraph G (secondOrderDefectGraph G) owner
  have hOD : O.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * O.adjMatrix ℤ := by
    simpa [O] using
      binarySquare_regular_componentOwnerGraph_adjMatrix_comm_defect
        G hfree (q := 8) (by norm_num) hreg (by norm_num) owner
          (m_c := 2) (by
            simpa using
              orderSixtyFour_regular_four_defectComponents_all_orderSixteen
                G hfree hreg hcount owner)
  have hHD : H.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * H.adjMatrix ℤ := by
    change (O.induce d.supp).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce d.supp).adjMatrix ℤ =
      ((secondOrderDefectGraph G).induce d.supp).adjMatrix ℤ *
        (O.induce d.supp).adjMatrix ℤ
    exact induce_component_adjMatrix_comm_of_comm
      O (secondOrderDefectGraph G) hOD d
  exact sevenRegular_privateCycle_twoStep_ownerColor_false
    D H hDreg hHreg hHD.symm hxy hxz hyz
      (by simpa [D] using hxyCommon)
      (by simpa [D] using huXY) (by simpa [D] using hvYX)
      (by simpa [D] using huvCommon)
      (by simpa [D] using hyUV) (by simpa [D] using hzVU) hxyRows

end

end Erdos85
