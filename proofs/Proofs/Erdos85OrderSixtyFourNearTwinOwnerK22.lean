import Proofs.Erdos85NearTwinOwnerFork
import Proofs.Erdos85DegreeTwoRepeatedForkSaturation

/-! # A defect near-twin forces an isolated owner four-cycle -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-component, no-owner-rainbow order-64 branch, every
codegree-six defect nonedge forces a nonbase restricted-owner factor with an
isolated `K₂,₂` block. -/
theorem orderSixtyFour_codegreeSix_forces_isolatedOwnerK22
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : d.supp) (hxy : x ≠ y)
    (hnot : ¬ ((secondOrderDefectGraph G).induce d.supp).Adj x y)
    (hcode : ((((secondOrderDefectGraph G).induce d.supp).neighborFinset x) ∩
      (((secondOrderDefectGraph G).induce d.supp).neighborFinset y)).card = 6)
    (hno : ∀ a b c,
      a ≠ b → a ≠ c → b ≠ c → ¬ routingOwnerRainbow G d a b c) :
    let base := nondefectPairOwner G hfree
      (fun h => hxy (Subtype.ext h)) (by simpa using hnot)
    ∃ owner r₁ r₂, owner ≠ base ∧ r₁ ≠ r₂ ∧
      let O := restrictedComponentOwnerGraph G d owner
      O.neighborFinset x = {r₁, r₂} ∧
      O.neighborFinset y = {r₁, r₂} ∧
      O.neighborFinset r₁ = {x, y} ∧
      O.neighborFinset r₂ = {x, y} := by
  classical
  dsimp only
  obtain ⟨owner, r₁, r₂, howner, hrne, _hr₁, _hr₂,
      hxr₁, hyr₁, hxr₂, hyr₂⟩ :=
    orderSixtyFour_codegreeSix_forces_repeatedOwnerFork
      G hfree hreg hcount d x y hxy hnot hcode hno
  refine ⟨owner, r₁, r₂, howner, hrne, ?_⟩
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hdeg : ∀ z,
      (restrictedComponentOwnerGraph G d owner).degree z = 2 := by
    intro z
    exact binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d owner
        (by simpa using hall d) (by simpa using hall owner) z
  exact degreeTwo_repeatedFork_isolatedK22
    (restrictedComponentOwnerGraph G d owner) hdeg hxy hrne
      hxr₁ hyr₁ hxr₂ hyr₂

end

end Erdos85
