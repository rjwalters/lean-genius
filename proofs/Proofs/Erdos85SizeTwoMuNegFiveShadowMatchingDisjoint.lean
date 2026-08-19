import Proofs.Erdos85SizeTwoMuNegFiveExtremeShadows

/-!
# Disjointness of the `mu=-5` exterior shadows and defect matchings

A second-order defect pair has no ambient common neighbor.  Consequently
the four-regular extreme-incidence shadow on either sign shore avoids the
same-sign defect perfect matching.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem orderSixtyFour_sizeTwo_muNegFive_extreme_shadows_disjoint_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) :
    let D := secondOrderDefectGraph G
    let Xp := MuNegFivePositiveShore D c s
    let Xm := MuNegFiveNegativeShore D c s
    let Sp := MuNegFiveExtremeFiber G c s 2
    let Sm := MuNegFiveExtremeFiber G c s (-2)
    let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
    let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
    (∀ ⦃x y⦄, (twoIncidenceShadow Rp).Adj x y → ¬ D.Adj x.1 y.1) ∧
      ∀ ⦃x y⦄, (twoIncidenceShadow Rm).Adj x y → ¬ D.Adj x.1 y.1 := by
  dsimp only
  let D := secondOrderDefectGraph G
  let Xp := MuNegFivePositiveShore D c s
  let Xm := MuNegFiveNegativeShore D c s
  let Sp := MuNegFiveExtremeFiber G c s 2
  let Sm := MuNegFiveExtremeFiber G c s (-2)
  let Rp := fun x : Xp => fun z : Sp => G.Adj x.1 z.1
  let Rm := fun x : Xm => fun z : Sm => G.Adj x.1 z.1
  constructor
  · intro x y hxy
    obtain ⟨hne, z, hxz, hyz⟩ := hxy
    change G.Adj x.1 z.1 at hxz
    change G.Adj y.1 z.1 at hyz
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree
      (fun h => hne (Subtype.ext h)) hxz hyz
  · intro x y hxy
    obtain ⟨hne, z, hxz, hyz⟩ := hxy
    change G.Adj x.1 z.1 at hxz
    change G.Adj y.1 z.1 at hyz
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree
      (fun h => hne (Subtype.ext h)) hxz hyz

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_extreme_shadows_disjoint_defect
