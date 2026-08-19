import Proofs.Erdos85SixTenAllTfOwnerCnfBridge

/-!
# Concrete coordinate terminal for the all-triangle-free six-plus-ten owner certificate

This packages the three shore-wise exterior-pair laws into the fixed
`Fin 16` owner model and invokes the checked CNF contradiction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

open SixTenAllTfOwnerBridge

set_option maxHeartbeats 0

theorem sixTenAllTfExteriorPairModel_false_of_shoreCoordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (a b : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (hurange : Set.range u = a.supp)
    (hvrange : Set.range v = b.supp)
    (hcover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp)
    (coord : c.supp ≃ Fin 16)
    (hcoordu : ∀ i, coord (u i) = zmodSixLeftFin16 i)
    (hcoordv : ∀ j, coord (v j) = zmodTenRightFin16 j)
    (hleft : ∀ i j : ZMod 6,
      (exteriorPairGraph G c).Adj (u i) (u j) ↔ j - i = 3)
    (hright : ∀ i j : ZMod 10,
      (exteriorPairGraph G c).Adj (v i) (v j) ↔
        j - i = 3 ∨ j - i = 5 ∨ j - i = 7)
    (hcross : ∀ (i : ZMod 6) (j : ZMod 10),
      (exteriorPairGraph G c).Adj (u i) (v j) ↔
        ((ZMod.finEquiv 6).symm i).val % 2 ≠
          ((ZMod.finEquiv 10).symm j).val % 2)
    (hcycle : ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔ sixTenAllTfCycleAdj (coord x).val (coord y).val = true) :
    False := by
  have hmodel := sixTenAllTfExteriorPair_pointwise_model_of_shores
    G c a b u v hurange hvrange hcover coord hcoordu hcoordv
      hleft hright hcross
  let modelIso := sixTenAllTfExteriorPairModelIso G c coord hmodel
  apply sixTenAllTfExteriorPairModel_false
    G hfree c hcard hinc hqcard hRedges modelIso
  intro x y
  simpa [modelIso, sixTenAllTfExteriorPairModelIso] using hcycle x y

end

end Erdos85

#print axioms Erdos85.sixTenAllTfExteriorPairModel_false_of_shoreCoordinates
