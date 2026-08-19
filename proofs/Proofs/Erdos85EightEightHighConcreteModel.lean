import Proofs.Erdos85EightEightAlignedShoreCoordinates
import Proofs.Erdos85EightEightHighOwnerCrossCoordinateTransport
import Proofs.Erdos85SizeTwoEigenlineEightEightHighParameterCrossBlock
import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalMatching
import Proofs.Erdos85SizeTwoEigenlineEightEightHighCrossAntipodal

/-! # Concrete normalized exterior model for the high eight-plus-eight case -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

def eightEightHighCoordinateExteriorGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    SimpleGraph (Fin 16) :=
  (exteriorPairGraph G c).comap
    (eightEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
      hurange hvrange).symm

noncomputable def eightEightHighCoordinateExteriorGraphIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    exteriorPairGraph G c ≃g
      eightEightHighCoordinateExteriorGraph G c hc a b hab u v huinj hvinj
        hurange hvrange where
  toEquiv := eightEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
    hurange hvrange
  map_rel_iff' := by
    intro x y
    simp [eightEightHighCoordinateExteriorGraph]

@[simp] theorem eightEightHighCoordinateExteriorGraph_left_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i j : ZMod 8) :
    (eightEightHighCoordinateExteriorGraph G c hc a b hab u v huinj hvinj
      hurange hvrange).Adj (zmodEightLeftFin16 i) (zmodEightLeftFin16 j) ↔
      (exteriorPairGraph G c).Adj (u i) (u j) := by
  let coord := eightEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
    hurange hvrange
  have hi : coord.symm (zmodEightLeftFin16 i) = u i := by
    apply coord.injective
    simp [coord]
  have hj : coord.symm (zmodEightLeftFin16 j) = u j := by
    apply coord.injective
    simp [coord]
  simp [eightEightHighCoordinateExteriorGraph, coord, hi, hj]

@[simp] theorem eightEightHighCoordinateExteriorGraph_right_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i j : ZMod 8) :
    (eightEightHighCoordinateExteriorGraph G c hc a b hab u v huinj hvinj
      hurange hvrange).Adj (zmodEightRightFin16 i) (zmodEightRightFin16 j) ↔
      (exteriorPairGraph G c).Adj (v i) (v j) := by
  let coord := eightEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
    hurange hvrange
  have hi : coord.symm (zmodEightRightFin16 i) = v i := by
    apply coord.injective
    simp [coord]
  have hj : coord.symm (zmodEightRightFin16 j) = v j := by
    apply coord.injective
    simp [coord]
  simp [eightEightHighCoordinateExteriorGraph, coord, hi, hj]

@[simp] theorem eightEightHighCoordinateExteriorGraph_left_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (i j : ZMod 8) :
    (eightEightHighCoordinateExteriorGraph G c hc a b hab u v huinj hvinj
      hurange hvrange).Adj (zmodEightLeftFin16 i) (zmodEightRightFin16 j) ↔
      (exteriorPairGraph G c).Adj (u i) (v j) := by
  let coord := eightEightShoreCoordinateEquiv G c hc a b hab u v huinj hvinj
    hurange hvrange
  have hi : coord.symm (zmodEightLeftFin16 i) = u i := by
    apply coord.injective
    simp [coord]
  have hj : coord.symm (zmodEightRightFin16 j) = v j := by
    apply coord.injective
    simp [coord]
  simp [eightEightHighCoordinateExteriorGraph, coord, hi, hj]

/-- The model isomorphism uses exactly the fixed two-cycle coordinates. -/
theorem eightEightHighCoordinateExteriorGraphIso_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidablePred (· ∈ c.supp)]
    (hc : c.supp.ncard = 16)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔
        eightEightHighCycleAdj
          ((eightEightHighCoordinateExteriorGraphIso G c hc a b hab u v
            huinj hvinj hurange hvrange) x).val
          ((eightEightHighCoordinateExteriorGraphIso G c hc a b hab u v
            huinj hvinj hurange hvrange) y).val = true := by
  let labeling := eightEightCycleLabeling_of_shoreCoordinates
    G c hc a b hab u v huinj hvinj hurange hvrange hu hv
  intro x y
  change (G.induce c.supp).Adj x y ↔ _
  rw [labeling.map_adj_iff]
  change eightEightCycleGraph.Adj (labeling.toEquiv x) (labeling.toEquiv y) ↔
    eightEightHighCycleAdj (labeling.toEquiv x).val
      (labeling.toEquiv y).val = true
  have hfinite : ∀ p q : Fin 16,
      eightEightCycleGraph.Adj p q ↔
        eightEightHighCycleAdj p q = true := by
    intro p q
    revert p q
    native_decide
  exact hfinite _ _

end

end Erdos85

#print axioms Erdos85.eightEightHighCoordinateExteriorGraphIso_cycle
