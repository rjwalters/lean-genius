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

def EightEightOddOffset (i j : ZMod 8) : Prop :=
  j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7

instance (i j : ZMod 8) : Decidable (EightEightOddOffset i j) := by
  unfold EightEightOddOffset
  infer_instance

theorem finSixteen_left_or_right (x : Fin 16) :
    (∃ i : ZMod 8, x = zmodEightLeftFin16 i) ∨
      ∃ j : ZMod 8, x = zmodEightRightFin16 j := by
  revert x
  native_decide

theorem eightEightHighCandidate_left_left_iff (i j : ZMod 8) :
    (eightEightHighCandidatePair (zmodEightLeftFin16 i)
        (zmodEightLeftFin16 j) = true ∨
      eightEightHighCandidatePair (zmodEightLeftFin16 j)
        (zmodEightLeftFin16 i) = true) ↔ EightEightOddOffset i j := by
  fin_cases i <;> fin_cases j <;> native_decide

theorem eightEightHighCandidate_right_right_iff (i j : ZMod 8) :
    (eightEightHighCandidatePair (zmodEightRightFin16 i)
        (zmodEightRightFin16 j) = true ∨
      eightEightHighCandidatePair (zmodEightRightFin16 j)
        (zmodEightRightFin16 i) = true) ↔ EightEightOddOffset i j := by
  fin_cases i <;> fin_cases j <;> native_decide

theorem eightEightHighCandidate_left_right_iff (i j : ZMod 8) :
    eightEightHighCandidatePair (zmodEightLeftFin16 i)
        (zmodEightRightFin16 j) = true ↔
      ((ZMod.finEquiv 8).symm i).val % 2 ≠
        ((ZMod.finEquiv 8).symm j).val % 2 := by
  revert i j
  native_decide

theorem eightEightHighFixedOwner_of_inactive
    (e : Fin 64) (hfixed : eightEightHighActiveVariable? e = none) :
    eightEightHighFixedOwnerPair (eightEightHighOwnerFirst e)
      (eightEightHighOwnerSecond e) = true := by
  revert e
  native_decide

theorem eightEightHighFixed_left_left_odd (i j : ZMod 8) :
    eightEightHighFixedOwnerPair (zmodEightLeftFin16 i)
        (zmodEightLeftFin16 j) = true → EightEightOddOffset i j := by
  fin_cases i <;> fin_cases j <;> native_decide

theorem eightEightHighFixed_right_right_odd (i j : ZMod 8) :
    eightEightHighFixedOwnerPair (zmodEightRightFin16 i)
        (zmodEightRightFin16 j) = true → EightEightOddOffset i j := by
  fin_cases i <;> fin_cases j <;> native_decide

theorem eightEightHighFixed_cross_false (i j : ZMod 8) :
    eightEightHighFixedOwnerPair (zmodEightLeftFin16 i)
      (zmodEightRightFin16 j) = false := by
  fin_cases i <;> fin_cases j <;> native_decide

theorem eightEightHighFixed_cross_reverse_false (i j : ZMod 8) :
    eightEightHighFixedOwnerPair (zmodEightRightFin16 i)
      (zmodEightLeftFin16 j) = false := by
  fin_cases i <;> fin_cases j <;> native_decide

/-- Coordinate laws reduce the generator's fixed/candidate support fields to
the two same-shore odd-offset blocks and the opposite-parity cross block. -/
theorem eightEightHigh_fixed_and_candidate_support
    (R : SimpleGraph (Fin 16))
    (hleft : ∀ i j : ZMod 8,
      R.Adj (zmodEightLeftFin16 i) (zmodEightLeftFin16 j) ↔
        EightEightOddOffset i j)
    (hright : ∀ i j : ZMod 8,
      R.Adj (zmodEightRightFin16 i) (zmodEightRightFin16 j) ↔
        EightEightOddOffset i j)
    (hcross : ∀ i j : ZMod 8,
      R.Adj (zmodEightLeftFin16 i) (zmodEightRightFin16 j) →
        ((ZMod.finEquiv 8).symm i).val % 2 ≠
          ((ZMod.finEquiv 8).symm j).val % 2) :
    (∀ e : Fin 64, eightEightHighActiveVariable? e = none →
      R.Adj (eightEightHighOwnerFirst e) (eightEightHighOwnerSecond e)) ∧
    ∀ a b, R.Adj a b →
      eightEightHighCandidatePair a b = true ∨
        eightEightHighCandidatePair b a = true := by
  constructor
  · intro e he
    have hf := eightEightHighFixedOwner_of_inactive e he
    rcases finSixteen_left_or_right (eightEightHighOwnerFirst e) with
      ⟨i, hi⟩ | ⟨i, hi⟩ <;>
      rcases finSixteen_left_or_right (eightEightHighOwnerSecond e) with
        ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [hi, hj, hleft]
      exact eightEightHighFixed_left_left_odd i j (by simpa [hi, hj] using hf)
    · rw [hi, hj, eightEightHighFixed_cross_false] at hf
      contradiction
    · rw [hi, hj, eightEightHighFixed_cross_reverse_false] at hf
      contradiction
    · rw [hi, hj, hright]
      exact eightEightHighFixed_right_right_odd i j (by simpa [hi, hj] using hf)
  · intro x y hxy
    rcases finSixteen_left_or_right x with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      rcases finSixteen_left_or_right y with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact (eightEightHighCandidate_left_left_iff i j).mpr
        ((hleft i j).mp hxy)
    · exact Or.inl ((eightEightHighCandidate_left_right_iff i j).mpr
        (hcross i j hxy))
    · exact Or.inr ((eightEightHighCandidate_left_right_iff j i).mpr
        (hcross j i hxy.symm))
    · exact (eightEightHighCandidate_right_right_iff i j).mpr
        ((hright i j).mp hxy)

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
