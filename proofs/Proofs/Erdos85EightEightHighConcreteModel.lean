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
  (exteriorPairGraph G c.supp).comap
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
    exteriorPairGraph G c.supp ≃g
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
      (exteriorPairGraph G c.supp).Adj (u i) (u j) := by
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
      (exteriorPairGraph G c.supp).Adj (v i) (v j) := by
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
      (exteriorPairGraph G c.supp).Adj (u i) (v j) := by
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

theorem zmodEight_negOnePow_eq_iff_parity (i j : ZMod 8) :
    (-1 : ℤ) ^ ((ZMod.finEquiv 8).symm i).val =
        (-1 : ℤ) ^ ((ZMod.finEquiv 8).symm j).val ↔
      ((ZMod.finEquiv 8).symm i).val % 2 =
        ((ZMod.finEquiv 8).symm j).val % 2 := by
  fin_cases i <;> fin_cases j <;> decide

/-- At quotient parameter six, normalized alternating coordinates realize
exactly the fixed odd-offset shore support and no same-parity cross edge. -/
theorem eightEightHighCoordinateExteriorGraph_fixed_and_candidate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hVcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (husign : ∀ z, s (u z).1 =
      (-1 : ℤ) ^ ((ZMod.finEquiv 8).symm z).val)
    (hvsign : ∀ z, s (v z).1 =
      (-1 : ℤ) ^ ((ZMod.finEquiv 8).symm z).val)
    (hab6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6)
    (hba6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 6) :
    let R := eightEightHighCoordinateExteriorGraph G c (by omega)
      a b hab u v huinj hvinj hurange hvrange
    (∀ e : Fin 64, eightEightHighActiveVariable? e = none →
      R.Adj (eightEightHighOwnerFirst e) (eightEightHighOwnerSecond e)) ∧
    ∀ x y, R.Adj x y →
      eightEightHighCandidatePair x y = true ∨
        eightEightHighCandidatePair y x = true := by
  let R := eightEightHighCoordinateExteriorGraph G c (by omega)
    a b hab u v huinj hvinj hurange hvrange
  have hDu :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_defectAdj_iff_halfTurn
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs
        a b ha hb hab u v huinj hvinj hurange hvrange hu hv hab6
  have hDv :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_defectAdj_iff_halfTurn
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs
        b a hb ha hab.symm v u hvinj huinj hvrange hurange hv hu hba6
  have hleft : ∀ i j : ZMod 8,
      R.Adj (zmodEightLeftFin16 i) (zmodEightLeftFin16 j) ↔
        EightEightOddOffset i j := by
    intro i j
    rw [eightEightHighCoordinateExteriorGraph_left_left]
    exact sizeTwo_eight_halfTurnDefect_exteriorPair_iff_odd_nonzero
      G hfree c u huinj hu hDu i j
  have hright : ∀ i j : ZMod 8,
      R.Adj (zmodEightRightFin16 i) (zmodEightRightFin16 j) ↔
        EightEightOddOffset i j := by
    intro i j
    rw [eightEightHighCoordinateExteriorGraph_right_right]
    exact sizeTwo_eight_halfTurnDefect_exteriorPair_iff_odd_nonzero
      G hfree c v hvinj hv hDv i j
  have hcomp := sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    G hfree c a b hab u v hurange hvrange
  have hsat :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_crossAntipodal_saturation
      G hfree hreg hVcard c hc s hs_in hs_out hA_in hDs
        a b ha hb hab u v huinj hvinj hurange hvrange hu hv hab6
  have hcross : ∀ i j : ZMod 8,
      R.Adj (zmodEightLeftFin16 i) (zmodEightRightFin16 j) →
        ((ZMod.finEquiv 8).symm i).val % 2 ≠
          ((ZMod.finEquiv 8).symm j).val % 2 := by
    intro i j hR hpar
    have hsign : s (v j).1 = s (u i).1 := by
      rw [husign, hvsign]
      exact (zmodEight_negOnePow_eq_iff_parity j i).mpr hpar.symm
    have hK := (hsat.1 i j).mpr (hsat.2 i j hsign)
    exact (hcomp i j).mp (by
      simpa [R] using hR) hK
  exact eightEightHigh_fixed_and_candidate_support R hleft hright hcross

end

end Erdos85

#print axioms Erdos85.eightEightHighCoordinateExteriorGraphIso_cycle
