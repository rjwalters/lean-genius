import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourDiagonalModel
import Proofs.Erdos85SizeTwoMuNegOneSelfCellOneFourCrossSplit

/-!
# Complete exterior geometry socket for the `mu=-1`, `(k,r)=(1,4)` cell

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

This file packages the exact two shore models and the variable cross block
in the form consumed by an owner-grid CNF.  It deliberately stops before
DIMACS numbering: the only remaining work is the generic outside-owner
semantics and a checked finite certificate for the three shore-mode cases.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- One normalized shore has within-shore owner support either `±3` or
`±1`. -/
def MuNegOneOneFourShoreExteriorModel
    {X : Type*} (R : SimpleGraph X) (u : ZMod 8 → X) : Prop :=
  (∀ i j, R.Adj (u i) (u j) ↔ j - i = 3 ∨ j - i = 5) ∨
  (∀ i j, R.Adj (u i) (u j) ↔ j - i = 1 ∨ j - i = 7)

/-- The parameter-four cross owner block has exactly two same-sign and two
opposite-sign entries in every row and column. -/
def MuNegOneOneFourCrossExteriorSplit
    {X : Type*} (R : SimpleGraph X) [DecidableRel R.Adj]
    (u v : ZMod 8 → X)
    (su sv : ZMod 8 → ℤ) : Prop :=
  (∀ i,
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      R.Adj (u i) (v j) ∧ sv j = su i).card = 2 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      R.Adj (u i) (v j) ∧ sv j ≠ su i).card = 2) ∧
  (∀ j,
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      R.Adj (u i) (v j) ∧ su i = sv j).card = 2 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      R.Adj (u i) (v j) ∧ su i ≠ sv j).card = 2)

set_option maxHeartbeats 0

/-- Complete terminal-facing exterior geometry of the parameter-four cell.
The diagonal same-sign degree-one rows force both half-turns; quotient three
then selects one of the two exact shore models, while quotient four and the
native cross signed ledgers give the exact `2+2` cross split. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_oneFour_completeExteriorGeometry
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (s : V → ℤ)
    (hsu : ∀ i, s (u i).1 = -1 ∨ s (u i).1 = 1)
    (hsv : ∀ j, s (v j).1 = -1 ∨ s (v j).1 = 1)
    (hflipu : ∀ i, s (u (i + 1)).1 = -s (u i).1)
    (hflipv : ∀ j, s (v (j + 1)).1 = -s (v j).1)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hbb3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3)
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4)
    (hdiagU : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u i).1 ∧
          ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j)).card = 1)
    (hdiagV : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (v i).1 ∧
          ((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j)).card = 1)
    (hcrossA : ∀ x ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ a.supp),
      (((Finset.univ : Finset c.supp).filter (fun y ↦ y ∈ b.supp)).filter
        (fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
          s y.1 = s x.1)).card = 2)
    (hcrossB : ∀ x ∈ (Finset.univ : Finset c.supp).filter
        (fun x ↦ x ∈ b.supp),
      (((Finset.univ : Finset c.supp).filter (fun y ↦ y ∈ a.supp)).filter
        (fun y ↦ ((secondOrderDefectGraph G).induce c.supp).Adj x y ∧
          s y.1 = s x.1)).card = 2) :
    let R := exteriorPairGraph G c.supp
    MuNegOneOneFourShoreExteriorModel R u ∧
    MuNegOneOneFourShoreExteriorModel R v ∧
    MuNegOneOneFourCrossExteriorSplit R u v
      (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) := by
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ :=
    (adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c).symm
  have hfourU := graph_zmodEight_sameSign_degreeOne_halfTurn
    H K u huinj hu (fun x : c.supp ↦ s x.1) hsu hflipu hcomm hdiagU
  have hfourV := graph_zmodEight_sameSign_degreeOne_halfTurn
    H K v hvinj hv (fun x : c.supp ↦ s x.1) hsv hflipv hcomm hdiagV
  have hshoreU :=
    binarySquare_regular_sizeTwoPart_eight_diagonalThree_halfTurn_exact_exterior_supports
      G hfree hreg hcard c hc a u huinj hurange hu haa3 hfourU
  have hshoreV :=
    binarySquare_regular_sizeTwoPart_eight_diagonalThree_halfTurn_exact_exterior_supports
      G hfree hreg hcard c hc b v hvinj hvrange hv hbb3 hfourV
  have hcross :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterFour_crossExterior_signed_two_two
      G hfree hreg hcard c hc a b ha hb hab u v huinj hvinj hurange hvrange
        s hsu hsv hflipu hflipv hab4 hcrossA hcrossB
  exact ⟨hshoreU, hshoreV, by
    simpa [MuNegOneOneFourCrossExteriorSplit] using hcross⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_oneFour_completeExteriorGeometry
