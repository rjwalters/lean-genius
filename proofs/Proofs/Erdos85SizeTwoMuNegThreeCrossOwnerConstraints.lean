import Proofs.Erdos85SizeTwoMuNegThreeCrossOwners

/-! # Collision constraints for `mu = -3` cross-pair owners -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If two cross-shore pairs have the same ambient owner, then the two
crossed pairs are nondefect as well. Thus every owner fibre cuts out a
complete bipartite rectangle in the cubic cross-nondefect relation. -/
theorem orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (x x' : MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
    (y y' : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s)
    (z : V)
    (hz : G.Adj x.1 z ∧ G.Adj y.1 z)
    (hz' : G.Adj x'.1 z ∧ G.Adj y'.1 z) :
    ¬ (secondOrderDefectGraph G).Adj x.1 y'.1 ∧
      ¬ (secondOrderDefectGraph G).Adj x'.1 y.1 := by
  have hne (u : MuNegThreePositiveShore (secondOrderDefectGraph G) c s)
      (v : MuNegThreeNegativeShore (secondOrderDefectGraph G) c s) :
      u.1 ≠ v.1 := by
    intro huv
    have hsuv : s u.1 = s v.1 := congrArg s huv
    omega
  constructor
  · intro hxy'
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree (hne x y')).mp hxy'
    have hmem : z ∈ G.neighborFinset x.1 ∩ G.neighborFinset y'.1 := by
      simp [hz.1, hz'.2]
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem
  · intro hx'y
    have hzero :=
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree (hne x' y)).mp hx'y
    have hmem : z ∈ G.neighborFinset x'.1 ∩ G.neighborFinset y.1 := by
      simp [hz'.1, hz.2]
    rw [Finset.card_eq_zero.mp hzero] at hmem
    simp at hmem

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_cross_owner_rectangle
