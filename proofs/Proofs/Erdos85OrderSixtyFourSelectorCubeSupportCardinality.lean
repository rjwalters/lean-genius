import Proofs.Erdos85BinarySquareThreeSelectorCubeLines
import Proofs.Erdos85OrderSixtyFourOwnerMixedTraces

/-!
# Cardinality of the order-64 three-selector support

Every axis-parallel line contains two selector-support points.  For three
size-16 components this gives support cardinality `512` and complement
cardinality `3584`, exactly the mixed three-owner trace.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Finite form of the three-selector cube support. -/
def threeSelectorCubeSupportFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e : (secondOrderDefectGraph G).ConnectedComponent) :
    Finset (c.supp × d.supp × e.supp) := by
  classical
  exact Finset.univ.filter fun p => p ∈ threeSelectorCubeSupport G c d e

/-- At order 64, three pairwise distinct size-16 coordinates have exactly
`512 = 64·2³` supported selector triples. -/
theorem orderSixtyFour_threeSizeSixteen_selectorCubeSupport_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16)
    (he : e.supp.ncard = 16) :
    (threeSelectorCubeSupportFinset G c d e).card = 512 := by
  classical
  have hlines :=
    binarySquare_regular_threeSizeTwoParts_cubeSupport_allAxisLines_exactlyTwo
      G hfree (q := 8) (by omega) hreg (by simpa using hcard)
        c d e hcd hce hde (by simpa using hc) (by simpa using hd)
          (by simpa using he)
  have hlineCard : ∀ a : c.supp, ∀ b : d.supp,
      ((Finset.univ : Finset e.supp).filter fun z =>
        (a, b, z) ∈ threeSelectorCubeSupport G c d e).card = 2 := by
    intro a b
    obtain ⟨u, v, huv, hline⟩ := hlines.1 a b
    have heq : ((Finset.univ : Finset e.supp).filter fun z =>
        (a, b, z) ∈ threeSelectorCubeSupport G c d e) = {u, v} := by
      ext z
      simp [hline z]
    rw [heq]
    simp [huv]
  have hcs : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hc
  have hds : Fintype.card d.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hd
  have hlineSum : ∀ a : c.supp, ∀ b : d.supp,
      (∑ z : e.supp,
        if (a, b, z) ∈ threeSelectorCubeSupport G c d e then 1 else 0) = 2 := by
    intro a b
    rw [Finset.sum_boole]
    exact hlineCard a b
  simp only [threeSelectorCubeSupportFinset]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  simp_rw [hlineSum]
  simp [hcs, hds]

/-- The complement of the three-selector support has cardinality `3584`. -/
theorem orderSixtyFour_threeSizeSixteen_selectorCubeSupport_compl_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16)
    (he : e.supp.ncard = 16) :
    ((Finset.univ : Finset (c.supp × d.supp × e.supp)) \
      threeSelectorCubeSupportFinset G c d e).card = 3584 := by
  classical
  have hsupp := orderSixtyFour_threeSizeSixteen_selectorCubeSupport_card
    G hfree hreg hcard c d e hcd hce hde hc hd he
  have hcs : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hc
  have hds : Fintype.card d.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hd
  have hes : Fintype.card e.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact he
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hsupp]
  simp [Fintype.card_prod, hcs, hds, hes]

/-- The mixed three-owner cubic trace equals the number of unsupported
selector triples. -/
theorem orderSixtyFour_owner_triple_trace_eq_selectorCubeSupport_compl_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16)
    (he : e.supp.ncard = 16) :
    Matrix.trace
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) e).adjMatrix ℤ) =
      (((Finset.univ : Finset (c.supp × d.supp × e.supp)) \
        threeSelectorCubeSupportFinset G c d e).card : ℤ) := by
  rw [orderSixtyFour_pairwiseDistinct_sizeSixteen_owner_triple_trace_eq
    G hfree hreg hcard c d e hc hd he hcd hde hce.symm]
  rw [orderSixtyFour_threeSizeSixteen_selectorCubeSupport_compl_card
    G hfree hreg hcard c d e hcd hce hde hc hd he]
  norm_num

end

end Erdos85
