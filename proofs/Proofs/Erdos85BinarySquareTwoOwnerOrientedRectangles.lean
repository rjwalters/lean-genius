import Proofs.Erdos85BinarySquareTwoOwnerPointwiseClosings
import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Disjoint oriented mixed-owner rectangles

Mixed two-step middle sets with different ordered owner-color pairs cannot
overlap.  Consequently the two orientations of a pair of distinct owner
components contribute two disjoint full rectangles at any root pair having
neither displayed owner.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Different ordered owner-color pairs give disjoint mixed-middle sets. -/
theorem coloredTwoStepMiddles_disjoint_of_orderedOwners_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (a b c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hpairs : (a, b) ≠ (c, d)) (x y : V) :
    Disjoint
      (coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) x y)
      (coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) d) x y) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzab hzcd
  have hab := (Finset.mem_filter.mp hzab).2
  have hcd := (Finset.mem_filter.mp hzcd).2
  have hca : c = a :=
    (componentOwnerGraph_adj_iff_owner_eq_of_adj G hfree a hab.1 c).mp hcd.1
  have hdb : d = b :=
    (componentOwnerGraph_adj_iff_owner_eq_of_adj G hfree b hab.2 d).mp hcd.2
  apply hpairs
  exact Prod.ext hca.symm hdb.symm

/-- At a pair having neither displayed owner, the two orientations of
distinct owners contribute exactly `2 m_a m_b` distinct middles. -/
theorem binarySquare_regular_two_orientedOwnerRectangles_union_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    {x y : V} (hxy : x ≠ y)
    (hnotA : ¬ (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x y)
    (hnotB : ¬ (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj x y) :
    ((coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) x y) ∪
      (coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) x y)).card =
        2 * m_a * m_b := by
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  have hAB : (coloredTwoStepMiddles A B x y).card = m_a * m_b := by
    exact binarySquare_regular_noDisplayedOwner_coloredTwoStepMiddles_card
      G hfree hq hreg hcard a b hab ha hb hxy hnotA hnotB
  have hBA : (coloredTwoStepMiddles B A x y).card = m_b * m_a := by
    exact binarySquare_regular_noDisplayedOwner_coloredTwoStepMiddles_card
      G hfree hq hreg hcard b a hab.symm hb ha hxy hnotB hnotA
  have hpairs : (a, b) ≠ (b, a) := by
    intro h
    exact hab (congrArg Prod.fst h)
  have hdis : Disjoint (coloredTwoStepMiddles A B x y)
      (coloredTwoStepMiddles B A x y) := by
    exact coloredTwoStepMiddles_disjoint_of_orderedOwners_ne
      G hfree a b b a hpairs x y
  rw [Finset.card_union_of_disjoint hdis, hAB, hBA]
  ring

end

end Erdos85
