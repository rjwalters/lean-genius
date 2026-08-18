import Proofs.Erdos85BinarySquareRoutingColorTwoLifts
import Proofs.Erdos85OrderSixtyFourRegularPartition
import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity

/-! # Global lower bound for monochromatic routing triples -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-component order-64 branch, every routing color occurs on at
least 128 monochromatic triples across any three pairwise distinct endpoint
components. This is `64` directly colored endpoint pairs, each with at least
two same-color lifts through the middle component. -/
theorem orderSixtyFour_regular_fourComponents_routingColor_monochromaticTriple_count_ge
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :
    128 ≤ ∑ x : c.supp, ∑ w : f.supp,
      ((Finset.univ : Finset e.supp).filter fun z =>
        d = crossIntermediateComponent G hfree hce x z ∧
        d = crossIntermediateComponent G hfree hef z w).card := by
  classical
  have hsize := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hcCard : Fintype.card c.supp = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_coe_set_eq c.supp).trans (hsize c)
  have hrow (x : c.supp) :
      ((Finset.univ : Finset f.supp).filter fun w =>
        d = crossIntermediateComponent G hfree hcf x w).card = 4 :=
    binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
      G hfree (q := 8) (by omega) hreg (by norm_num) c d f hcf
        (by simpa using hsize c) (by simpa using hsize d)
        (by simpa using hsize f) x
  have hperRow : ∀ x : c.supp, 8 ≤ ∑ w : f.supp,
      ((Finset.univ : Finset e.supp).filter fun z =>
        d = crossIntermediateComponent G hfree hce x z ∧
        d = crossIntermediateComponent G hfree hef z w).card := by
    intro x
    let S := (Finset.univ : Finset f.supp).filter fun w =>
      d = crossIntermediateComponent G hfree hcf x w
    let L : f.supp → ℕ := fun w =>
      ((Finset.univ : Finset e.supp).filter fun z =>
        d = crossIntermediateComponent G hfree hce x z ∧
        d = crossIntermediateComponent G hfree hef z w).card
    have hSCard : S.card = 4 := by simpa [S] using hrow x
    have hrestricted : 8 ≤ ∑ w ∈ S, L w := by
      calc
        8 = ∑ w ∈ S, 2 := by simp [hSCard]
        _ ≤ ∑ w ∈ S, L w := by
          apply Finset.sum_le_sum
          intro w hw
          have hwRoute : d = crossIntermediateComponent G hfree hcf x w :=
            (Finset.mem_filter.mp hw).2
          exact binarySquare_regular_sizeTwoRoutingColor_two_le_lift_card
            G hfree (q := 8) (by omega) hreg (by norm_num)
              c d e f hce hef hcf (by simpa using hsize e) x w hwRoute
    calc
      8 ≤ ∑ w ∈ S, L w := hrestricted
      _ ≤ ∑ w : f.supp, L w := by
        exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = _ := by rfl
  calc
    128 = ∑ _x : c.supp, 8 := by simp [hcCard]
    _ ≤ ∑ x : c.supp, ∑ w : f.supp,
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
          d = crossIntermediateComponent G hfree hef z w).card := by
      apply Finset.sum_le_sum
      intro x _hx
      exact hperRow x

end

end Erdos85
