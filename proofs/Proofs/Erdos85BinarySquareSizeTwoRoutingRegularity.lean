import Proofs.Erdos85BinarySquareCrossBlockUniqueRouting
import Proofs.Erdos85BinarySquareSizeTwoCrossIndexedBlocks

/-! # Uniform routing multiplicities between size-two components -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem crossIncidence_row_sum_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {c d : (secondOrderDefectGraph G).ConnectedComponent}
    (x : c.supp)
    (hcard : (componentCrossNeighborFinset G d x).card = 2) :
    (∑ y : d.supp,
      defectComponentCrossIncidenceMatrix (K := ℤ) G c d x y) = 2 := by
  simp only [defectComponentCrossIncidenceMatrix,
    defectComponentNeighborIncidenceMatrix]
  calc
    (∑ y : d.supp, if G.Adj x.1 y.1 then (1 : ℤ) else 0) =
        ((componentCrossNeighborFinset G d x).card : ℤ) := by
      rw [Finset.sum_boole]
      rfl
    _ = 2 := by exact_mod_cast hcard

private theorem transpose_cross_mul_cross_row_sum_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcardV : Fintype.card V = q * q)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (he : e.supp.ncard = q * 2) (x : c.supp) :
    (∑ z : e.supp,
      ((defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
        defectComponentCrossIncidenceMatrix (K := ℤ) G d e) x z) = 4 := by
  have hdc :=
    binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
      G hfree hq hreg hcardV d c hd hc
  have hde :=
    binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
      G hfree hq hreg hcardV d e hd he
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  calc
    (∑ y : d.supp, ∑ z : e.supp,
        (defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose x y *
          defectComponentCrossIncidenceMatrix (K := ℤ) G d e y z) =
        ∑ y : d.supp,
          (defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose x y * 2 := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← Finset.mul_sum]
      congr 1
      exact crossIncidence_row_sum_eq_two G y (hde.2.1 y)
    _ = 4 := by
      rw [hdc.1]
      simp_rw [← Finset.sum_mul]
      rw [crossIncidence_row_sum_eq_two G x (hdc.2.2 x)]
      norm_num

/-- Fixing the left endpoint and an intermediate size-two component, exactly
four right endpoints receive that routing label. -/
theorem binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcardV : Fintype.card V = q * q)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (he : e.supp.ncard = q * 2) (x : c.supp) :
    ((Finset.univ : Finset e.supp).filter fun z =>
      d = crossIntermediateComponent G hfree hce x z).card = 4 := by
  have hsum := transpose_cross_mul_cross_row_sum_eq_four
    G hfree hq hreg hcardV c d e hc hd he x
  simp_rw [transpose_cross_mul_cross_apply_eq_ite_intermediate
    G hfree hce] at hsum
  rw [Finset.sum_boole] at hsum
  exact_mod_cast hsum

/-- Fixing the right endpoint and an intermediate size-two component, exactly
four left endpoints receive that routing label. -/
theorem binarySquare_regular_threeSizeTwoParts_routing_column_card_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcardV : Fintype.card V = q * q)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (he : e.supp.ncard = q * 2) (z : e.supp) :
    ((Finset.univ : Finset c.supp).filter fun x =>
      d = crossIntermediateComponent G hfree hce x z).card = 4 := by
  have hdc :=
    binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
      G hfree hq hreg hcardV d c hd hc
  have hde :=
    binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
      G hfree hq hreg hcardV d e hd he
  have hsum :
      (∑ x : c.supp,
        ((defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
          defectComponentCrossIncidenceMatrix (K := ℤ) G d e) x z) = 4 := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc
      (∑ y : d.supp, ∑ x : c.supp,
          (defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose x y *
            defectComponentCrossIncidenceMatrix (K := ℤ) G d e y z) =
          ∑ y : d.supp, 2 *
            defectComponentCrossIncidenceMatrix (K := ℤ) G d e y z := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [← Finset.sum_mul]
        congr 1
        simpa only [Matrix.transpose_apply] using
          crossIncidence_row_sum_eq_two G y (hdc.2.1 y)
      _ = 4 := by
        rw [← Finset.mul_sum]
        have hcol :
            (∑ y : d.supp,
              defectComponentCrossIncidenceMatrix (K := ℤ) G d e y z) = 2 := by
          calc
            (∑ y : d.supp,
                defectComponentCrossIncidenceMatrix (K := ℤ) G d e y z) =
                ∑ y : d.supp,
                  (defectComponentCrossIncidenceMatrix
                    (K := ℤ) G d e).transpose z y := by rfl
            _ = ∑ y : d.supp,
                  defectComponentCrossIncidenceMatrix (K := ℤ) G e d z y := by
                rw [hde.1]
            _ = 2 := crossIncidence_row_sum_eq_two G z (hde.2.2 z)
        rw [hcol]
        norm_num
  simp_rw [transpose_cross_mul_cross_apply_eq_ite_intermediate
    G hfree hce] at hsum
  rw [Finset.sum_boole] at hsum
  exact_mod_cast hsum

end

end Erdos85
