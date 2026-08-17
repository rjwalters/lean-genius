import Proofs.Erdos85BinarySquareSizeTwoCrossBlockNoRectangle
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Paired cross-block owner factors are cospectral -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem crossIncidence_mul_transpose_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : source.supp) :
    (defectComponentCrossIncidenceMatrix (K := ℤ) G source target *
      (defectComponentCrossIncidenceMatrix (K := ℤ) G source target).transpose)
        x y =
      (((componentCrossNeighborFinset G target x) ∩
        componentCrossNeighborFinset G target y).card : ℤ) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, defectComponentCrossIncidenceMatrix,
    defectComponentNeighborIncidenceMatrix, ite_mul, one_mul, zero_mul]
  calc
    (∑ z : target.supp,
      if G.Adj x.1 z.1 then if G.Adj y.1 z.1 then (1 : ℤ) else 0 else 0) =
        ∑ z : target.supp,
          if G.Adj x.1 z.1 ∧ G.Adj y.1 z.1 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hxz : G.Adj x.1 z.1 <;>
        by_cases hyz : G.Adj y.1 z.1 <;> simp [hxz, hyz]
    _ = (((componentCrossNeighborFinset G target x) ∩
        componentCrossNeighborFinset G target y).card : ℤ) := by
      rw [Finset.sum_boole]
      have hfilt :
          (Finset.univ : Finset target.supp).filter
              (fun z => G.Adj x.1 z.1 ∧ G.Adj y.1 z.1) =
            componentCrossNeighborFinset G target x ∩
              componentCrossNeighborFinset G target y := by
        ext z
        simp [componentCrossNeighborFinset]
      rw [hfilt]

/-- Row Gram of a size-two cross block: diagonal `2` plus the corresponding
restricted owner 2-factor. -/
theorem binarySquare_regular_sizeTwoTarget_crossIncidence_mul_transpose
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (htarget : target.supp.ncard = q * 2) :
    defectComponentCrossIncidenceMatrix (K := ℤ) G source target *
        (defectComponentCrossIncidenceMatrix (K := ℤ) G source target).transpose =
      Matrix.diagonal (fun _ => (2 : ℤ)) +
        (restrictedComponentOwnerGraph G source target).adjMatrix ℤ := by
  ext x y
  rw [crossIncidence_mul_transpose_apply]
  by_cases hxy : x = y
  · subst y
    have hcardCross : (componentCrossNeighborFinset G target x).card = 2 := by
      rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
      exact binarySquare_regular_sizeTwoPart_selector_card
        G hfree hq hreg hcard target htarget x.1
    simp [hcardCross, SimpleGraph.adjMatrix_apply]
  · have hinter := binarySquare_regular_sizeTwoTarget_crossRow_inter_card_eq_ite
      G hfree target x y hxy
    rw [hinter]
    by_cases hadj : (restrictedComponentOwnerGraph G source target).Adj x y <;>
      simp [hadj, hxy, SimpleGraph.adjMatrix_apply]

/-- Reversing a square size-two cross block gives the column Gram and the
reverse restricted owner factor. -/
theorem binarySquare_regular_twoSizeTwoParts_transpose_crossIncidence_mul_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    (defectComponentCrossIncidenceMatrix (K := ℤ) G c d).transpose *
        defectComponentCrossIncidenceMatrix (K := ℤ) G c d =
      Matrix.diagonal (fun _ => (2 : ℤ)) +
        (restrictedComponentOwnerGraph G d c).adjMatrix ℤ := by
  rw [defectComponentCrossIncidenceMatrix_transpose,
    ← defectComponentCrossIncidenceMatrix_transpose (K := ℤ) G d c]
  exact binarySquare_regular_sizeTwoTarget_crossIncidence_mul_transpose
    G hfree hq hreg hcard d c hc

/-- The restricted owner 2-factors paired by a size-two cross block have the
same characteristic polynomial.  Algebraically this is the square
rectangular `AB/BA` identity after removing the common scalar shift `2I`. -/
theorem binarySquare_regular_twoSizeTwoParts_restrictedOwner_charpoly_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    ((restrictedComponentOwnerGraph G c d).adjMatrix ℤ).charpoly =
      ((restrictedComponentOwnerGraph G d c).adjMatrix ℤ).charpoly := by
  let B := defectComponentCrossIncidenceMatrix (K := ℤ) G c d
  let A := (restrictedComponentOwnerGraph G c d).adjMatrix ℤ
  let C := (restrictedComponentOwnerGraph G d c).adjMatrix ℤ
  have hcardEq : Fintype.card c.supp = Fintype.card d.supp := by
    rw [Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard, hc, hd]
  have hmul := Matrix.charpoly_mul_comm_of_le B B.transpose
    (by omega : Fintype.card d.supp ≤ Fintype.card c.supp)
  have hrow : B * B.transpose = Matrix.diagonal (fun _ => (2 : ℤ)) + A := by
    simpa [B, A] using
      binarySquare_regular_sizeTwoTarget_crossIncidence_mul_transpose
        G hfree hq hreg hcard c d hd
  have hcol : B.transpose * B = Matrix.diagonal (fun _ => (2 : ℤ)) + C := by
    simpa [B, C] using
      binarySquare_regular_twoSizeTwoParts_transpose_crossIncidence_mul_self
        G hfree hq hreg hcard c d hc
  rw [hcardEq, Nat.sub_self, pow_zero, one_mul, hrow, hcol] at hmul
  have hAshift : Matrix.diagonal (fun _ => (2 : ℤ)) + A =
      A - Matrix.scalar c.supp (-2 : ℤ) := by
    rw [← Matrix.scalar_apply]
    rw [map_neg, sub_neg_eq_add]
    ac_rfl
  have hCshift : Matrix.diagonal (fun _ => (2 : ℤ)) + C =
      C - Matrix.scalar d.supp (-2 : ℤ) := by
    rw [← Matrix.scalar_apply]
    rw [map_neg, sub_neg_eq_add]
    ac_rfl
  have hshift :
      A.charpoly.comp (Polynomial.X + Polynomial.C (-2 : ℤ)) =
        C.charpoly.comp (Polynomial.X + Polynomial.C (-2 : ℤ)) := by
    rw [← Matrix.charpoly_sub_scalar A (-2 : ℤ),
      ← Matrix.charpoly_sub_scalar C (-2 : ℤ), ← hAshift, ← hCshift]
    exact hmul
  have hinv := congrArg
    (fun p : Polynomial ℤ => p.comp (Polynomial.X + Polynomial.C (2 : ℤ)))
    hshift
  simpa [Polynomial.comp_assoc] using hinv

end

end Erdos85
