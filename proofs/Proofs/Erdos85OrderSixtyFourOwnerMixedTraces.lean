import Proofs.Erdos85BinarySquareOwnerBottomMultiplicity
import Proofs.Erdos85BinarySquareComponentIncidence

/-!
# Mixed owner traces in the order-64 all-two stratum

Distinct size-16 component incidence blocks have all-ones cross Grams.  This
determines pairwise and three-color mixed traces of their owner graphs.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem sizeSixteen_incidence_mul_transpose_eq_ownerShift_int
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    let I := defectComponentNeighborIncidenceMatrix (K := ℤ) G c
    let O := componentOwnerGraph G (secondOrderDefectGraph G) c
    I * I.transpose = O.adjMatrix ℤ +
      (2 : ℤ) • (1 : Matrix V V ℤ) := by
  dsimp
  let I := defectComponentNeighborIncidenceMatrix (K := ℤ) G c
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  have hr :=
    realDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_ownerShift
      G hfree (q := 8) (by omega) hreg (by simpa using hcard) c
        (m_c := 2) (by simpa using hc)
  apply (Matrix.map_injective (Int.cast_injective : Function.Injective
    (Int.castRingHom ℝ))).eq_iff.mp
  calc
    (I * I.transpose).map (Int.castRingHom ℝ) =
        realDefectComponentNeighborIncidenceMatrix G c *
          (realDefectComponentNeighborIncidenceMatrix G c).transpose := by
      rw [Matrix.map_mul, Matrix.transpose_map]
      rfl
    _ = O.adjMatrix ℝ + (2 : ℝ) • (1 : Matrix V V ℝ) := hr
    _ = (O.adjMatrix ℤ + (2 : ℤ) • (1 : Matrix V V ℤ)).map
        (Int.castRingHom ℝ) := by
      ext x y
      change O.adjMatrix ℝ x y + 2 * (if x = y then 1 else 0) =
        ((O.adjMatrix ℤ x y + 2 * (if x = y then 1 else 0) : ℤ) : ℝ)
      by_cases hxy : x = y <;>
        simp [SimpleGraph.adjMatrix_apply, hxy]

/-- Distinct size-16 owner adjacency matrices have zero mixed quadratic
trace. -/
theorem orderSixtyFour_distinct_sizeSixteen_owner_mul_trace_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16)
    (hcd : c ≠ d) :
    Matrix.trace
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ) = 0 := by
  let Ic := defectComponentNeighborIncidenceMatrix (K := ℤ) G c
  let Id := defectComponentNeighborIncidenceMatrix (K := ℤ) G d
  let Oc := (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ
  let Od := (componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ
  have hcs : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hc
  have hds : Fintype.card d.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hd
  have hshiftc := sizeSixteen_incidence_mul_transpose_eq_ownerShift_int
    G hfree hreg hcard c hc
  have hshiftd := sizeSixteen_incidence_mul_transpose_eq_ownerShift_int
    G hfree hreg hcard d hd
  have hcdGram := transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones
    G hfree c d hcd
  have hdcGram := transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones
    G hfree d c hcd.symm
  have hshiftTrace : Matrix.trace
      ((Oc + (2 : ℤ) • (1 : Matrix V V ℤ)) *
        (Od + (2 : ℤ) • (1 : Matrix V V ℤ))) = 256 := by
    rw [← hshiftc, ← hshiftd]
    calc
      Matrix.trace ((Ic * Ic.transpose) * (Id * Id.transpose)) =
          Matrix.trace ((Ic * (Ic.transpose * Id)) * Id.transpose) := by
        congr 1
        simp [Matrix.mul_assoc]
      _ = Matrix.trace (Id.transpose * (Ic * (Ic.transpose * Id))) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace
          ((Id.transpose * Ic) * (Ic.transpose * Id)) := by
        congr 1
        simp [Matrix.mul_assoc]
      _ = 256 := by
        rw [hdcGram, hcdGram]
        simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, hcs, hds]
  have htrc : Matrix.trace Oc = 0 :=
    SimpleGraph.trace_adjMatrix ℤ
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
  have htrd : Matrix.trace Od = 0 :=
    SimpleGraph.trace_adjMatrix ℤ
      (componentOwnerGraph G (secondOrderDefectGraph G) d)
  have hexpand :
      (Oc + (2 : ℤ) • (1 : Matrix V V ℤ)) *
          (Od + (2 : ℤ) • (1 : Matrix V V ℤ)) =
        Oc * Od + (2 : ℤ) • Oc + (2 : ℤ) • Od +
          (4 : ℤ) • (1 : Matrix V V ℤ) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul]
    module
  rw [hexpand, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, htrc, htrd, hcard] at hshiftTrace
  dsimp only [Oc, Od] at hshiftTrace ⊢
  norm_num at hshiftTrace
  linarith

/-- Three pairwise distinct size-16 owners have the exact mixed cubic trace
`3584`. -/
theorem orderSixtyFour_pairwiseDistinct_sizeSixteen_owner_triple_trace_eq
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
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16)
    (he : e.supp.ncard = 16)
    (hcd : c ≠ d) (hde : d ≠ e) (hec : e ≠ c) :
    Matrix.trace
      ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ *
        (componentOwnerGraph G (secondOrderDefectGraph G) e).adjMatrix ℤ) =
      3584 := by
  let Ic := defectComponentNeighborIncidenceMatrix (K := ℤ) G c
  let Id := defectComponentNeighborIncidenceMatrix (K := ℤ) G d
  let Ie := defectComponentNeighborIncidenceMatrix (K := ℤ) G e
  let Oc := (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ
  let Od := (componentOwnerGraph G (secondOrderDefectGraph G) d).adjMatrix ℤ
  let Oe := (componentOwnerGraph G (secondOrderDefectGraph G) e).adjMatrix ℤ
  have hcs : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hc
  have hds : Fintype.card d.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact hd
  have hes : Fintype.card e.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]; exact he
  have hshiftc := sizeSixteen_incidence_mul_transpose_eq_ownerShift_int
    G hfree hreg hcard c hc
  have hshiftd := sizeSixteen_incidence_mul_transpose_eq_ownerShift_int
    G hfree hreg hcard d hd
  have hshifte := sizeSixteen_incidence_mul_transpose_eq_ownerShift_int
    G hfree hreg hcard e he
  have hcdGram := transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones
    G hfree c d hcd
  have hdeGram := transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones
    G hfree d e hde
  have hecGram := transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones
    G hfree e c hec
  have hshiftTrace : Matrix.trace
      ((Oc + (2 : ℤ) • (1 : Matrix V V ℤ)) *
        (Od + (2 : ℤ) • (1 : Matrix V V ℤ)) *
        (Oe + (2 : ℤ) • (1 : Matrix V V ℤ))) = 4096 := by
    rw [← hshiftc, ← hshiftd, ← hshifte]
    calc
      Matrix.trace ((Ic * Ic.transpose) * (Id * Id.transpose) *
          (Ie * Ie.transpose)) =
        Matrix.trace
          ((Ic * ((Ic.transpose * Id) * (Id.transpose * Ie))) *
            Ie.transpose) := by
          congr 1
          simp [Matrix.mul_assoc]
      _ = Matrix.trace
          (Ie.transpose * (Ic * ((Ic.transpose * Id) *
            (Id.transpose * Ie)))) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace
          ((Ie.transpose * Ic) * (Ic.transpose * Id) *
            (Id.transpose * Ie)) := by
          congr 1
          simp [Matrix.mul_assoc]
      _ = 4096 := by
        rw [hecGram, hcdGram, hdeGram]
        simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, hcs, hds, hes]
  have hpairCD := orderSixtyFour_distinct_sizeSixteen_owner_mul_trace_eq_zero
    G hfree hreg hcard c d hc hd hcd
  have hpairCE := orderSixtyFour_distinct_sizeSixteen_owner_mul_trace_eq_zero
    G hfree hreg hcard c e hc he hec.symm
  have hpairDE := orderSixtyFour_distinct_sizeSixteen_owner_mul_trace_eq_zero
    G hfree hreg hcard d e hd he hde
  have htrc : Matrix.trace Oc = 0 :=
    SimpleGraph.trace_adjMatrix ℤ
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
  have htrd : Matrix.trace Od = 0 :=
    SimpleGraph.trace_adjMatrix ℤ
      (componentOwnerGraph G (secondOrderDefectGraph G) d)
  have htre : Matrix.trace Oe = 0 :=
    SimpleGraph.trace_adjMatrix ℤ
      (componentOwnerGraph G (secondOrderDefectGraph G) e)
  have hexpand :
      (Oc + (2 : ℤ) • (1 : Matrix V V ℤ)) *
        (Od + (2 : ℤ) • (1 : Matrix V V ℤ)) *
        (Oe + (2 : ℤ) • (1 : Matrix V V ℤ)) =
      Oc * Od * Oe + (2 : ℤ) • (Oc * Od) +
        (2 : ℤ) • (Oc * Oe) + (4 : ℤ) • Oc +
        (2 : ℤ) • (Od * Oe) + (4 : ℤ) • Od +
        (4 : ℤ) • Oe + (8 : ℤ) • (1 : Matrix V V ℤ) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add, smul_smul]
    module
  rw [hexpand, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_one, hpairCD, hpairCE, hpairDE,
    htrc, htrd, htre, hcard] at hshiftTrace
  dsimp only [Oc, Od, Oe] at hshiftTrace ⊢
  norm_num at hshiftTrace
  linarith

end

end Erdos85
