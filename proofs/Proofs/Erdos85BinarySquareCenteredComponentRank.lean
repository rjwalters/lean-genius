import Proofs.Erdos85BinarySquareCenteredComponentLaplacian
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact rank of centered component-incidence blocks

This file transfers the integral component Gram factorization to `ℝ` and
extracts its exact rank.  The columns belonging to a defect component have
only the single constant linear dependency.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The real centered incidence matrix, obtained by casting the canonical
integral matrix. -/
def realCenteredDefectComponentNeighborIncidenceMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix V c.supp ℝ :=
  (centeredDefectComponentNeighborIncidenceMatrix G q c).map
    (Int.castRingHom ℝ)

private theorem lapMatrix_map_intCast
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] :
    (H.lapMatrix ℤ).map (Int.castRingHom ℝ) = H.lapMatrix ℝ := by
  ext x y
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.map_apply, Matrix.sub_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply]
  split_ifs <;> norm_num

/-- Real form of the component Laplacian Gram factorization. -/
theorem transpose_realCenteredDefectComponentNeighborIncidenceMatrix_mul_self_eq_lapMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (realCenteredDefectComponentNeighborIncidenceMatrix G q c).transpose *
        realCenteredDefectComponentNeighborIncidenceMatrix G q c =
      ((q * q : ℕ) : ℝ) •
        ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ := by
  have hz :=
    transpose_centeredDefectComponentNeighborIncidenceMatrix_mul_self_eq_lapMatrix
      G hfree hq hreg hcard c
  have hr := congrArg
    (fun M : Matrix c.supp c.supp ℤ => M.map (Int.castRingHom ℝ)) hz
  have hmap :
      ((((q * q : ℕ) : ℤ) •
          ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℤ).map
            (Int.castRingHom ℝ)) =
        ((q * q : ℕ) : ℝ) •
          ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ := by
    rw [← lapMatrix_map_intCast]
    ext x y
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul]
    norm_num
  rw [hmap] at hr
  simpa only [realCenteredDefectComponentNeighborIncidenceMatrix,
    Matrix.map_mul, Matrix.transpose_map] using hr

/-- **Exact centered-block rank.**  The columns indexed by a defect component
span a space of dimension `|c| - 1`; their only lost direction is constant. -/
theorem realCenteredDefectComponentNeighborIncidenceMatrix_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (realCenteredDefectComponentNeighborIncidenceMatrix G q c).rank =
      Fintype.card c.supp - 1 := by
  let B := realCenteredDefectComponentNeighborIncidenceMatrix G q c
  let H := (secondOrderDefectGraph G).induce c.supp
  have hgram : B.transpose * B = ((q * q : ℕ) : ℝ) • H.lapMatrix ℝ := by
    simpa [B, H] using
      transpose_realCenteredDefectComponentNeighborIncidenceMatrix_mul_self_eq_lapMatrix
        G hfree hq hreg hcard c
  have ha : ((q * q : ℕ) : ℝ) ≠ 0 := by positivity
  have hmulVecLin :
      (((q * q : ℕ) : ℝ) • H.lapMatrix ℝ).mulVecLin =
        ((q * q : ℕ) : ℝ) • (H.lapMatrix ℝ).mulVecLin := by
    ext v x
    simp
  have hker : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
    rw [← Matrix.ker_mulVecLin_transpose_mul_self B, hgram, hmulVecLin,
      LinearMap.ker_smul _ _ ha]
    exact induced_connectedComponent_lapMatrix_nullity_eq_one
      (secondOrderDefectGraph G) c
  have hrankNull := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  change Module.finrank ℝ (LinearMap.range B.mulVecLin) =
    Fintype.card c.supp - 1
  rw [hker] at hrankNull
  have hcardfun : Module.finrank ℝ (c.supp → ℝ) = Fintype.card c.supp :=
    Module.finrank_fintype_fun_eq_card ℝ
  rw [hcardfun] at hrankNull
  omega

end

end Erdos85
