import Proofs.Erdos85SquareOrderHighQuadraticSector
import Proofs.Erdos85NonregularDefectOperator

/-!
# High differences in the minus-one defect sector

At square order, adjacency-row differences between high vertices lie in the
`A² = d` sector.  The nonregular defect identity then places the same vectors
in the `-1` eigenspace of the second-order defect graph.  This converts the
quadratic adjacency sector into a combinatorial spectral constraint.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def degreePredDiagonalRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℚ :=
  Matrix.diagonal fun x => (G.degree x : ℚ) - 1

def onesMatrixRat (V : Type*) : Matrix V V ℚ := fun _ _ => 1

theorem adjMatrixRat_sq_eq_degreePredDiagonalRat_add_ones_sub_secondOrderDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    G.adjMatrix ℚ * G.adjMatrix ℚ =
      degreePredDiagonalRat G + onesMatrixRat V -
        (secondOrderDefectGraph G).adjMatrix ℚ := by
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, onesMatrixRat]
  by_cases hxy : x = y
  · subst y
    rw [G.adjMatrix_mul_self_apply_self]
    simp [degreePredDiagonalRat, SimpleGraph.adjMatrix_apply]
  · have hentry : (G.adjMatrix ℚ * G.adjMatrix ℚ) x y =
        ((G.neighborFinset x ∩ G.neighborFinset y).card : ℚ) := by
      simp only [Matrix.mul_apply, SimpleGraph.adjMatrix_apply]
      simp_rw [ite_mul, one_mul, zero_mul]
      have hterm : ∀ z : V,
          (if G.Adj x z then if G.Adj z y then (1 : ℚ) else 0 else 0) =
            if G.Adj x z ∧ G.Adj y z then 1 else 0 := by
        intro z
        by_cases hxz : G.Adj x z <;> by_cases hyz : G.Adj y z <;>
          simp [hxz, hyz, G.adj_comm]
      simp_rw [hterm]
      rw [Finset.sum_boole]
      norm_cast
      apply congrArg Finset.card
      ext z
      simp [neighborFinset_eq_filter]
    rw [hentry]
    simp only [degreePredDiagonalRat, Matrix.diagonal_apply_ne _ hxy]
    have hcommon := card_common_eq_if_secondOrderDefect G hfree x y hxy
    by_cases hdefect : y ∈ (secondOrderDefectGraph G).neighborFinset x
    · rw [if_pos hdefect] at hcommon
      have hadj : (secondOrderDefectGraph G).Adj x y :=
        ((secondOrderDefectGraph G).mem_neighborFinset x y).mp hdefect
      simp [SimpleGraph.adjMatrix_apply, hadj, hcommon]
    · rw [if_neg hdefect] at hcommon
      have hadj : ¬(secondOrderDefectGraph G).Adj x y := by
        intro hadj
        exact hdefect
          (((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hadj)
      simp [SimpleGraph.adjMatrix_apply, hadj, hcommon]

theorem squareOrder_highRowDifferenceRat_defect_mulVec_eq_neg
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d)
    (b : {x // x ∈ (squareOrderHighVertices G d).erase a}) :
    ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec
        (squareOrderHighRowDifferenceRat G b.1 a) =
      -squareOrderHighRowDifferenceRat G b.1 a := by
  let r := squareOrderHighRowDifferenceRat G b.1 a
  have hbHigh : b.1 ∈ squareOrderHighVertices G d :=
    Finset.mem_of_mem_erase b.2
  have haDegree : G.degree a = d + 1 := (Finset.mem_filter.mp ha).2
  have hbDegree : G.degree b.1 = d + 1 :=
    (Finset.mem_filter.mp hbHigh).2
  have hnotAdj : ∀ {x y : V}, x ∈ squareOrderHighVertices G d →
      y ∈ squareOrderHighVertices G d → ¬G.Adj x y := by
    intro x y hx hy hxy
    exact squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
  have hrHighZero : ∀ x ∈ squareOrderHighVertices G d, r x = 0 := by
    intro x hx
    have hbx := hnotAdj hbHigh hx
    have hax := hnotAdj ha hx
    simp [r, squareOrderHighRowDifferenceRat,
      SimpleGraph.adjMatrix_apply, hbx, hax]
  have hdiag : (degreePredDiagonalRat G).mulVec r =
      (d - 1 : ℚ) • r := by
    funext x
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard x with hx | hx
    · simp [degreePredDiagonalRat, Matrix.mulVec, dotProduct, hx,
        Pi.smul_apply, Matrix.diagonal_apply]
    · have hxHigh : x ∈ squareOrderHighVertices G d := by
        simp [squareOrderHighVertices, hx]
      simp [degreePredDiagonalRat, Matrix.mulVec, dotProduct,
        hrHighZero x hxHigh, Pi.smul_apply, Matrix.diagonal_apply]
  have hsum : ∑ x : V, r x = 0 := by
    simp only [r, squareOrderHighRowDifferenceRat, Finset.sum_sub_distrib]
    have hbSum : (∑ x : V, G.adjMatrix ℚ b.1 x) = (G.degree b.1 : ℚ) := by
      simp only [SimpleGraph.adjMatrix_apply, Finset.sum_boole]
      norm_cast
      rw [← G.card_neighborFinset_eq_degree]
      congr 1
      ext x
      simp [neighborFinset_eq_filter]
    have haSum : (∑ x : V, G.adjMatrix ℚ a x) = (G.degree a : ℚ) := by
      simp only [SimpleGraph.adjMatrix_apply, Finset.sum_boole]
      norm_cast
      rw [← G.card_neighborFinset_eq_degree]
      congr 1
      ext x
      simp [neighborFinset_eq_filter]
    rw [hbSum, haSum, hbDegree, haDegree]
    ring
  have hones : (onesMatrixRat V).mulVec r = 0 := by
    funext x
    simp [onesMatrixRat, Matrix.mulVec, dotProduct, hsum]
  have hsq : (G.adjMatrix ℚ * G.adjMatrix ℚ).mulVec r = (d : ℚ) • r := by
    rw [← Matrix.mulVec_mulVec]
    simpa [r, squareOrderHighQuadraticSectorFamily] using
      squareOrder_adjMatrixRat_sq_mulVec_highQuadraticSectorFamily
        G hfree hd hmin hcard ha (Sum.inr b)
  have hid := congrArg (fun M : Matrix V V ℚ => M.mulVec r)
    (adjMatrixRat_sq_eq_degreePredDiagonalRat_add_ones_sub_secondOrderDefect
      G hfree)
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, hdiag, hones, add_zero, hsq] at hid
  funext x
  have hx := congrFun hid x
  change ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec r x = -r x
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hx
  linarith

def secondOrderDefectPlusOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    (V → ℚ) →ₗ[ℚ] (V → ℚ) :=
  ((secondOrderDefectGraph G).adjMatrix ℚ).toLin' + LinearMap.id

theorem squareOrder_highRowDifferenceRat_mem_defectPlusOne_ker
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d)
    (b : {x // x ∈ (squareOrderHighVertices G d).erase a}) :
    squareOrderHighRowDifferenceRat G b.1 a ∈
      LinearMap.ker (secondOrderDefectPlusOne G) := by
  rw [LinearMap.mem_ker]
  simp only [secondOrderDefectPlusOne, LinearMap.add_apply,
    Matrix.toLin'_apply, LinearMap.id_coe, id_eq]
  rw [squareOrder_highRowDifferenceRat_defect_mulVec_eq_neg
    G hfree hd hmin hcover hcard ha b]
  exact neg_add_cancel _

theorem squareOrder_high_card_sub_one_le_finrank_defectPlusOne_ker
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    (squareOrderHighVertices G d).card - 1 ≤
      Module.finrank ℚ (LinearMap.ker (secondOrderDefectPlusOne G)) := by
  let E := {x // x ∈ (squareOrderHighVertices G d).erase a}
  let rows : E → (V → ℚ) := fun b =>
    squareOrderHighRowDifferenceRat G b.1 a
  let rowsKer : E → LinearMap.ker (secondOrderDefectPlusOne G) := fun b =>
    ⟨rows b, squareOrder_highRowDifferenceRat_mem_defectPlusOne_ker
      G hfree hd hmin hcover hcard ha b⟩
  have hrows : LinearIndependent ℚ rows := by
    simpa [E, rows] using squareOrder_highRowDifferencesRat_linearIndependent
      G hfree hd hmin hcard ha
  have hrowsKer : LinearIndependent ℚ rowsKer := by
    apply LinearIndependent.of_comp
      (LinearMap.ker (secondOrderDefectPlusOne G)).subtype
    simpa [Function.comp_def, rowsKer] using hrows
  have hbound := hrowsKer.fintype_card_le_finrank
  have herase : Fintype.card E =
      (squareOrderHighVertices G d).card - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem ha]
  simpa only [herase] using hbound

end

end Erdos85
