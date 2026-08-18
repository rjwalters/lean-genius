import Proofs.Erdos85PathCharpoly

namespace Erdos85

open Polynomial Polynomial.Chebyshev SimpleGraph

noncomputable local instance (n : ℕ) : DecidableRel (pathGraph n).Adj := Classical.decRel _

theorem cycle_succ_sub_val_eq_one {n : ℕ} (i j : Fin (n + 2)) :
    (i.succ - j.succ).val = 1 ↔ j.val + 1 = i.val := by
  rw [Fin.val_sub]
  by_cases hji : j.val ≤ i.val
  · have heq : n + 2 + 1 - j.succ.val + i.succ.val =
        (n + 2 + 1) + (i.val - j.val) := by
      simp only [Fin.val_succ]
      omega
    rw [heq, Nat.add_mod, Nat.mod_self, zero_add,
      Nat.mod_eq_of_lt (by omega : i.val - j.val < n + 2 + 1)]
    rw [Nat.mod_eq_of_lt (by omega : i.val - j.val < n + 2 + 1)]
    rw [Nat.sub_eq_iff_eq_add hji]
    omega
  · have hij : i.val < j.val := by omega
    have heq : n + 2 + 1 - j.succ.val + i.succ.val =
        n + 2 + 1 - (j.val - i.val) := by
      simp only [Fin.val_succ]
      omega
    rw [heq, Nat.mod_eq_of_lt
      (by omega : n + 2 + 1 - (j.val - i.val) < n + 2 + 1)]
    omega

theorem cycleCharmatrix_tail (n : ℕ) :
    (((cycleGraph (n + 3)).adjMatrix ℤ).charmatrix.submatrix Fin.succ Fin.succ) =
      ((pathGraph (n + 2)).adjMatrix ℤ).charmatrix := by
  ext i j
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, cycleGraph_adj', pathGraph_adj,
    Matrix.submatrix_apply, Fin.ext_iff, cycle_succ_sub_val_eq_one, or_comm]

theorem cycle_middle_not_adj_zero {n : ℕ} (x : Fin n) :
    (-x.castSucc.succ.succ : Fin (n + 3)).val ≠ 1 := by
  intro h
  have heq : (-x.castSucc.succ.succ : Fin (n + 3)) = 1 := Fin.ext h
  have hneg := congrArg (fun z : Fin (n + 3) ↦ -z) heq
  have hv := congrArg Fin.val hneg
  simp only [neg_neg, Fin.val_succ, Fin.val_castSucc, Fin.coe_neg_one] at hv
  omega

theorem cycleCharmatrix_leftCofactor_pathMinor (n : ℕ) :
    ((adjMatrix ℤ (cycleGraph (n + 3))).charmatrix.submatrix
      (Fin.succ ∘ Fin.succAbove 0) ((Fin.succ 0).succAbove ∘ Fin.succ)) =
      (adjMatrix ℤ (pathGraph (n + 1))).charmatrix := by
  ext i j
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, cycleGraph_adj', pathGraph_adj,
    Matrix.submatrix_apply, Fin.ext_iff, cycle_succ_sub_val_eq_one, or_comm]

theorem cycleCharmatrix_shiftedMinor_det (n : ℕ) :
    (((adjMatrix ℤ (cycleGraph (n + 3))).charmatrix.submatrix
      (Fin.succ ∘ (Fin.last n).succ.succAbove)
      ((Fin.succ 0).succAbove ∘ Fin.succ)).det) =
      (-1 : ℤ[X]) ^ (n + 1) := by
  let Q := (adjMatrix ℤ (cycleGraph (n + 3))).charmatrix.submatrix
    (Fin.succ ∘ (Fin.last n).succ.succAbove)
    ((Fin.succ 0).succAbove ∘ Fin.succ)
  have htri : Q.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hi := i.isLt
    have hj := j.isLt
    simp [Q, Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, cycleGraph_adj', Matrix.submatrix_apply,
      Fin.ext_iff, cycle_succ_sub_val_eq_one]
    grind
  rw [Matrix.det_of_lowerTriangular Q htri]
  simp [Q, Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, cycleGraph_adj', Matrix.submatrix_apply,
    Fin.ext_iff, cycle_succ_sub_val_eq_one]

theorem cycleCharmatrix_leftCofactor (n : ℕ) :
    ((((cycleGraph (n + 3)).adjMatrix ℤ).charmatrix.submatrix
      Fin.succ (Fin.succ 0).succAbove).det) =
      -((pathGraph (n + 1)).adjMatrix ℤ).charpoly - 1 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc]
  simp only [Matrix.submatrix_submatrix, Fin.zero_succAbove]
  rw [cycleCharmatrix_leftCofactor_pathMinor n,
    cycleCharmatrix_shiftedMinor_det n]
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, cycleGraph_adj', Matrix.submatrix_apply,
    Matrix.charpoly, Fin.ext_iff, cycle_middle_not_adj_zero]
  have hsign : ((-1 : ℤ[X]) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [hsign]
  ring

theorem cycleCharmatrix_rightShiftedMinor_det (n : ℕ) :
    (((adjMatrix ℤ (cycleGraph (n + 3))).charmatrix.submatrix
      (Fin.succ ∘ Fin.succAbove 0) (Fin.castSucc ∘ Fin.succ)).det) =
      (-1 : ℤ[X]) ^ (n + 1) := by
  let Q := (adjMatrix ℤ (cycleGraph (n + 3))).charmatrix.submatrix
    (Fin.succ ∘ Fin.succAbove 0) (Fin.castSucc ∘ Fin.succ)
  have htri : Q.BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    have hi := i.isLt
    have hj := j.isLt
    simp [Q, Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply, cycleGraph_adj', Matrix.submatrix_apply,
      Fin.ext_iff, cycle_succ_sub_val_eq_one]
    grind
  rw [Matrix.det_of_upperTriangular htri]
  simp [Q, Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, cycleGraph_adj', Matrix.submatrix_apply,
    Fin.ext_iff, cycle_succ_sub_val_eq_one]

theorem cycleCharmatrix_rightPathMinor (n : ℕ) :
    ((adjMatrix ℤ (cycleGraph (n + 3))).charmatrix.submatrix
      (Fin.succ ∘ (Fin.last n).succ.succAbove) (Fin.castSucc ∘ Fin.succ)) =
      (adjMatrix ℤ (pathGraph (n + 1))).charmatrix := by
  ext i j
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, cycleGraph_adj', pathGraph_adj,
    Matrix.submatrix_apply, Fin.ext_iff, cycle_succ_sub_val_eq_one, or_comm]

theorem cycleCharmatrix_rightCofactorContribution (n : ℕ) :
    -((-1 : ℤ[X]) ^ (n + 2) *
      (((cycleGraph (n + 3)).adjMatrix ℤ).charmatrix.submatrix
        Fin.succ Fin.castSucc).det) =
      -((pathGraph (n + 1)).adjMatrix ℤ).charpoly - 1 := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc]
  simp only [Matrix.submatrix_submatrix]
  rw [cycleCharmatrix_rightShiftedMinor_det n,
    cycleCharmatrix_rightPathMinor n]
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, cycleGraph_adj', Matrix.submatrix_apply,
    Matrix.charpoly, Fin.ext_iff, cycle_middle_not_adj_zero]
  have hsign : (-1 : ℤ[X]) ^ (n + 2) * (-1) ^ (n + 1) = -1 := by
    rw [← pow_add]
    have : n + 2 + (n + 1) = 2 * (n + 1) + 1 := by omega
    rw [this, pow_add, pow_mul]
    simp
  let P := ((pathGraph (n + 1)).adjMatrix ℤ).charmatrix.det
  change -((-1 : ℤ[X]) ^ (n + 2) *
      (-(-1 : ℤ[X]) ^ (n + 1) + -((-1 : ℤ[X]) ^ (n + 1) * P))) = -P - 1
  calc
    _ = (((-1 : ℤ[X]) ^ (n + 2)) * (-1) ^ (n + 1)) * (1 + P) := by ring
    _ = -P - 1 := by rw [hsign]; ring

theorem cycleGraph_charpoly_expansion (n : ℕ) :
    ((cycleGraph (n + 3)).adjMatrix ℤ).charpoly =
      X * ((pathGraph (n + 2)).adjMatrix ℤ).charpoly -
        2 * ((pathGraph (n + 1)).adjMatrix ℤ).charpoly - 2 := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have htail :
      ((adjMatrix ℤ (cycleGraph (n + 3))).charmatrix.submatrix
        Fin.succ (Fin.succAbove 0)) =
        (adjMatrix ℤ (pathGraph (n + 2))).charmatrix := by
    simpa using cycleCharmatrix_tail n
  rw [htail]
  rw [cycleCharmatrix_leftCofactor n]
  have hr : -((-1 : ℤ[X]) ^ (n + 1 + 1) *
      (((cycleGraph (n + 3)).adjMatrix ℤ).charmatrix.submatrix
        Fin.succ Fin.castSucc).det) =
      -((pathGraph (n + 1)).adjMatrix ℤ).charpoly - 1 := by
    simpa only [show n + 1 + 1 = n + 2 by omega] using
      cycleCharmatrix_rightCofactorContribution n
  simp [Matrix.charmatrix, Matrix.scalar_apply, Matrix.diagonal_apply,
    SimpleGraph.adjMatrix_apply, cycleGraph_adj', Matrix.submatrix_apply,
    Matrix.charpoly, Fin.ext_iff, cycle_middle_not_adj_zero]
  have hr' : -((-1 : ℤ[X]) ^ (n + 1 + 1) *
      (((Matrix.diagonal fun _ : Fin (n + 3) ↦ X) -
        ((cycleGraph (n + 3)).adjMatrix ℤ).map Polynomial.C).submatrix
          Fin.succ Fin.castSucc).det) =
      -(((Matrix.diagonal fun _ : Fin (n + 1) ↦ X) -
        ((pathGraph (n + 1)).adjMatrix ℤ).map Polynomial.C).det) - 1 := by
    simpa [Matrix.charmatrix, Matrix.charpoly] using hr
  rw [hr']
  ring

theorem cycleGraph_charpoly_eq_chebyshev_C_sub_two (n : ℕ) :
    ((cycleGraph (n + 3)).adjMatrix ℤ).charpoly =
      C ℤ (n + 3 : ℕ) - 2 := by
  rw [cycleGraph_charpoly_expansion n,
    pathGraph_charpoly_eq_chebyshev_S (n + 2),
    pathGraph_charpoly_eq_chebyshev_S (n + 1),
    C_eq_S_sub_X_mul_S]
  have hs : S ℤ ((n + 3 : ℕ) : ℤ) =
      X * S ℤ ((n + 2 : ℕ) : ℤ) - S ℤ ((n + 1 : ℕ) : ℤ) := by
    convert S_add_two ℤ ((n : ℤ) + 1) using 1 <;> push_cast <;> ring
  ring_nf at hs ⊢
  rw [hs]
  have hidx : -1 + ((3 + n : ℕ) : ℤ) = ((2 + n : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hidx]
  ring

end Erdos85
