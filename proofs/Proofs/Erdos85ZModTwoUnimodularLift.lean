import Proofs.Erdos85TwoAdicDeterminant
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Unimodular lifts of binary row operations

Every invertible matrix over `ZMod 2` is a product of transvections and an
invertible diagonal matrix.  Lifting each binary coefficient to its canonical
integer representative gives a matrix of determinant one over `ℤ` whose
reduction modulo two is the original matrix.
-/

namespace Erdos85

open Matrix Matrix.TransvectionStruct

noncomputable section

private theorem zmodTwo_intCast_val_local :
    ∀ x : ZMod 2, ((x.val : ℤ) : ZMod 2) = x := by
  decide

private def liftZModTwoTransvection {ι : Type*}
    (t : Matrix.TransvectionStruct ι (ZMod 2)) :
    Matrix.TransvectionStruct ι ℤ where
  i := t.i
  j := t.j
  hij := t.hij
  c := t.c.val

private theorem map_liftZModTwoTransvection
    {ι : Type*} [DecidableEq ι]
    (t : Matrix.TransvectionStruct ι (ZMod 2)) :
    (liftZModTwoTransvection t).toMatrix.map
        (Int.castRingHom (ZMod 2)) = t.toMatrix := by
  change ((1 + Matrix.single t.i t.j (t.c.val : ℤ)).map
      (Int.castRingHom (ZMod 2))) = 1 + Matrix.single t.i t.j t.c
  ext i j
  by_cases hi : t.i = i <;> by_cases hj : t.j = j <;>
    simp [Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, hi, hj, zmodTwo_intCast_val_local]

private theorem map_liftZModTwoTransvection_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι (ZMod 2))) :
    ((L.map fun t => (liftZModTwoTransvection t).toMatrix).prod.map
        (Int.castRingHom (ZMod 2))) =
      (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons, Matrix.map_mul]
      rw [map_liftZModTwoTransvection, ih]

/-- Every invertible binary matrix is the reduction of a unimodular integral
matrix.  In fact the lift constructed here has determinant exactly one. -/
theorem exists_unimodular_int_lift_zmodTwo
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι (ZMod 2)) (hQ : Q.det ≠ 0) :
    ∃ U : Matrix ι ι ℤ,
      U.det = 1 ∧ U.map (Int.castRingHom (ZMod 2)) = Q := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, L', D, hfac⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec Q
  have hDdet : (Matrix.diagonal D).det ≠ 0 := by
    intro hzero
    apply hQ
    rw [hfac, Matrix.det_mul, Matrix.det_mul, hzero]
    simp
  have hD : ∀ i, D i ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hDdet
    exact fun i => hDdet i (Finset.mem_univ i)
  have hDval : ∀ i, (D i).val = 1 := by
    intro i
    have hlt := (D i).val_lt
    have hne : (D i).val ≠ 0 := by
      intro hz
      apply hD i
      apply ZMod.val_injective
      simpa [hz]
    omega
  let UL : Matrix ι ι ℤ :=
    (L.map fun t => (liftZModTwoTransvection t).toMatrix).prod
  let UR : Matrix ι ι ℤ :=
    (L'.map fun t => (liftZModTwoTransvection t).toMatrix).prod
  let UD : Matrix ι ι ℤ := Matrix.diagonal fun i => (D i).val
  refine ⟨UL * UD * UR, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul]
    have hUL : UL.det = 1 := by
      change (L.map (Matrix.TransvectionStruct.toMatrix ∘
        liftZModTwoTransvection)).prod.det = 1
      simpa only [List.map_map] using
        Matrix.TransvectionStruct.det_toMatrix_prod
          (L.map liftZModTwoTransvection)
    have hUR : UR.det = 1 := by
      change (L'.map (Matrix.TransvectionStruct.toMatrix ∘
        liftZModTwoTransvection)).prod.det = 1
      simpa only [List.map_map] using
        Matrix.TransvectionStruct.det_toMatrix_prod
          (L'.map liftZModTwoTransvection)
    have hUD : UD.det = 1 := by
      change (Matrix.diagonal (fun i => ((D i).val : ℤ))).det = 1
      rw [Matrix.det_diagonal]
      simp [hDval]
    rw [hUL, hUD, hUR]
    norm_num
  · rw [Matrix.map_mul, Matrix.map_mul]
    have hUL : UL.map (Int.castRingHom (ZMod 2)) =
        (L.map Matrix.TransvectionStruct.toMatrix).prod := by
      exact map_liftZModTwoTransvection_prod L
    have hUR : UR.map (Int.castRingHom (ZMod 2)) =
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by
      exact map_liftZModTwoTransvection_prod L'
    have hUD : UD.map (Int.castRingHom (ZMod 2)) = Matrix.diagonal D := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [UD, zmodTwo_intCast_val_local]
      · simp [UD, hij]
    rw [hUL, hUD, hUR]
    exact hfac.symm

end

end Erdos85
