import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Projection matrix of an eight-element equivalence partition -/

namespace Erdos85

noncomputable section

/-- The `0/1` matrix indicating that two indices lie in the same class. -/
def relationClassMatrix
    {V : Type*} [Fintype V] (r : V → V → Prop) [DecidableRel r] :
    Matrix V V ℚ := fun x y => if r x y then 1 else 0

/-- If every class of an equivalence relation has eight elements, its class
matrix squares to eight times itself.  This is the exact projection identity
needed for the two sides of each `K_{8,8}`-minus-matching component. -/
theorem relationClassMatrix_mul_self_eq_eight
    {V : Type*} [Fintype V]
    (r : V → V → Prop) [DecidableRel r]
    (hsymm : ∀ {x y}, r x y → r y x)
    (htrans : ∀ {x y z}, r x y → r y z → r x z)
    (hcard : ∀ x,
      ((Finset.univ : Finset V).filter fun y => r x y).card = 8) :
    relationClassMatrix r * relationClassMatrix r =
      (8 : ℚ) • relationClassMatrix r := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [relationClassMatrix, Matrix.smul_apply, smul_eq_mul]
  by_cases hxy : r x y
  · calc
      (∑ z, (if r x z then 1 else 0) * if r z y then 1 else 0) =
          ∑ z, if r x z then (1 : ℚ) else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hxz : r x z
        · have hzy : r z y := htrans (hsymm hxz) hxy
          simp [hxz, hzy]
        · simp [hxz]
      _ = (((Finset.univ : Finset V).filter fun z => r x z).card : ℚ) := by simp
      _ = 8 := by rw [hcard x]; norm_num
      _ = (8 : ℚ) * (if r x y then (1 : ℚ) else 0) := by simp [hxy]
  · calc
      (∑ z, (if r x z then 1 else 0) * if r z y then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        by_cases hxz : r x z
        · have hnzy : ¬ r z y := fun hzy => hxy (htrans hxz hzy)
          simp [hxz, hnzy]
        · simp [hxz]
      _ = (8 : ℚ) * (if r x y then (1 : ℚ) else 0) := by simp [hxy]

/-- Entrywise degree/codegree data packages into the other projection
identity.  Diagonal entries are seven, distinct vertices in one class have
codegree six, and vertices in different classes have codegree zero. -/
theorem matrix_sq_eq_one_add_six_relationClassMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : Matrix V V ℚ)
    (r : V → V → Prop) [DecidableRel r]
    (hrefl : ∀ x, r x x)
    (hdiag : ∀ x, (D * D) x x = 7)
    (hsame : ∀ {x y}, x ≠ y → r x y → (D * D) x y = 6)
    (hdiff : ∀ {x y}, ¬ r x y → (D * D) x y = 0) :
    D * D = 1 + (6 : ℚ) • relationClassMatrix r := by
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, relationClassMatrix,
    Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    rw [hdiag]
    simp [hrefl]
    norm_num
  · by_cases hr : r x y
    · rw [hsame hxy hr]
      simp [hxy, hr]
    · rw [hdiff hr]
      simp [hxy, hr]

end

end Erdos85
