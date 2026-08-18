import Proofs.Erdos85MinimumLayerDesignArithmetic

/-!
# Rigidity of the minimum-layer design matrix

For an integral matrix `R`, let `sᵢ` be its row sums and set

`Bᵢⱼ = w + (if i = j then sᵢ - 3 else 0)`.

If `R² = B`, then `R` commutes with `B`.  For symmetric `R`, the `(i,j)`
entry of this commutator is `(sᵢ-sⱼ)(w-Rᵢⱼ)`.  Thus the strict entry bound
`Rᵢⱼ < w` forces all row sums to be equal.  The common row sum `s` then
satisfies `s² + 3 = |I|w + s`.
-/

namespace Erdos85

open Matrix

def minimumLayerRowSum {I : Type*} [Fintype I]
    (R : Matrix I I ℤ) (i : I) : ℤ := ∑ j, R i j

def minimumLayerDesignMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℤ) (w : ℤ) : Matrix I I ℤ :=
  fun i j ↦ w + if i = j then minimumLayerRowSum R i - 3 else 0

theorem mul_minimumLayerDesignMatrix_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℤ) (w : ℤ) (i j : I) :
    (R * minimumLayerDesignMatrix R w) i j =
      w * minimumLayerRowSum R i +
        R i j * (minimumLayerRowSum R j - 3) := by
  rw [Matrix.mul_apply]
  calc
    (∑ x, R i x * minimumLayerDesignMatrix R w x j) =
        ∑ x, (R i x * w +
          if x = j then R i x * (minimumLayerRowSum R x - 3) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [minimumLayerDesignMatrix]
      split <;> ring
    _ = (∑ x, R i x * w) +
        ∑ x, if x = j then R i x * (minimumLayerRowSum R x - 3) else 0 := by
      rw [Finset.sum_add_distrib]
    _ = w * minimumLayerRowSum R i +
        R i j * (minimumLayerRowSum R j - 3) := by
      rw [← Finset.sum_mul]
      simp [minimumLayerRowSum]
      ring

theorem minimumLayerDesignMatrix_mul_apply_of_symm
    {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℤ) (w : ℤ) (hsymm : R.IsSymm) (i j : I) :
    (minimumLayerDesignMatrix R w * R) i j =
      w * minimumLayerRowSum R j +
        (minimumLayerRowSum R i - 3) * R i j := by
  rw [Matrix.mul_apply]
  have hcol : (∑ x, R x j) = minimumLayerRowSum R j := by
    apply Finset.sum_congr rfl
    intro x hx
    exact (hsymm.apply x j).symm
  calc
    (∑ x, minimumLayerDesignMatrix R w i x * R x j) =
        ∑ x, (w * R x j +
          if i = x then (minimumLayerRowSum R i - 3) * R x j else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [minimumLayerDesignMatrix]
      split <;> ring
    _ = (∑ x, w * R x j) +
        ∑ x, if i = x then (minimumLayerRowSum R i - 3) * R x j else 0 := by
      rw [Finset.sum_add_distrib]
    _ = w * minimumLayerRowSum R j +
        (minimumLayerRowSum R i - 3) * R i j := by
      rw [← Finset.mul_sum, hcol]
      simp

/-- A symmetric design-square matrix whose entries are strictly below `w`
has constant row sum. -/
theorem minimumLayer_rowSum_eq_of_sq_eq_design
    {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℤ) (w : ℤ) (hsymm : R.IsSymm)
    (hsq : R * R = minimumLayerDesignMatrix R w)
    (hlt : ∀ i j, R i j < w) :
    ∀ i j, minimumLayerRowSum R i = minimumLayerRowSum R j := by
  have hcomm : R * minimumLayerDesignMatrix R w =
      minimumLayerDesignMatrix R w * R := by
    rw [← hsq, Matrix.mul_assoc]
  intro i j
  have hij := congrFun (congrFun hcomm i) j
  rw [mul_minimumLayerDesignMatrix_apply R w i j,
    minimumLayerDesignMatrix_mul_apply_of_symm R w hsymm i j] at hij
  have hproduct :
      (minimumLayerRowSum R i - minimumLayerRowSum R j) *
        (w - R i j) = 0 := by
    linarith
  have hpos : 0 < w - R i j := by linarith [hlt i j]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right (ne_of_gt hpos))

/-- The common row sum of a nonempty design-square matrix obeys the scalar
quadratic `s² + 3 = |I|w + s`. -/
theorem minimumLayer_design_scalar_of_constant_rowSum
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (R : Matrix I I ℤ) (w s : ℤ)
    (hsq : R * R = minimumLayerDesignMatrix R w)
    (hrow : ∀ i, minimumLayerRowSum R i = s) :
    s * s + 3 = (Fintype.card I : ℤ) * w + s := by
  classical
  let i : I := Classical.choice inferInstance
  have hsumSq := congrArg (fun A : Matrix I I ℤ ↦ ∑ j, A i j) hsq
  have hleft : (∑ j, (R * R) i j) = s * s := by
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc
      (∑ x, ∑ j, R i x * R x j) =
          ∑ x, R i x * minimumLayerRowSum R x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [minimumLayerRowSum, Finset.mul_sum]
      _ = ∑ x, R i x * s := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hrow x]
      _ = (∑ x, R i x) * s := by rw [Finset.sum_mul]
      _ = s * s := by
        rw [show (∑ x, R i x) = minimumLayerRowSum R i from rfl, hrow i]
  have hright : (∑ j, minimumLayerDesignMatrix R w i j) =
      (Fintype.card I : ℤ) * w + s - 3 := by
    calc
      _ = ∑ j, (w + if i = j then s - 3 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [minimumLayerDesignMatrix, hrow i]
      _ = (Fintype.card I : ℤ) * w + s - 3 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp
        ring
  rw [hleft, hright] at hsumSq
  linarith

end Erdos85
