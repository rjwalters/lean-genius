import Proofs.Erdos85MinimumLayerDesignMatrix

/-!
# The minimum-layer quotient as a lattice similarity

On the zero-sum lattice, the rank-one part of the design square vanishes.
The restricted quotient therefore squares to the scalar `s - 3`; symmetry
then says that it scales the standard inner product by `s - 3`.  This is the
entry point for Bruck--Ryser--Chowla and local Hilbert-symbol obstructions.
-/

namespace Erdos85

open Matrix

/-- The design matrix acts quadratically as `s - 3` on zero-sum vectors. -/
theorem minimumLayer_mulVec_sq_of_sum_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℤ) (w s : ℤ)
    (hsq : R * R = minimumLayerDesignMatrix R w)
    (hrow : ∀ i, minimumLayerRowSum R i = s)
    (x : I → ℤ) (hx : ∑ i, x i = 0) :
    R *ᵥ (R *ᵥ x) = (s - 3) • x := by
  rw [Matrix.mulVec_mulVec x R R, hsq]
  funext i
  simp only [minimumLayerDesignMatrix, Matrix.mulVec, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  calc
    (∑ j, (w + if i = j then minimumLayerRowSum R i - 3 else 0) * x j) =
        w * (∑ j, x j) + (minimumLayerRowSum R i - 3) * x i := by
      rw [Finset.mul_sum]
      simp only [add_mul, Finset.sum_add_distrib]
      simp
    _ = (s - 3) * x i := by rw [hx, hrow i]; ring

/-- A symmetric design quotient is an integral similarity of multiplier
`s - 3` on the zero-sum lattice. -/
theorem minimumLayer_dotProduct_mulVec_of_sum_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (R : Matrix I I ℤ) (w s : ℤ)
    (hsymm : R.IsSymm)
    (hsq : R * R = minimumLayerDesignMatrix R w)
    (hrow : ∀ i, minimumLayerRowSum R i = s)
    (x y : I → ℤ) (hx : ∑ i, x i = 0) :
    (R *ᵥ x) ⬝ᵥ (R *ᵥ y) = (s - 3) * (x ⬝ᵥ y) := by
  rw [Matrix.dotProduct_mulVec]
  let v := R *ᵥ x
  have hvec : v ᵥ* R = R *ᵥ v := by
    calc
      v ᵥ* R = v ᵥ* Rᵀ := congrArg (fun A ↦ v ᵥ* A) hsymm.symm
      _ = R *ᵥ v := Matrix.vecMul_transpose R v
  change v ᵥ* R ⬝ᵥ y = _
  rw [hvec]
  change R *ᵥ (R *ᵥ x) ⬝ᵥ y = _
  rw [minimumLayer_mulVec_sq_of_sum_zero R w s hsq hrow x hx]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, (s - 3) * x i * y i) = ∑ i, (s - 3) * (x i * y i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (s - 3) * ∑ i, x i * y i := by rw [Finset.mul_sum]

end Erdos85
