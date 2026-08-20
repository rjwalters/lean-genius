import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Eigenvalue transfer across a complement partition -/

open Finset Matrix

namespace Erdos85

/-- If three zero-diagonal relations partition every off-diagonal pair,
then a zero-sum common eigenvector for two relations is automatically an
eigenvector for the third.  Its eigenvalue is the complementary
`-1-mu-nu`.  This is the algebra behind the connected-C16 identity
`K + R + C16²_offdiag = J-I`. -/
theorem complementPartition_signedEigenvalue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K R Q : Matrix ι ι ℤ) (s : ι → ℤ) (mu nu : ℤ)
    (hpart : ∀ i j, K i j + R i j + Q i j = if i = j then 0 else 1)
    (hsum : ∑ i, s i = 0)
    (hK : K.mulVec s = fun i ↦ mu * s i)
    (hQ : Q.mulVec s = fun i ↦ nu * s i) :
    R.mulVec s = fun i ↦ (-1 - mu - nu) * s i := by
  funext i
  have hoff : ∑ j, (if i = j then (0 : ℤ) else 1) * s j = -s i := by
    simp only [ite_mul, zero_mul, one_mul]
    calc
      (∑ j, if i = j then 0 else s j) =
          ∑ j ∈ (Finset.univ.erase i), s j := by
        rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : i = j <;> simp [h, Ne.symm]
      _ = (∑ j, s j) - s i := by
        have h := Finset.sum_erase_add Finset.univ s (Finset.mem_univ i)
        omega
      _ = -s i := by rw [hsum]; ring
  have hKi : K.mulVec s i = mu * s i := congrFun hK i
  have hQi : Q.mulVec s i = nu * s i := congrFun hQ i
  change ∑ j, R i j * s j = _
  calc
    _ = ∑ j, ((if i = j then (0 : ℤ) else 1) - K i j - Q i j) * s j := by
      apply Finset.sum_congr rfl
      intro j _
      have hp := hpart i j
      rw [← hp]
      ring
    _ = (∑ j, (if i = j then (0 : ℤ) else 1) * s j) -
          (∑ j, K i j * s j) - ∑ j, Q i j * s j := by
      simp only [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = -s i - K.mulVec s i - Q.mulVec s i := by
      rw [hoff]
      rfl
    _ = (-1 - mu - nu) * s i := by rw [hKi, hQi]; ring

end Erdos85

#print axioms Erdos85.complementPartition_signedEigenvalue
