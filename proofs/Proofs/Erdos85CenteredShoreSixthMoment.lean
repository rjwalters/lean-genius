import Proofs.Erdos85EightEightCenteredCharpoly
import Proofs.Erdos85QuadraticFactorRootMoments

/-! # Sixth moment of the centered `C8 ⊔ C8` shore factor -/

open SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

private theorem complexRootPowerSum_X_sub_C_six (a : ℂ) :
    complexRootPowerSum (X - C a) 6 = a ^ 6 := by
  rw [complexRootPowerSum, roots_X_sub_C]
  simp

theorem complexRootPowerSum_quadratic_six (d : ℂ) :
    complexRootPowerSum (X ^ 2 - C d) 6 = 2 * d ^ 3 := by
  rw [complexRootPowerSum]
  let r := (X ^ 2 - C d).roots
  have hr : r.card = 2 := by
    dsimp [r]
    have hs : Polynomial.Splits (X ^ 2 - C d) := IsAlgClosed.splits _
    rw [← hs.natDegree_eq_card_roots]
    exact ((isMonicOfDegree_X_pow ℂ 2).sub (by simp)).natDegree_eq
  have hroot : ∀ z ∈ r, z ^ 6 = d ^ 3 := by
    intro z hz
    have hz0 :=
      (mem_roots (X_pow_sub_C_ne_zero (R := ℂ) (by norm_num) d)).mp hz
    have hz2 : z ^ 2 = d :=
      sub_eq_zero.mp (by simpa [IsRoot.def] using hz0)
    rw [show z ^ 6 = (z ^ 2) ^ 3 by ring, hz2]
  change (r.map fun z => z ^ 6).sum = _
  have hmap : r.map (fun z => z ^ 6) = r.map (fun _z => d ^ 3) :=
    Multiset.map_congr rfl hroot
  rw [hmap]
  simp [hr]
  ring

/-- The explicit centered shore factor contributes exactly `46912` to the
sixth spectral moment. -/
theorem h305CenteredServiceFactor_complexRootPowerSum_six :
    complexRootPowerSum
      ((X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
        (X - C (2 : ℂ)) ^ 2 * X ^ 4 *
        (X ^ 2 - C (2 : ℂ)) ^ 4) 6 = 46912 := by
  have h6 : (X - C (6 : ℂ)) ≠ 0 := (monic_X_sub_C 6).ne_zero
  have hm2 : (X - C (-2 : ℂ)) ≠ 0 := (monic_X_sub_C (-2)).ne_zero
  have h2 : (X - C (2 : ℂ)) ^ 2 ≠ 0 :=
    ((monic_X_sub_C 2).pow 2).ne_zero
  have h0 : (X : ℂ[X]) ^ 4 ≠ 0 := (monic_X.pow 4).ne_zero
  have hq : (X ^ 2 - C (2 : ℂ)) ^ 4 ≠ 0 :=
    (((isMonicOfDegree_X_pow ℂ 2).sub (by simp)).pow 4).ne_zero
  have h6m2 : (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) ≠ 0 :=
    ((monic_X_sub_C 6).mul (monic_X_sub_C (-2))).ne_zero
  have h6m2two :
      (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
        (X - C (2 : ℂ)) ^ 2 ≠ 0 :=
    (((monic_X_sub_C 6).mul (monic_X_sub_C (-2))).mul
      ((monic_X_sub_C 2).pow 2)).ne_zero
  have hprefix :
      (X - C (6 : ℂ)) * (X - C (-2 : ℂ)) *
        (X - C (2 : ℂ)) ^ 2 * X ^ 4 ≠ 0 :=
    ((((monic_X_sub_C 6).mul (monic_X_sub_C (-2))).mul
      ((monic_X_sub_C 2).pow 2)).mul (monic_X.pow 4)).ne_zero
  have hlin6 := complexRootPowerSum_X_sub_C_six (6 : ℂ)
  have hlinm2 := complexRootPowerSum_X_sub_C_six (-2 : ℂ)
  have hlin2 := complexRootPowerSum_X_sub_C_six (2 : ℂ)
  have hX : complexRootPowerSum (X : ℂ[X]) 6 = 0 := by
    rw [complexRootPowerSum, roots_X]
    simp
  have hquad := complexRootPowerSum_quadratic_six (2 : ℂ)
  rw [complexRootPowerSum_mul
        hprefix hq,
      complexRootPowerSum_mul h6m2two h0,
      complexRootPowerSum_mul h6m2 h2,
      complexRootPowerSum_mul h6 hm2,
      complexRootPowerSum_pow,
      complexRootPowerSum_pow,
      complexRootPowerSum_pow,
      hlin6, hlinm2, hlin2, hX, hquad]
  norm_num

/-- Matrix-facing form: two labeled eight-cycles have centered sixth trace
`46912`. -/
theorem eightEight_centeredShore_trace_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))}) :
    let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
    Matrix.trace (B ^ 6) = 46912 := by
  dsimp only
  let B := (2 : ℂ)⁻¹ • edgeIndexedVertexOnesMatrix V - H.adjMatrix ℂ
  have hchar := eightEight_centeredCharpoly_eq_integerFactor
    H e hleft hright
  have hmoment := complexRootPowerSum_charpoly_eq_trace_pow
    B (by
      apply Matrix.IsHermitian.ext
      intro i j
      simp [B, edgeIndexedVertexOnesMatrix,
        SimpleGraph.adjMatrix_apply, H.adj_comm]) 6
  rw [hchar] at hmoment
  exact hmoment.symm.trans h305CenteredServiceFactor_complexRootPowerSum_six

end

end Erdos85

#print axioms Erdos85.h305CenteredServiceFactor_complexRootPowerSum_six
#print axioms Erdos85.eightEight_centeredShore_trace_six
