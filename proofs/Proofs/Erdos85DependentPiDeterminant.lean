import Proofs.Erdos85OrderSixtyFourComponentMeanZeroEquiv

/-! # Determinant of a dependent product endomorphism -/

namespace Erdos85

noncomputable section

/-- The determinant of a componentwise endomorphism on a finite dependent
product is the product of the component determinants.  Mathlib's
`LinearMap.det_pi` treats the homogeneous special case; this is the dependent
version needed when connected components have different orders. -/
theorem LinearMap.det_dependent_pi
    {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]
    (f : ∀ i, M i →ₗ[R] M i) :
    LinearMap.det
        (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
      ∏ i, LinearMap.det (f i) := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  let B := Pi.basis b
  simp_rw [← LinearMap.det_toMatrix B,
    ← LinearMap.det_toMatrix (b _)]
  have hmatrix :
      LinearMap.toMatrix B B
          (LinearMap.pi (fun i => (f i).comp (LinearMap.proj i))) =
        Matrix.blockDiagonal'
          (fun i => LinearMap.toMatrix (b i) (b i) (f i)) := by
    ext ⟨i, a⟩ ⟨j, d⟩
    by_cases hij : i = j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq, LinearMap.toMatrix_apply']
      unfold B
      simp only [Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.coe_proj, Function.eval, Pi.basis_apply]
      simp
      rw [LinearMap.toMatrix_apply']
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hij,
        LinearMap.toMatrix_apply']
      unfold B
      simp only [Pi.basis_repr, LinearMap.pi_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.coe_proj, Function.eval, Pi.basis_apply]
      simp [hij]
  rw [hmatrix]
  exact RationalCanonicalFormExists.RCF.det_blockDiagonal' _

end

end Erdos85
