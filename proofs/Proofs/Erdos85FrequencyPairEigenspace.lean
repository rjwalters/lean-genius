import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Frequency-pair eigenspace bridge: abstract operator layer

For matrices `A`, `D`, `J` over a field with `A * D = D * A`,
`A * A = κ • 1 + J - D`, and `J * D = 2 • J`, every eigenspace of `D` at
an eigenvalue `μ ≠ 2` is invariant under `A`, the matrix `J` annihilates
that eigenspace, and the restriction `T` of `A` to it satisfies
`T * T = (κ - μ) • id`.

This is the operator half of the frequency-pair bridge for the equal-cycle
extremal graph of Erdős problem 85: there `A` is the adjacency matrix, `D`
the second-order defect two-factor of
`adjMatrix_sq_eq_sub_secondOrderDefect_of_even`, `J` the all-ones matrix,
`κ = d - 1`, and `μ = ζ + ζ⁻¹` for a prime-order root of unity `ζ`.  No
cycle structure is needed at this level: the two-regularity of the defect
graph enters only through the column-sum identity `J * D = 2 • J`.
-/

namespace Erdos85

noncomputable section

open Module

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V]

/-- The eigenspace of a defect operator at frequency eigenvalue `μ`. -/
def defectEigenspace (D : Matrix V V K) (μ : K) : Submodule K (V → K) :=
  Module.End.eigenspace (Matrix.toLin' D) μ

theorem mem_defectEigenspace_iff {D : Matrix V V K} {μ : K} {v : V → K} :
    v ∈ defectEigenspace D μ ↔ D.mulVec v = μ • v := by
  rw [defectEigenspace, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

/-- `J` annihilates every `μ`-eigenvector of a defect operator whose column
sum is the scalar `δ`, provided `μ ≠ δ`.  This is the excess-uniform form of
the frequency-pair annihilation lemma: at positive excess the defect graph
has degree `δ = e + 2`, rather than degree two. -/
theorem mulVec_eq_zero_of_mem_defectEigenspace_of_scalar
    {D J : Matrix V V K} {δ : K} (hJD : J * D = δ • J)
    {μ : K} (hμ : μ ≠ δ) {v : V → K}
    (hv : v ∈ defectEigenspace D μ) :
    J.mulVec v = 0 := by
  have hDv : D.mulVec v = μ • v := mem_defectEigenspace_iff.mp hv
  have h1 : J.mulVec (D.mulVec v) = μ • J.mulVec v := by
    rw [hDv, Matrix.mulVec_smul]
  have h2 : J.mulVec (D.mulVec v) = δ • J.mulVec v := by
    rw [Matrix.mulVec_mulVec, hJD, Matrix.smul_mulVec]
  have h3 : (μ - δ) • J.mulVec v = 0 := by
    rw [sub_smul, h1.symm.trans h2, sub_self]
  have h4 := congrArg (fun w ↦ (μ - δ)⁻¹ • w) h3
  simpa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hμ)] using h4

/-- `J` annihilates every `μ`-eigenvector of `D` with `μ ≠ 2` as soon as
`J * D = 2 • J`: composing the eigen-equation with `J` forces
`(μ - 2) • (J v) = 0`. -/
theorem mulVec_eq_zero_of_mem_defectEigenspace
    {D J : Matrix V V K} (hJD : J * D = (2 : K) • J)
    {μ : K} (hμ : μ ≠ 2) {v : V → K}
    (hv : v ∈ defectEigenspace D μ) :
    J.mulVec v = 0 := by
  exact mulVec_eq_zero_of_mem_defectEigenspace_of_scalar hJD hμ hv

/-- Commutation `A * D = D * A` makes every defect eigenspace
`A`-invariant. -/
theorem mulVec_mem_defectEigenspace
    {A D : Matrix V V K} (hcomm : A * D = D * A)
    {μ : K} {v : V → K} (hv : v ∈ defectEigenspace D μ) :
    A.mulVec v ∈ defectEigenspace D μ := by
  rw [mem_defectEigenspace_iff] at hv ⊢
  calc
    D.mulVec (A.mulVec v) = (D * A).mulVec v := by
      rw [Matrix.mulVec_mulVec]
    _ = (A * D).mulVec v := by rw [hcomm]
    _ = A.mulVec (D.mulVec v) := by rw [Matrix.mulVec_mulVec]
    _ = A.mulVec (μ • v) := by rw [hv]
    _ = μ • A.mulVec v := by rw [Matrix.mulVec_smul]

/-- The restriction `T` of the adjacency operator to the frequency
eigenspace of a commuting defect operator. -/
def defectEigenspaceRestrict (A : Matrix V V K) {D : Matrix V V K}
    (hcomm : A * D = D * A) (μ : K) :
    defectEigenspace D μ →ₗ[K] defectEigenspace D μ :=
  (Matrix.toLin' A).restrict fun v hv ↦ by
    rw [Matrix.toLin'_apply]
    exact mulVec_mem_defectEigenspace hcomm hv

@[simp] theorem defectEigenspaceRestrict_coe (A : Matrix V V K)
    {D : Matrix V V K} (hcomm : A * D = D * A) (μ : K)
    (v : defectEigenspace D μ) :
    (defectEigenspaceRestrict A hcomm μ v : V → K) =
      A.mulVec (v : V → K) := by
  rw [defectEigenspaceRestrict, LinearMap.coe_restrict_apply,
    Matrix.toLin'_apply]

/-- **Frequency-pair square identity.**  On the `μ`-eigenspace of the
defect operator, the square of the restricted adjacency operator is the
scalar `κ - μ`: the all-ones summand of `A * A = κ • 1 + J - D` dies on
the eigenspace and the defect summand acts as `μ`. -/
theorem defectEigenspaceRestrict_sq
    {A D J : Matrix V V K} {κ μ : K}
    (hcomm : A * D = D * A)
    (hsq : A * A = κ • (1 : Matrix V V K) + J - D)
    (hJD : J * D = (2 : K) • J) (hμ : μ ≠ 2) :
    defectEigenspaceRestrict A hcomm μ * defectEigenspaceRestrict A hcomm μ =
      (κ - μ) • LinearMap.id := by
  refine LinearMap.ext fun v ↦ Subtype.ext ?_
  have hJv : J.mulVec (v : V → K) = 0 :=
    mulVec_eq_zero_of_mem_defectEigenspace hJD hμ v.2
  have hDv : D.mulVec (v : V → K) = μ • (v : V → K) :=
    mem_defectEigenspace_iff.mp v.2
  have hcoe :
      (((defectEigenspaceRestrict A hcomm μ *
          defectEigenspaceRestrict A hcomm μ) v : defectEigenspace D μ) :
        V → K) = (A * A).mulVec (v : V → K) := by
    rw [Module.End.mul_apply, defectEigenspaceRestrict_coe,
      defectEigenspaceRestrict_coe, Matrix.mulVec_mulVec]
  rw [hcoe, hsq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hJv, hDv]
  simp [sub_smul]

/-- **Excess-uniform defect-eigenspace square identity.**  If the defect
operator has column sum `δ`, then on every nonprincipal `μ`-eigenspace its
commuting adjacency restriction squares to `κ - μ`.  No two-factor or cycle
decomposition is used. -/
theorem defectEigenspaceRestrict_sq_of_scalar
    {A D J : Matrix V V K} {κ μ δ : K}
    (hcomm : A * D = D * A)
    (hsq : A * A = κ • (1 : Matrix V V K) + J - D)
    (hJD : J * D = δ • J) (hμ : μ ≠ δ) :
    defectEigenspaceRestrict A hcomm μ * defectEigenspaceRestrict A hcomm μ =
      (κ - μ) • LinearMap.id := by
  refine LinearMap.ext fun v ↦ Subtype.ext ?_
  have hJv : J.mulVec (v : V → K) = 0 :=
    mulVec_eq_zero_of_mem_defectEigenspace_of_scalar hJD hμ v.2
  have hDv : D.mulVec (v : V → K) = μ • (v : V → K) :=
    mem_defectEigenspace_iff.mp v.2
  have hcoe :
      (((defectEigenspaceRestrict A hcomm μ *
          defectEigenspaceRestrict A hcomm μ) v : defectEigenspace D μ) :
        V → K) = (A * A).mulVec (v : V → K) := by
    rw [Module.End.mul_apply, defectEigenspaceRestrict_coe,
      defectEigenspaceRestrict_coe, Matrix.mulVec_mulVec]
  rw [hcoe, hsq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, hJv, hDv]
  simp [sub_smul]

end

end Erdos85
