import Proofs.Erdos85RationalPrimaryTraceSplit
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Real spectrum of a symmetric primary restriction

For a symmetric real operator commuting with `T`, every polynomial primary
sector of `T` is invariant.  The symmetric spectral theorem therefore gives a
complete eigenvector family on that sector, indexed by its dimension, and the
sector trace is the sum of those eigenvalues with multiplicity.
-/

open Polynomial
open scoped InnerProductSpace

namespace Erdos85

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A symmetric operator has a complete multiplicity-aware real eigenfamily
on every primary sector of a commuting operator.  The vectors are stated in
the ambient space so the result can feed graph eigenvalue bounds directly. -/
theorem exists_eigenfamily_on_ker_aeval_of_symmetric_commute
    (S T : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (hcomm : S * T = T * S)
    (p : ℝ[X]) :
    ∃ (θ : Fin (Module.finrank ℝ (LinearMap.ker (aeval T p))) → ℝ)
      (w : Fin (Module.finrank ℝ (LinearMap.ker (aeval T p))) → E),
      (∀ i, w i ≠ 0) ∧
      (∀ i, w i ∈ LinearMap.ker (aeval T p)) ∧
      (∀ i, S (w i) = θ i • w i) ∧
      LinearMap.trace ℝ (LinearMap.ker (aeval T p))
          (kerAevalRestrict S T hcomm p) = ∑ i, θ i := by
  let R := kerAevalRestrict S T hcomm p
  have hR : R.IsSymmetric :=
    hS.restrict_invariant (mapsTo_ker_aeval_of_commute S T hcomm p)
  let b := hR.eigenvectorBasis rfl
  let θ := hR.eigenvalues rfl
  refine ⟨θ, fun i ↦ (b i : E), ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact (b.toBasis.ne_zero i) (Subtype.ext hi)
  · intro i
    exact (b i).property
  · intro i
    have hi := hR.apply_eigenvectorBasis rfl i
    exact congrArg Subtype.val hi
  · change LinearMap.trace ℝ _ R = _
    have hb : ∀ i, R (b i) = θ i • b i := hR.apply_eigenvectorBasis rfl
    have hb' : ∀ i, R (b.toBasis i) = θ i • b.toBasis i := by
      intro i
      simpa using hb i
    rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply,
      hb', map_smul, Finsupp.smul_apply,
      Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]

/-- Under the sector identity `S² = κI - T`, the eigenbasis supplied above is
automatically a simultaneous eigenfamily for `T`, with eigenvalue
`κ - θᵢ²`.  Thus no separate simultaneous-diagonalisation theorem is needed. -/
theorem exists_paired_eigenfamily_on_ker_aeval_of_symmetric_commute
    (S T : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (hcomm : S * T = T * S)
    (p : ℝ[X]) (κ : ℝ)
    (hsq : ∀ v ∈ LinearMap.ker (aeval T p),
      S (S v) = κ • v - T v) :
    ∃ (θ : Fin (Module.finrank ℝ (LinearMap.ker (aeval T p))) → ℝ)
      (w : Fin (Module.finrank ℝ (LinearMap.ker (aeval T p))) → E),
      (∀ i, w i ≠ 0) ∧
      (∀ i, S (w i) = θ i • w i) ∧
      (∀ i, T (w i) = (κ - (θ i) ^ 2) • w i) ∧
      LinearMap.trace ℝ (LinearMap.ker (aeval T p))
          (kerAevalRestrict S T hcomm p) = ∑ i, θ i := by
  obtain ⟨θ, w, hw, hwmem, heigen, htrace⟩ :=
    exists_eigenfamily_on_ker_aeval_of_symmetric_commute S T hS hcomm p
  refine ⟨θ, w, hw, heigen, ?_, htrace⟩
  intro i
  have hi := hsq (w i) (hwmem i)
  rw [heigen i, map_smul, heigen i] at hi
  rw [sub_smul, pow_two, mul_smul]
  apply (eq_sub_iff_add_eq).2
  simpa [add_comm] using (eq_sub_iff_add_eq.mp hi)

#print axioms exists_eigenfamily_on_ker_aeval_of_symmetric_commute
#print axioms exists_paired_eigenfamily_on_ker_aeval_of_symmetric_commute

end

end Erdos85
