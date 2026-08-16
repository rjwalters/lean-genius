import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Lifting a positive eigenvalue of an operator square
-/

namespace Erdos85

theorem hasEigenvalue_sqrt_or_neg_sqrt_of_sq
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (T : Module.End ℝ E) {mu : ℝ}
    (hmu : (T ^ 2).HasEigenvalue mu) (hmupos : 0 < mu) :
    T.HasEigenvalue (Real.sqrt mu) ∨
      T.HasEigenvalue (-Real.sqrt mu) := by
  obtain ⟨v, hv⟩ := hmu.exists_hasEigenvector
  let s := Real.sqrt mu
  have hspos : 0 < s := Real.sqrt_pos.2 hmupos
  have hs : s ^ 2 = mu := Real.sq_sqrt hmupos.le
  have hs' : s * s = mu := by simpa [pow_two] using hs
  have hTv : T (T v) = mu • v := by
    simpa [pow_two, Module.End.mul_apply] using hv.apply_eq_smul
  let w := T v + s • v
  have hTw : T w = s • w := by
    dsimp [w]
    rw [map_add, map_smul, hTv]
    rw [smul_add, smul_smul, hs']
    module
  by_cases hw : w = 0
  · right
    apply Module.End.hasEigenvalue_of_hasEigenvector
    refine Module.End.hasEigenvector_iff.mpr ⟨?_, hv.2⟩
    rw [Module.End.mem_eigenspace_iff]
    have hw' : T v + s • v = 0 := by simpa [w] using hw
    calc
      T v = -(s • v) := eq_neg_of_add_eq_zero_left hw'
      _ = (-s) • v := by rw [neg_smul]
  · left
    apply Module.End.hasEigenvalue_of_hasEigenvector
    exact Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr hTw, hw⟩

end Erdos85
