import Mathlib

/-!
# Rational characteristic roots and trace

This packages the base-change bridge needed to read a rational primary-sector
trace as the sum of the complex roots of its characteristic polynomial, with
algebraic multiplicity.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- The first complex-root power sum of a rational endomorphism's
characteristic polynomial is its rational trace, cast to `ℂ`. -/
theorem sum_roots_map_charpoly_eq_trace
    {E : Type*} [AddCommGroup E] [Module ℚ E]
    [Module.Free ℚ E] [Module.Finite ℚ E]
    (f : E →ₗ[ℚ] E) :
    (f.charpoly.map (algebraMap ℚ ℂ)).roots.sum =
      (LinearMap.trace ℚ E f : ℂ) := by
  let fC := f.baseChange ℂ
  let ι := Module.Free.ChooseBasisIndex ℂ (TensorProduct ℚ ℂ E)
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  let b : Module.Basis ι ℂ (TensorProduct ℚ ℂ E) :=
    Module.Free.chooseBasis ℂ (TensorProduct ℚ ℂ E)
  calc
    (f.charpoly.map (algebraMap ℚ ℂ)).roots.sum =
        fC.charpoly.roots.sum := by
      rw [LinearMap.charpoly_baseChange]
    _ = Matrix.trace (LinearMap.toMatrix b b fC) := by
      rw [← fC.charpoly_toMatrix b]
      exact (Matrix.trace_eq_sum_roots_charpoly _).symm
    _ = LinearMap.trace ℂ (TensorProduct ℚ ℂ E) fC := by
      rw [LinearMap.trace_eq_matrix_trace ℂ b]
    _ = (LinearMap.trace ℚ E f : ℂ) := by
      exact LinearMap.trace_baseChange f ℂ

#print axioms sum_roots_map_charpoly_eq_trace

end

end Erdos85
