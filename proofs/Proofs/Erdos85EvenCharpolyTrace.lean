import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Polynomial.Expand

/-!
# Trace obstruction from an even characteristic polynomial

The degree-twelve second-order exception reduces to showing that the
characteristic polynomial on a 132-dimensional invariant complement is a
polynomial in `X²`.  This file records the final reusable trace step.
-/

namespace Erdos85

open Polynomial

/-- In even dimension, a matrix whose characteristic polynomial is a
polynomial in `X²` has trace zero. -/
theorem Matrix.trace_eq_zero_of_charpoly_eq_expand_two
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℚ) (p : ℚ[X])
    (hchar : A.charpoly = Polynomial.expand ℚ 2 p)
    (hdim : Even (Fintype.card ι)) :
    A.trace = 0 := by
  have hcardpos : 0 < Fintype.card ι := Fintype.card_pos
  have hodd : ¬2 ∣ Fintype.card ι - 1 := by
    obtain ⟨k, hk⟩ := hdim
    intro hdvd
    obtain ⟨j, hj⟩ := hdvd
    omega
  rw [Matrix.trace_eq_neg_charpoly_coeff, hchar,
    Polynomial.coeff_expand (by norm_num : 0 < 2)]
  simp [hodd]

/-- Endomorphism form of the even-characteristic-polynomial trace
obstruction. -/
theorem LinearMap.trace_eq_zero_of_charpoly_eq_expand_two
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (f : E →ₗ[ℚ] E) (p : ℚ[X])
    (hchar : f.charpoly = Polynomial.expand ℚ 2 p)
    (hpos : 0 < Module.finrank ℚ E)
    (hdim : Even (Module.finrank ℚ E)) :
    LinearMap.trace ℚ E f = 0 := by
  let b := Module.Free.chooseBasis ℚ E
  have hcard : Module.finrank ℚ E =
      Fintype.card (Module.Free.ChooseBasisIndex ℚ E) :=
    Module.finrank_eq_card_chooseBasisIndex ℚ E
  letI : Nonempty (Module.Free.ChooseBasisIndex ℚ E) :=
    Fintype.card_pos_iff.mp (hcard ▸ hpos)
  rw [LinearMap.trace_eq_matrix_trace ℚ b]
  apply Matrix.trace_eq_zero_of_charpoly_eq_expand_two
    (LinearMap.toMatrix b b f) p
  · rw [LinearMap.charpoly_toMatrix]
    exact hchar
  · rwa [← hcard]

end Erdos85
