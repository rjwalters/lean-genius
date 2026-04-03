/-
  Aristotle targets for Hilbert11 OQ-01
  Routine supporting lemmas for automated proof search.
  See Hilbert11OQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (Hasse-Minkowski)
  - Known results likely provable via flatness/freeness arguments
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  Main sorry targets:
  1. Injectivity of (1 ⊗ₜ ·) : (Fin n → ℚ) → A ⊗[ℚ] (Fin n → ℚ)
     when A is a flat ℚ-algebra (e.g., ℝ or ℚ_[p]).
     Follows from Module.Flat.lTensor_injective or tensor product of free modules.

  2. Same for ℚ_[p] ⊗[ℚ] (Fin n → ℚ).
-/
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.Flat.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

namespace Hilbert11OQ01Aristotle

variable {n : ℕ}

open scoped TensorProduct

/-- The canonical map v ↦ 1 ⊗ₜ v is injective for ℝ ⊗[ℚ] (Fin n → ℚ).

ℝ is flat over ℚ (in fact, ℝ is a flat ℚ-algebra since ℚ is a field and every
module over a field is flat). Therefore the map (1 ⊗ₜ ·) is injective.

Used in: Hilbert11OQ01.rational_implies_real_isotropic -/
theorem one_tmul_injective_real (n : ℕ) :
    Function.Injective (fun v : Fin n → ℚ => (1 : ℝ) ⊗ₜ[ℚ] v) := by
  sorry

/-- The canonical map v ↦ 1 ⊗ₜ v is injective for ℚ_[p] ⊗[ℚ] (Fin n → ℚ).

ℚ_[p] is flat over ℚ (same reason: ℚ is a field). -/
theorem one_tmul_injective_padic (n : ℕ) (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (fun v : Fin n → ℚ => (1 : ℚ_[p]) ⊗ₜ[ℚ] v) := by
  sorry

end Hilbert11OQ01Aristotle
