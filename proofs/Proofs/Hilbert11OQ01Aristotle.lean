/-
  Injectivity lemmas for Hilbert11 OQ-01
  These are used by Hilbert11OQ01.lean to prove the easy direction of Hasse-Minkowski.
  See Hilbert11OQ01.lean for the main formalization.

  Both theorems are proved via evaluation functionals:
  for each i : Fin n, define ev_i : A ⊗[ℚ] (Fin n → ℚ) →ₗ[ℚ] A by a ⊗ₜ w ↦ a * (w i : A).
  Then ev_i(1 ⊗ₜ v) = (v i : A), giving v i = w i from 1 ⊗ₜ v = 1 ⊗ₜ w.
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

Proved via evaluation functionals: for each i, ev_i(a ⊗ₜ w) = a * (w i : ℝ),
so ev_i(1 ⊗ₜ v) = (v i : ℝ). From 1 ⊗ₜ v = 1 ⊗ₜ w we get v i = w i for all i. -/
theorem one_tmul_injective_real (n : ℕ) :
    Function.Injective (fun v : Fin n → ℚ => (1 : ℝ) ⊗ₜ[ℚ] v) := by
  intro v w h
  funext i
  let ev : ℝ ⊗[ℚ] (Fin n → ℚ) →ₗ[ℚ] ℝ :=
    TensorProduct.lift (LinearMap.mk₂ ℚ (fun (a : ℝ) (w : Fin n → ℚ) => a * algebraMap ℚ ℝ (w i))
      (fun _ _ _ => by ring)
      (fun c _ _ => by simp only [Algebra.smul_def]; ring)
      (fun _ _ _ => by simp only [Pi.add_apply, map_add]; ring)
      (fun c _ w => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]; ring))
  have hv : ev ((1 : ℝ) ⊗ₜ[ℚ] v) = algebraMap ℚ ℝ (v i) := by
    simp only [ev, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul]
  have hw : ev ((1 : ℝ) ⊗ₜ[ℚ] w) = algebraMap ℚ ℝ (w i) := by
    simp only [ev, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul]
  have heq : algebraMap ℚ ℝ (v i) = algebraMap ℚ ℝ (w i) := by rw [← hv, ← hw, h]
  exact_mod_cast heq

/-- The canonical map v ↦ 1 ⊗ₜ v is injective for ℚ_[p] ⊗[ℚ] (Fin n → ℚ).

Same proof as for ℝ: evaluation functionals extract each coordinate. -/
theorem one_tmul_injective_padic (n : ℕ) (p : ℕ) [Fact (Nat.Prime p)] :
    Function.Injective (fun v : Fin n → ℚ => (1 : ℚ_[p]) ⊗ₜ[ℚ] v) := by
  intro v w h
  funext i
  let ev : ℚ_[p] ⊗[ℚ] (Fin n → ℚ) →ₗ[ℚ] ℚ_[p] :=
    TensorProduct.lift (LinearMap.mk₂ ℚ (fun (a : ℚ_[p]) (w : Fin n → ℚ) => a * algebraMap ℚ ℚ_[p] (w i))
      (fun _ _ _ => by ring)
      (fun c _ _ => by simp only [Algebra.smul_def]; ring)
      (fun _ _ _ => by simp only [Pi.add_apply, map_add]; ring)
      (fun c _ w => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]; ring))
  have hv : ev ((1 : ℚ_[p]) ⊗ₜ[ℚ] v) = algebraMap ℚ ℚ_[p] (v i) := by
    simp only [ev, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul]
  have hw : ev ((1 : ℚ_[p]) ⊗ₜ[ℚ] w) = algebraMap ℚ ℚ_[p] (w i) := by
    simp only [ev, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul]
  have heq : algebraMap ℚ ℚ_[p] (v i) = algebraMap ℚ ℚ_[p] (w i) := by rw [← hv, ← hw, h]
  exact_mod_cast heq

end Hilbert11OQ01Aristotle
