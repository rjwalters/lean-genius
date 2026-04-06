/-
  Aristotle targets for Hilbert11OQ01OQ01 (Meyer's Theorem / Real Isotropy Criterion)
  Routine supporting lemmas for automated proof search.
  See Hilbert11OQ01OQ01.lean for the main formalization.

  Two sorry targets: both prove that a quadratic form is IsIsotropicOverReals
  given sign-change hypotheses. The proofs use:
  1. `baseChange_real_tmul`: Q.baseChange ℝ (r ⊗ₜ v) = Q v • (r * r)
  2. Casting from ℚ to ℝ: `Q v • (1:ℝ) = (Q v : ℝ)` when r = 1
  3. The Intermediate Value Theorem for continuous functions

  TARGET ANALYSIS:

  real_isotropic_of_sign_change:
    Given Q.baseChange ℝ (1⊗v) < 0 and Q.baseChange ℝ (1⊗w) > 0,
    find a nonzero zero of Q.baseChange ℝ.
    Strategy: IVT on f(t) = Q.baseChange ℝ (t • (1⊗v) + (1-t) • (1⊗w)).
    f is continuous (quadratic form), f(1) < 0, f(0) > 0.
    By IVT, ∃ t₀ ∈ (0,1), f(t₀) = 0.
    The vector t₀ • (1⊗v) + (1-t₀) • (1⊗w) is nonzero (endpoints give nonzero value,
    so the form doesn't vanish at v or w; strict interior IVT avoids endpoint issues).

  real_isotropic_of_rational_sign_change:
    Simpler: Q v < 0 and Q w > 0 in ℚ.
    Step 1: Q.baseChange ℝ (1⊗v) = (Q v : ℝ) < 0  (via baseChange_real_tmul + cast)
    Step 2: Q.baseChange ℝ (1⊗w) = (Q w : ℝ) > 0  (similarly)
    Step 3: Apply real_isotropic_of_sign_change.

  Excluded:
  - padic_five_var_isotropic: axiom in main file
  - hasse_minkowski_refined: axiom in parent file
  - meyer_theorem, meyer_five_vars: proved theorems using the axioms

  Pre-submission checks: no def-sorries, no axioms, no True placeholders, no docstring sections
-/
import Proofs.Hilbert11OQ01
import Proofs.Hilbert11OQ01OQ01
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

namespace Hilbert11OQ01OQ01Aristotle

open Hilbert11OQ01 Hilbert11OQ01OQ01
open scoped TensorProduct

variable {n : ℕ}

/-
TARGET 1 (helper — proved)
Base change of Q at (1 ⊗ₜ v) equals the rational value cast to ℝ.

Q.baseChange ℝ ((1:ℝ) ⊗ₜ[ℚ] v) = Q v • ((1:ℝ) * (1:ℝ)) = Q v • 1 = (Q v : ℝ)

This uses `baseChange_real_tmul` from Hilbert11OQ01, then `smul_one` and algebraMap.
-/
theorem baseChange_one_tmul_eq (Q : QuadraticForm ℚ (Fin n → ℚ))
    (v : Fin n → ℚ) :
    Q.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] v) = algebraMap ℚ ℝ (Q v) := by
  rw [baseChange_real_tmul, mul_one, Algebra.algebraMap_eq_smul_one]

/-
TARGET 2
If Q.baseChange ℝ evaluates negatively at (1⊗v) and positively at (1⊗w),
then Q is isotropic over ℝ (has a nonzero zero in ℝ ⊗[ℚ] (Fin n → ℚ)).

Strategy (IVT):
  Let f : ℝ → ℝ := fun t => Q.baseChange ℝ (t • ((1:ℝ) ⊗ₜ[ℚ] v) + (1-t) • ((1:ℝ) ⊗ₜ[ℚ] w))
  Then:
  - f is continuous (Q.baseChange ℝ is a continuous map, being a degree-2 polynomial)
  - f 1 = Q.baseChange ℝ (1 ⊗ₜ v) = hv < 0
  - f 0 = Q.baseChange ℝ (1 ⊗ₜ w) = hw > 0
  By IVT (intermediate_value_univ or intermediate_value_Icc'), ∃ t₀ ∈ [0,1] with f t₀ = 0.
  The zero is z := t₀ • (1 ⊗ₜ v) + (1-t₀) • (1 ⊗ₜ w).
  Nonzero: Q.baseChange ℝ (1⊗v) < 0 ≠ 0 and Q.baseChange ℝ (1⊗w) > 0 ≠ 0,
  so neither 1⊗v nor 1⊗w is in the zero set. If z = 0, then f t₀ = 0, and we still need
  IsIsotropicOverReals Q = ∃ v ≠ 0, Q.baseChange ℝ v = 0. The easier path:
  use strict_ivt to get t₀ ∈ (0,1) (open interval), then z is a nonzero linear combination.
-/
theorem real_isotropic_of_sign_change_ari (Q : QuadraticForm ℚ (Fin n → ℚ))
    (v w : Fin n → ℚ)
    (hv : Q.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] v) < 0)
    (hw : 0 < Q.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] w)) :
    IsIsotropicOverReals Q := by
  sorry

/-
TARGET 3 (most tractable — reduces to TARGET 2 via TARGET 1)
If Q v < 0 and Q w > 0 in ℚ, then Q is isotropic over ℝ.

Strategy:
  Step 1: Q.baseChange ℝ (1⊗v) = (Q v : ℝ) < 0
    by `baseChange_one_tmul_eq` and `Rat.cast_lt_zero`/`Rat.cast_pos`
  Step 2: Q.baseChange ℝ (1⊗w) = (Q w : ℝ) > 0
    similarly
  Step 3: Apply `real_isotropic_of_sign_change` from Hilbert11OQ01OQ01.

Aristotle can likely handle this: it's a cast + existing theorem application.
-/
theorem real_isotropic_of_rational_sign_change_ari (Q : QuadraticForm ℚ (Fin n → ℚ))
    (v w : Fin n → ℚ) (hv : Q v < 0) (hw : 0 < Q w) :
    IsIsotropicOverReals Q := by
  sorry

end Hilbert11OQ01OQ01Aristotle
