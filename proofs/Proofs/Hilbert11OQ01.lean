import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.CharP.Invertible
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic

/-!
# Hilbert's 11th Problem OQ-01: Hasse-Minkowski via p-adic Tensor Products

## Overview

This file formalizes the **local isotropy conditions** for the Hasse-Minkowski theorem
using proper tensor product base change, replacing the `True` placeholders in
`Hilbert11_QuadraticForms.lean`.

## Key Contributions

1. **Proper local isotropy**: `IsIsotropicOverReals` and `IsIsotropicOverPadic`
   use `QuadraticForm.baseChange` (Mathlib) to correctly define isotropy over
   completions via scalar extension through tensor products.

2. **Axiom elimination**: The `four_squares_connection` axiom from the parent file
   is proved here as `four_squares_from_mathlib` using `Nat.sum_four_squares`.

3. **Refined theorem statement**: `hasse_minkowski_refined` states Hasse-Minkowski
   using the proper local conditions.

## How Base Change Works

For `Q : QuadraticForm ℚ (Fin n → ℚ)` and a CharZero field `A` with `Algebra ℚ A`,
the base change `Q.baseChange A : QuadraticForm A (A ⊗[ℚ] (Fin n → ℚ))`
is the quadratic form on the tensor product, implementing scalar extension.

- `IsIsotropicOverReals Q` ↔ `Q.baseChange ℝ` has a nonzero zero in `ℝ ⊗[ℚ] (Fin n → ℚ)`
- `IsIsotropicOverPadic Q p` ↔ `Q.baseChange ℚ_[p]` has a nonzero zero in `ℚ_[p] ⊗[ℚ] (Fin n → ℚ)`

## Axiom Count

This file has **1 axiom** (`hasse_minkowski_refined`), compared to the parent file's 6.
The `four_squares_connection` axiom is eliminated via Mathlib.

## References

- Serre, J-P. "A Course in Arithmetic", Chapter IV
- Lam, T-Y. "Introduction to Quadratic Forms over Fields"
- Wieser, E. `Mathlib.LinearAlgebra.QuadraticForm.TensorProduct`
-/

set_option maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace Hilbert11OQ01

variable {n : ℕ}

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: AXIOM ELIMINATION — Four Squares from Mathlib
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Lagrange's Four Squares Theorem** (proved, not axiomatized).

Every natural number is a sum of four integer squares.
This directly proves the `four_squares_connection` axiom from `Hilbert11_QuadraticForms.lean`
using `Nat.sum_four_squares` from Mathlib.

Eliminates 1 of the 6 axioms in the parent file. -/
theorem four_squares_from_mathlib :
    ∀ m : ℕ, ∃ a b c d : ℤ, (m : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  intro m
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  exact ⟨↑a, ↑b, ↑c, ↑d, by exact_mod_cast h.symm⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: LOCAL ISOTROPY VIA TENSOR PRODUCT BASE CHANGE
═══════════════════════════════════════════════════════════════════════════════ -/

-- `Invertible (2 : ℚ)` is needed for QuadraticForm.baseChange.
-- It follows from CharZero ℚ via invertibleOfPos.
-- Lean's instance system finds this automatically.

/-- A rational quadratic form is **isotropic over ℝ** if its tensor product base change
    to ℝ has a nonzero zero.

`Q.baseChange ℝ : QuadraticForm ℝ (ℝ ⊗[ℚ] (Fin n → ℚ))` is the scalar extension of `Q`
from ℚ to ℝ via the tensor product construction. This is the correct formalization
of "Q has a nontrivial real solution", replacing the placeholder `True` in the parent file.

Note: `ℝ ⊗[ℚ] (Fin n → ℚ) ≅ Fin n → ℝ` as ℝ-vector spaces. -/
def IsIsotropicOverReals (Q : QuadraticForm ℚ (Fin n → ℚ)) : Prop :=
  ∃ v : ℝ ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange ℝ v = 0

/-- A rational quadratic form is **isotropic over ℚₚ** if its tensor product base change
    to ℚₚ has a nonzero zero.

`Q.baseChange ℚ_[p] : QuadraticForm ℚ_[p] (ℚ_[p] ⊗[ℚ] (Fin n → ℚ))` is the scalar
extension of `Q` from ℚ to ℚₚ, implementing the p-adic tensor product formalization.
This replaces the placeholder `True` in the parent file.

Note: `ℚ_[p] ⊗[ℚ] (Fin n → ℚ) ≅ Fin n → ℚ_[p]` as ℚ_[p]-vector spaces. -/
def IsIsotropicOverPadic (Q : QuadraticForm ℚ (Fin n → ℚ)) (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ v : ℚ_[p] ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange ℚ_[p] v = 0

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: BASE CHANGE COMPUTATION LEMMAS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The base change of Q over ℝ evaluates on simple tensors as:
    `(Q.baseChange ℝ) (r ⊗ₜ v) = Q v • (r * r)` -/
theorem baseChange_real_tmul (Q : QuadraticForm ℚ (Fin n → ℚ))
    (r : ℝ) (v : Fin n → ℚ) :
    Q.baseChange ℝ (r ⊗ₜ[ℚ] v) = Q v • (r * r) :=
  QuadraticForm.baseChange_tmul Q r v

/-- The base change of Q over ℚₚ evaluates on simple tensors as:
    `(Q.baseChange ℚ_[p]) (x ⊗ₜ v) = Q v • (x * x)` -/
theorem baseChange_padic_tmul (Q : QuadraticForm ℚ (Fin n → ℚ))
    (p : ℕ) [Fact (Nat.Prime p)] (x : ℚ_[p]) (v : Fin n → ℚ) :
    Q.baseChange ℚ_[p] (x ⊗ₜ[ℚ] v) = Q v • (x * x) :=
  QuadraticForm.baseChange_tmul Q x v

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: RATIONAL ISOTROPY IMPLIES LOCAL ISOTROPY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Rational isotropy implies isotropy over ℝ.

If Q has a nonzero rational zero `v₀`, then `(1 : ℝ) ⊗ₜ v₀` gives a zero of
`Q.baseChange ℝ`, since `(Q.baseChange ℝ)(1 ⊗ₜ v₀) = Q v₀ • (1 * 1) = 0`.

The nonzero condition follows from the injectivity of `1 ⊗ₜ · : (Fin n → ℚ) → ℝ ⊗[ℚ] (Fin n → ℚ)`,
which holds because `Fin n → ℚ` is a free ℚ-module.

Note: Injectivity is proved via evaluation functionals — for each i, map a ⊗ₜ w ↦ a * (w i : ℝ).
This extracts each coordinate, showing 1 ⊗ₜ v = 0 implies v = 0. -/
theorem rational_implies_real_isotropic (Q : QuadraticForm ℚ (Fin n → ℚ))
    (h : ∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0) : IsIsotropicOverReals Q := by
  obtain ⟨v, hv_ne, hv_zero⟩ := h
  refine ⟨(1 : ℝ) ⊗ₜ[ℚ] v, ?_, ?_⟩
  · -- 1 ⊗ₜ v ≠ 0 because v ≠ 0 and the canonical map Fin n → ℚ → ℝ ⊗[ℚ] (Fin n → ℚ) is injective
    -- Proved via evaluation functionals: for each i, ev_i(a ⊗ₜ w) = a * (w i : ℝ)
    intro heq
    apply hv_ne
    funext i
    -- Evaluation functional ev_i : ℝ ⊗[ℚ] (Fin n → ℚ) →ₗ[ℚ] ℝ defined by a ⊗ₜ w ↦ a * (w i : ℝ)
    let ev : ℝ ⊗[ℚ] (Fin n → ℚ) →ₗ[ℚ] ℝ :=
      TensorProduct.lift (LinearMap.mk₂ ℚ (fun (a : ℝ) (w : Fin n → ℚ) => a * algebraMap ℚ ℝ (w i))
        (fun _ _ _ => by ring)
        (fun c _ _ => by simp only [Algebra.smul_def]; ring)
        (fun _ _ _ => by simp only [Pi.add_apply, map_add]; ring)
        (fun c _ w => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]; ring))
    have heval : ev ((1 : ℝ) ⊗ₜ[ℚ] v) = algebraMap ℚ ℝ (v i) := by
      simp only [ev, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul]
    have hzero : ev ((1 : ℝ) ⊗ₜ[ℚ] v) = 0 := by rw [heq]; exact map_zero ev
    have hvi : (v i : ℝ) = 0 := by simpa using heval.symm.trans hzero
    exact_mod_cast hvi
  · rw [baseChange_real_tmul, hv_zero]
    simp

/-- Rational isotropy implies isotropy over ℚₚ.

Same argument as for ℝ: `(1 : ℚ_[p]) ⊗ₜ v₀` is a zero of `Q.baseChange ℚ_[p]`. -/
theorem rational_implies_padic_isotropic (Q : QuadraticForm ℚ (Fin n → ℚ))
    (p : ℕ) [Fact (Nat.Prime p)]
    (h : ∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0) : IsIsotropicOverPadic Q p := by
  obtain ⟨v, hv_ne, hv_zero⟩ := h
  refine ⟨(1 : ℚ_[p]) ⊗ₜ[ℚ] v, ?_, ?_⟩
  · -- 1 ⊗ₜ v ≠ 0 via evaluation functionals: for each i, ev_i(a ⊗ₜ w) = a * (w i : ℚ_[p])
    intro heq
    apply hv_ne
    funext i
    -- Evaluation functional ev_i : ℚ_[p] ⊗[ℚ] (Fin n → ℚ) →ₗ[ℚ] ℚ_[p]
    let ev : ℚ_[p] ⊗[ℚ] (Fin n → ℚ) →ₗ[ℚ] ℚ_[p] :=
      TensorProduct.lift (LinearMap.mk₂ ℚ (fun (a : ℚ_[p]) (w : Fin n → ℚ) => a * algebraMap ℚ ℚ_[p] (w i))
        (fun _ _ _ => by ring)
        (fun c _ _ => by simp only [Algebra.smul_def]; ring)
        (fun _ _ _ => by simp only [Pi.add_apply, map_add]; ring)
        (fun c _ w => by simp only [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]; ring))
    have heval : ev ((1 : ℚ_[p]) ⊗ₜ[ℚ] v) = algebraMap ℚ ℚ_[p] (v i) := by
      simp only [ev, TensorProduct.lift.tmul, LinearMap.mk₂_apply, one_mul]
    have hzero : ev ((1 : ℚ_[p]) ⊗ₜ[ℚ] v) = 0 := by rw [heq]; exact map_zero ev
    have hvi : (v i : ℚ_[p]) = 0 := by simpa using heval.symm.trans hzero
    exact_mod_cast hvi
  · rw [baseChange_padic_tmul, hv_zero]
    simp

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: THE REFINED HASSE-MINKOWSKI THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The Hasse-Minkowski Theorem** (axiomatized with proper tensor-product local conditions).

A quadratic form `Q` over ℚ is isotropic iff it is locally isotropic everywhere:
- Isotropic over ℝ (i.e., `Q.baseChange ℝ` has a nonzero zero), AND
- Isotropic over ℚₚ for every prime p (i.e., `Q.baseChange ℚ_[p]` has a nonzero zero).

**This is the main result**: the Hasse-Minkowski theorem with mathematically correct
local conditions replacing the placeholder `True` definitions in the parent file.

**Status**: Axiomatized. The proof requires:
- p-adic analysis and Hensel's lemma for local solvability
- Product formula for Hilbert symbols: ∏_v (a,b)_v = 1
- Global-to-local techniques via idelic methods or class field theory
- Classification of quadratic forms over local fields

References: Serre, "A Course in Arithmetic", Ch. IV; O'Meara, "Introduction to Quadratic Forms" -/
axiom hasse_minkowski_refined (Q : QuadraticForm ℚ (Fin n → ℚ)) :
    (∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0) ↔
      IsIsotropicOverReals Q ∧ ∀ p : ℕ, [Fact (Nat.Prime p)] → IsIsotropicOverPadic Q p

/-- The "easy direction" of Hasse-Minkowski: rational isotropy implies local isotropy.

This is fully proved: injectivity uses evaluation functionals, not sorry. -/
theorem hasse_easy_direction (Q : QuadraticForm ℚ (Fin n → ℚ))
    (h : ∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0) :
    IsIsotropicOverReals Q ∧ ∀ p : ℕ, [Fact (Nat.Prime p)] → IsIsotropicOverPadic Q p :=
  ⟨rational_implies_real_isotropic Q h,
   fun p _ => rational_implies_padic_isotropic Q p h⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: SUMMARY AND STATUS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
## Summary of OQ-01 Contributions

### Axiom Status Comparison

| Axiom (Parent File) | Status in OQ-01 |
|---------------------|-----------------|
| `diagonalForm` | Unchanged (inherited from parent) |
| `sylvester_law_of_inertia` | Unchanged (deep theorem) |
| `hasse_minkowski_alt` (with `True` local conditions) | **Replaced** by `hasse_minkowski_refined` |
| `four_squares_connection` | **ELIMINATED** — proved as `four_squares_from_mathlib` |
| `rational_classification_complete` | Unchanged |
| `selmer_curve_no_rational_points` | Unchanged |

### What This File Proves

1. `four_squares_from_mathlib` — Lagrange's 4 squares, proved from Mathlib (axiom eliminated)
2. `baseChange_real_tmul` — computation lemma for local isotropy over ℝ
3. `baseChange_padic_tmul` — computation lemma for local isotropy over ℚₚ
4. `hasse_easy_direction` — easy direction of Hasse-Minkowski (fully proved, no sorry)
5. `rational_implies_real_isotropic` — rational ⟹ ℝ-isotropic (proved via evaluation functionals)
6. `rational_implies_padic_isotropic` — rational ⟹ ℚₚ-isotropic (proved via evaluation functionals)

### Remaining Sorries

None. All sorries have been eliminated:
- `rational_implies_real_isotropic`: proved `1 ⊗ₜ v ≠ 0` via coordinate evaluation functionals
- `rational_implies_padic_isotropic`: proved `1 ⊗ₜ v ≠ 0` via coordinate evaluation functionals

### Next Steps

1. State Meyer's theorem: dim ≥ 5 forms over ℚ are isotropic
2. State the p-adic classification theorem (Meyer's theorem: dim ≥ 5 forms are isotropic)
3. Add Hilbert symbol formalization using `IsIsotropicOverPadic`
-/

-- Verification that key declarations type-check
#check @IsIsotropicOverReals
#check @IsIsotropicOverPadic
#check @four_squares_from_mathlib
#check @hasse_minkowski_refined
#check @hasse_easy_direction

end Hilbert11OQ01

end
