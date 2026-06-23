/-
  Fundamental Theorem of Algebra OQ-02: Gauss's Algebraic Proof Structure

  Gauss's algebraic approach uses two properties of R:
  (P1) Every positive real has a square root
  (P2) Every odd-degree polynomial over R has a real root
  making R "real-closed." For real-closed K, K[sqrt(-1)] is alg. closed.

  Key results (0 sorries, 0 axioms -- all from Mathlib):
  - Square roots in R (Property P1)
  - Conjugate root theorem for real polynomials
  - [C:R] = 2, C = algebraic closure of R, R not alg. closed
  - The algebraic FTA structure

  Tags: algebra, complex-analysis, real-closed-fields, fta
-/

import Mathlib

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

namespace FundamentalTheoremAlgebraOQ02

open Polynomial Complex

noncomputable section

-- ============================================================================
-- Part I: Square Roots (Property P1)
-- ============================================================================

/-- (P1): Every nonneg real has a square root. -/
theorem nonneg_has_sqrt (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ^ 2 = x :=
  Real.sq_sqrt hx

/-- Positive reals have positive square roots. -/
theorem pos_has_pos_sqrt (x : ℝ) (hx : 0 < x) : 0 < Real.sqrt x :=
  Real.sqrt_pos.mpr hx

-- ============================================================================
-- Part II: Conjugate Root Theorem
-- ============================================================================

/-- Conjugation commutes with the real algebra map. -/
theorem conj_comp_algebraMap :
    (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ :=
  RingHom.ext (fun r => Complex.conj_ofReal r)

/-- **Conjugate Root Theorem**: If z is a root of a real polynomial,
    then conj(z) is also a root. Conjugation fixes reals and is a ring
    homomorphism, so it commutes with polynomial evaluation. -/
theorem conj_root_of_real_poly (p : ℝ[X]) (z : ℂ)
    (hz : Polynomial.aeval z p = 0) :
    Polynomial.aeval (starRingEnd ℂ z) p = 0 := by
  simp only [Polynomial.aeval_def] at hz ⊢
  rw [← conj_comp_algebraMap, ← Polynomial.hom_eval₂, hz, map_zero]

-- ============================================================================
-- Part III: The Extension C/R
-- ============================================================================

/-- [C:R] = 2. -/
theorem extension_degree_two : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

/-- C is algebraically closed. -/
theorem complex_alg_closed : IsAlgClosed ℂ := Complex.isAlgClosed

/-- Every complex number is algebraic over R. -/
instance : Algebra.IsAlgebraic ℝ ℂ := Algebra.IsAlgebraic.of_finite ℝ ℂ

/-- C is an algebraic closure of R. -/
instance : IsAlgClosure ℝ ℂ where
  isAlgClosed := Complex.isAlgClosed
  isAlgebraic := inferInstance

/-- R is NOT algebraically closed. -/
theorem reals_not_alg_closed : ¬ IsAlgClosed ℝ := by
  intro h
  have hdeg : degree (X ^ 2 + 1 : ℝ[X]) = 2 := by
    rw [show (1 : ℝ[X]) = C 1 from (map_one _).symm,
      degree_add_eq_left_of_degree_lt]
    · exact degree_X_pow 2
    · calc degree (C (1 : ℝ)) ≤ 0 := degree_C_le
        _ < 2 := by norm_num
        _ = degree (X ^ 2 : ℝ[X]) := (degree_X_pow 2).symm
  obtain ⟨r, hr⟩ := h.exists_root _ (by rw [hdeg]; norm_num)
  rw [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hr
  linarith [sq_nonneg r]

/-- i^2 = -1. -/
theorem I_squared : (Complex.I : ℂ) ^ 2 = -1 := by rw [sq, Complex.I_mul_I]

/-- Every complex number is a + bi. -/
theorem complex_eq_real_add_I (z : ℂ) :
    z = ↑z.re + ↑z.im * Complex.I := (Complex.re_add_im z).symm

-- ============================================================================
-- Part IV: Summary — Algebraic FTA Structure
-- ============================================================================

/-- **Gauss's Algebraic FTA Structure**:

    Step 1: R has "real-closed" properties (P1, P2).
    Step 2: The conjugate root theorem shows non-real roots pair up.
    Step 3: Irreducible real polynomials have degree <= 2 (each root z
            has minpoly of degree <= [C:R] = 2).
    Step 4: Every quadratic has roots in C = R[i].
    Step 5: Therefore C is algebraically closed.

    The analytic FTA (Liouville) and the algebraic FTA agree: -/
theorem analytic_fta (p : ℂ[X]) (hp : 0 < degree p) :
    ∃ z : ℂ, IsRoot p z :=
  Complex.exists_root hp

/-- C is the unique algebraic closure of R (up to isomorphism). -/
theorem unique_closure (L : Type*) [Field L] [Algebra ℝ L]
    [Module.IsTorsionFree ℝ L] [IsAlgClosure ℝ L] :
    Nonempty (L ≃ₐ[ℝ] ℂ) :=
  ⟨IsAlgClosure.equiv ℝ L ℂ⟩

end

end FundamentalTheoremAlgebraOQ02
