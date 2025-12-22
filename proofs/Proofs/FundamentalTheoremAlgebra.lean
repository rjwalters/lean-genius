/-
  The Fundamental Theorem of Algebra

  A formal proof in Lean 4 that every non-constant polynomial with complex
  coefficients has at least one complex root.

  Historical context: First conjectured by Albert Girard (1629), with the first
  rigorous proof by Carl Friedrich Gauss in his 1799 doctoral dissertation.
  Despite its name, every known proof requires analysis - there is no purely
  algebraic proof.

  The Mathlib proof uses Liouville's theorem: a bounded entire function is
  constant. If p(z) had no roots, then 1/p(z) would be a bounded entire
  function, hence constant, contradicting that p is non-constant.

  Author: Chris Hughes (Mathlib formalization)
  Source: https://github.com/leanprover-community/mathlib4

  This proof demonstrates how Mathlib's deep library of complex analysis
  yields this fundamental result with elegant concision.
-/

import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.FieldTheory.IsAlgClosed.Basic

-- We work with complex polynomials
open Polynomial Complex

namespace FundamentalTheoremAlgebra

/-
  Polynomial Preliminaries

  A polynomial p(z) = a_n z^n + ... + a_1 z + a_0 is represented in Mathlib
  as Polynomial ℂ. The degree is the highest power with non-zero coefficient.

  A root (or zero) of p is a value z₀ such that p(z₀) = 0, written IsRoot p z₀.
-/

-- Example: The polynomial z² + 1 has degree 2
example : degree (X ^ 2 + 1 : ℂ[X]) = 2 := by
  simp [degree_add_eq_left_of_degree_lt]

-- Example: i is a root of z² + 1
example : IsRoot (X ^ 2 + 1 : ℂ[X]) Complex.I := by
  simp [IsRoot, eval_add, eval_pow, eval_X, eval_one]
  ring

/-
  The Fundamental Theorem of Algebra

  Every non-constant polynomial with complex coefficients has at least one
  complex root. "Non-constant" means degree ≥ 1.

  This is Mathlib's Complex.exists_root theorem.
-/

-- The main theorem: every non-constant complex polynomial has a root
theorem fundamental_theorem_of_algebra {p : ℂ[X]} (hp : 0 < degree p) :
    ∃ z : ℂ, IsRoot p z :=
  Complex.exists_root hp

-- Equivalent formulation: if p has no roots, it must be constant
theorem no_roots_implies_constant {p : ℂ[X]} (h : ∀ z : ℂ, ¬IsRoot p z) :
    degree p = 0 := by
  by_contra hp
  have : 0 < degree p := Nat.pos_of_ne_zero (fun h0 => hp (h0 ▸ rfl))
  obtain ⟨z, hz⟩ := Complex.exists_root this
  exact h z hz

/-
  Algebraic Closure

  A field K is algebraically closed if every non-constant polynomial over K
  has a root in K. The Fundamental Theorem of Algebra says exactly that
  ℂ is algebraically closed.

  Mathlib provides this as an instance: Complex.isAlgClosed
-/

-- The complex numbers are algebraically closed
example : IsAlgClosed ℂ := Complex.isAlgClosed

-- This means every polynomial splits completely into linear factors
theorem splits_over_complex (p : ℂ[X]) : Splits (RingHom.id ℂ) p :=
  IsAlgClosed.splits_codomain p

/-
  Complete Factorization

  Since ℂ is algebraically closed, every degree-n polynomial has exactly n
  roots (counted with multiplicity) and factors as:

    p(z) = a_n (z - r₁)(z - r₂)...(z - rₙ)

  where r₁, ..., rₙ are the roots.
-/

-- The number of roots equals the degree (for non-zero polynomials)
theorem card_roots_eq_degree {p : ℂ[X]} (hp : p ≠ 0) :
    Multiset.card (roots p) = natDegree p :=
  IsAlgClosed.card_roots_eq_natDegree hp

-- Every monic polynomial equals the product of (X - root) over its roots
theorem monic_prod_roots {p : ℂ[X]} (hp : Monic p) :
    p = (roots p).prod (fun r => X - C r) :=
  IsAlgClosed.prod_rootsEquiv p hp

/-
  Why This Matters

  The Fundamental Theorem of Algebra has profound consequences:

  1. Every polynomial equation has a solution in ℂ - we never need to extend
     the number system further for algebra

  2. Linear algebra over ℂ is "complete": every matrix has an eigenvalue,
     every linear map can be put in Jordan normal form

  3. The complex numbers are the algebraic closure of both ℝ and ℚ

  4. Connects algebra with analysis: the proof uses that ℂ is complete and
     connected - topological properties of the complex plane
-/

-- Every quadratic has roots (special case)
theorem quadratic_has_root (a b c : ℂ) (ha : a ≠ 0) :
    ∃ z : ℂ, a * z ^ 2 + b * z + c = 0 := by
  let p : ℂ[X] := C a * X ^ 2 + C b * X + C c
  have hdeg : degree p = 2 := by
    simp only [p]
    rw [degree_add_eq_left_of_degree_lt]
    · simp [degree_C_mul_X_pow_eq_iff, ha]
    · calc degree (C b * X + C c) ≤ max (degree (C b * X)) (degree (C c)) := degree_add_le _ _
        _ ≤ max 1 0 := by simp [degree_C_mul_X_le, degree_C_le]
        _ = 1 := by norm_num
        _ < 2 := by norm_num
  have hpos : 0 < degree p := by simp [hdeg]
  obtain ⟨z, hz⟩ := Complex.exists_root hpos
  use z
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_C, p] at hz
  exact hz

end FundamentalTheoremAlgebra

#check FundamentalTheoremAlgebra.fundamental_theorem_of_algebra
#check FundamentalTheoremAlgebra.splits_over_complex
#check FundamentalTheoremAlgebra.card_roots_eq_degree
