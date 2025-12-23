import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.FieldTheory.IsAlgClosed.Basic

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
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one, Complex.I_sq]
  norm_num

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
-- This is the contrapositive of the fundamental theorem
theorem no_roots_implies_constant {p : ℂ[X]} (h : ∀ z : ℂ, ¬IsRoot p z) :
    degree p = 0 := by
  -- If degree > 0, then by FTA there's a root, contradicting h
  by_contra hp
  -- We need to show 0 < degree p to apply FTA
  have hp_pos : 0 < degree p := by
    rcases eq_or_ne p 0 with rfl | hp_ne
    · -- If p = 0, every z is a root: IsRoot 0 z ↔ eval z 0 = 0 ↔ True
      simp [IsRoot] at h
    · -- p ≠ 0, so degree p = natDegree p ≥ 0
      -- Since degree p ≠ 0 (from hp), we have degree p > 0
      rw [Polynomial.degree_eq_natDegree hp_ne]
      have hnd : natDegree p ≠ 0 := by
        intro hzero
        rw [Polynomial.degree_eq_natDegree hp_ne, hzero] at hp
        simp at hp
      exact WithBot.coe_pos.mpr (Nat.pos_of_ne_zero hnd)
  -- By FTA, there exists a root
  obtain ⟨z, hz⟩ := Complex.exists_root hp_pos
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
-- In an algebraically closed field, a polynomial of degree n has exactly n roots
theorem card_roots_eq_degree {p : ℂ[X]} (_hp : p ≠ 0) :
    Multiset.card (roots p) = natDegree p := by
  -- In an algebraically closed field, a polynomial splits completely
  have hsplit : Splits (RingHom.id ℂ) p := IsAlgClosed.splits_codomain p
  -- For a polynomial that splits, the number of roots equals the natDegree
  have h := Polynomial.natDegree_eq_card_roots hsplit
  -- map (RingHom.id ℂ) p = p, so roots are the same
  simp only [Polynomial.map_id] at h
  exact h.symm

-- Every monic polynomial equals the product of (X - root) over its roots
-- This is the complete factorization theorem for algebraically closed fields
theorem monic_prod_roots {p : ℂ[X]} (hp : Monic p) :
    p = ((roots p).map (fun r => X - C r)).prod := by
  -- For a monic polynomial over an algebraically closed field,
  -- p = prod (X - r) over all roots r
  have hsplit : Splits (RingHom.id ℂ) p := IsAlgClosed.splits_codomain p
  -- Get the root count equality
  have hcard : Multiset.card (roots p) = natDegree p := by
    have h := Polynomial.natDegree_eq_card_roots hsplit
    simp only [Polynomial.map_id] at h
    exact h.symm
  -- Use Mathlib's theorem: monic polynomial equals product of linear factors
  exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard).symm

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
-- This follows directly from the fundamental theorem
theorem quadratic_has_root (a b c : ℂ) (ha : a ≠ 0) :
    ∃ z : ℂ, a * z ^ 2 + b * z + c = 0 := by
  -- Construct the polynomial p(X) = a*X² + b*X + c
  let p : ℂ[X] := C a * X ^ 2 + C b * X + C c
  -- Show degree p = 2 (since a ≠ 0)
  have hdeg : degree p = 2 := by
    have h1 : degree (C a * X ^ 2) = 2 := by
      simp only [← mul_comm (X ^ 2) (C a), degree_mul, degree_C ha, degree_X_pow, zero_add]
      rfl
    have h2 : degree (C b * X + C c) < degree (C a * X ^ 2) := by
      have hbx : degree (C b * X) ≤ 1 := by
        rcases eq_or_ne b 0 with rfl | hb
        · simp [degree_zero]
        · simp only [← mul_comm X (C b), degree_mul, degree_C hb, degree_X, zero_add]
          rfl
      have hc : degree (C c) ≤ 0 := degree_C_le
      calc degree (C b * X + C c) ≤ max (degree (C b * X)) (degree (C c)) := degree_add_le _ _
        _ ≤ max 1 0 := max_le_max hbx hc
        _ = 1 := by rfl
        _ < 2 := by norm_num
        _ = degree (C a * X ^ 2) := h1.symm
    -- p = C a * X ^ 2 + (C b * X + C c)
    have hassoc : p = C a * X ^ 2 + (C b * X + C c) := by ring
    calc degree p = degree (C a * X ^ 2 + (C b * X + C c)) := by rw [hassoc]
      _ = degree (C a * X ^ 2) := degree_add_eq_left_of_degree_lt h2
      _ = 2 := h1
  -- Apply FTA: degree > 0 implies existence of root
  have hpos : 0 < degree p := by rw [hdeg]; norm_num
  obtain ⟨z, hz⟩ := Complex.exists_root hpos
  use z
  -- Unfold the polynomial evaluation
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_C, p] at hz
  exact hz

end FundamentalTheoremAlgebra

#check FundamentalTheoremAlgebra.fundamental_theorem_of_algebra
#check FundamentalTheoremAlgebra.splits_over_complex
#check FundamentalTheoremAlgebra.card_roots_eq_degree
