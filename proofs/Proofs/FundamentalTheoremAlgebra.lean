import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Fundamental Theorem of Algebra

## What This Proves
Every non-constant polynomial with complex coefficients has at least one
complex root. Equivalently: the complex numbers ℂ are algebraically closed.

## Approach
- **Foundation (from Mathlib):** The core theorem `Complex.exists_root` is
  provided by Mathlib, which proves it using Liouville's theorem from complex
  analysis. The full algebraic closure `Complex.isAlgClosed` is also provided.
- **Original Contributions:** This file provides exposition, demonstrates the
  connection to polynomial factorization, and shows consequences like complete
  splitting of polynomials over ℂ.
- **Proof Techniques Demonstrated:** Working with Mathlib's polynomial API,
  using algebraically closed field instances, `simp` with polynomial lemmas.

## Status
- [ ] Complete proof
- [x] Uses Mathlib for main result
- [ ] Proves extensions/corollaries
- [ ] Pedagogical example
- [x] Incomplete (has sorries)

## Mathlib Dependencies
- `Complex.exists_root` : Core theorem—every non-constant polynomial has a root
- `Complex.isAlgClosed` : Instance proving ℂ is algebraically closed
- `IsAlgClosed.splits_codomain` : Every polynomial splits over an algebraically closed field
- `Polynomial.degree`, `Polynomial.IsRoot` : Polynomial degree and root definitions

Historical Note: First conjectured by Albert Girard (1629), with the first
rigorous proof by Carl Friedrich Gauss in his 1799 doctoral dissertation.
Despite its name, every known proof requires analysis—there is no purely
algebraic proof.
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
  sorry

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
theorem card_roots_eq_degree {p : ℂ[X]} (hp : p ≠ 0) :
    Multiset.card (roots p) = natDegree p := by
  sorry  -- Requires full theory of algebraically closed fields

-- Every monic polynomial equals the product of (X - root) over its roots
-- This is the complete factorization theorem for algebraically closed fields
theorem monic_prod_roots {p : ℂ[X]} (hp : Monic p) :
    p = ((roots p).map (fun r => X - C r)).prod := by
  sorry  -- Requires full factorization theory

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
  -- The polynomial a*X² + b*X + c has degree 2 (since a ≠ 0)
  -- so by FTA it has a root
  sorry

end FundamentalTheoremAlgebra

#check FundamentalTheoremAlgebra.fundamental_theorem_of_algebra
#check FundamentalTheoremAlgebra.splits_over_complex
#check FundamentalTheoremAlgebra.card_roots_eq_degree
