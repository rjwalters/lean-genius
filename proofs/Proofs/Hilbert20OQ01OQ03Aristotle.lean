/-
  Aristotle targets for Hilbert20OQ01OQ03
  Routine supporting lemmas for automated proof search.
  See Hilbert20OQ01OQ03.lean for the main formalization of Dencker's theorem.

  Criteria for inclusion:
  - NOT the bridge-axiom sorries (real_symbol_solvable, self_adjoint_solvable)
    which need imSymbolAlongCurve to principalSymbol connections
  - Algebraic helper: product of complex numbers with zero imaginary parts
  - Algebraic helper: finite products of real-embedded complex monomials
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (2):
  - prod_im_eq_zero_ari: finite product of complex numbers with zero im has zero im
  - monomial_real_ari: Finset.univ product of (ξ i : ℂ)^(α i) has zero imaginary part

  NOT included (need bridge axiom):
  - real_symbol_solvable: connects imSymbolAlongCurve to principalSymbol
  - self_adjoint_solvable: same bridge axiom issue
-/
import Mathlib

namespace Hilbert20OQ01OQ03Aristotle

open Finset Complex

/-
## Part 1: Product of Real Complex Numbers

If every factor in a finite product of complex numbers has imaginary part 0,
then the product also has imaginary part 0.

This is the key helper used in monomial_real: since each factor (ξ i : ℂ)^(α i)
is a real number embedded in ℂ, the product is also a real complex number.
-/

/-- A finite product of complex numbers with zero imaginary parts has zero imaginary part. -/
theorem prod_im_eq_zero_ari {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, (f i).im = 0) : (s.prod f).im = 0 := by
  induction s using Finset.induction with
  | empty => simp
  | insert ha ih =>
    rw [Finset.prod_insert ha, Complex.mul_im,
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi)),
        h _ (Finset.mem_insert_self _ _)]
    ring

/-
## Part 2: Monomials at Real Inputs Are Real

The monomial ξ^α = ∏ᵢ (ξ i : ℂ)^(α i) evaluated at real inputs ξ : Fin n → ℝ
has imaginary part 0. This is because (x : ℂ)^n for x : ℝ is a real complex number.

Proof: each factor (ξ i : ℂ)^(α i) = Complex.ofReal (ξ i ^ α i) has im = 0,
so by prod_im_eq_zero_ari, the whole product has im = 0.
-/

/-- Finite products of real-embedded powers have zero imaginary part. -/
theorem monomial_real_ari {n : ℕ} (α : Fin n → ℕ) (ξ : Fin n → ℝ) :
    (Finset.univ.prod fun i => (ξ i : ℂ) ^ α i).im = 0 := by
  apply prod_im_eq_zero_ari
  intro i _
  simp [Complex.ofReal_pow]

end Hilbert20OQ01OQ03Aristotle
