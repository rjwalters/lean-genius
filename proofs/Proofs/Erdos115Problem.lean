/-!
# Erdős Problem #115 — Polynomial Derivatives on Connected Lemniscates

For a polynomial p(z) of degree n, define the lemniscate
  L(p) = {z ∈ ℂ : |p(z)| ≤ 1}.

If L(p) is connected, is it true that
  max_{z ∈ L(p)} |p'(z)| ≤ (1/2 + o(1)) · n²?

**PROVED** by Eremenko and Lempert. The Chebyshev polynomials are extremal.

Known bounds:
- Lower: max |p'| ≥ n (equality for p(z) = zⁿ)
- Upper: Pommerenke proved max |p'| ≤ (e/2) · n²
- Sharp: Eremenko–Lempert proved (1/2 + o(1)) · n² is the correct bound

Reference: https://erdosproblems.com/115
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Polynomial and Lemniscate Abstractions -/

/-- Abstract representation of a complex polynomial of degree n -/
axiom ComplexPoly : ℕ → Type

/-- The degree of a polynomial -/
axiom polyDegree : {n : ℕ} → ComplexPoly n → ℕ
axiom polyDegree_eq (n : ℕ) (p : ComplexPoly n) : polyDegree p = n

/-- Whether the lemniscate {z : |p(z)| ≤ 1} is connected -/
axiom IsLemniscateConnected : {n : ℕ} → ComplexPoly n → Prop

/-- The maximum of |p'(z)| over the lemniscate {z : |p(z)| ≤ 1} -/
axiom maxDerivOnLemniscate : {n : ℕ} → ComplexPoly n → ℝ

/-- The maximum of |p'(z)| is always non-negative -/
axiom maxDeriv_nonneg (n : ℕ) (p : ComplexPoly n) :
  0 ≤ maxDerivOnLemniscate p

/-! ## Known Bounds -/

/-- Lower bound: the maximum derivative on a connected lemniscate is at least n.
    Equality is achieved by p(z) = zⁿ. -/
axiom lemniscate_deriv_lower (n : ℕ) (hn : 1 ≤ n) (p : ComplexPoly n)
    (hc : IsLemniscateConnected p) :
  (n : ℝ) ≤ maxDerivOnLemniscate p

/-- The monomial p(z) = zⁿ achieves the lower bound -/
axiom monomial_poly : (n : ℕ) → ComplexPoly n
axiom monomial_connected (n : ℕ) (hn : 1 ≤ n) :
  IsLemniscateConnected (monomial_poly n)
axiom monomial_deriv_eq (n : ℕ) (hn : 1 ≤ n) :
  maxDerivOnLemniscate (monomial_poly n) = (n : ℝ)

/-- Pommerenke's bound: max |p'| ≤ (e/2) · n² on connected lemniscates -/
axiom pommerenke_upper (n : ℕ) (hn : 1 ≤ n) (p : ComplexPoly n)
    (hc : IsLemniscateConnected p) :
  maxDerivOnLemniscate p ≤ (2718 : ℝ) / 1000 / 2 * ((n : ℝ) ^ 2)

/-- Chebyshev polynomials of degree n -/
axiom chebyshev_poly : (n : ℕ) → ComplexPoly n
axiom chebyshev_connected (n : ℕ) (hn : 1 ≤ n) :
  IsLemniscateConnected (chebyshev_poly n)

/-- Chebyshev polynomials achieve max derivative ~ n²/2 -/
axiom chebyshev_deriv_asymptotic :
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (1 / 2 - ε) * ((n : ℝ) ^ 2) ≤ maxDerivOnLemniscate (chebyshev_poly n) ∧
    maxDerivOnLemniscate (chebyshev_poly n) ≤ (1 / 2 + ε) * ((n : ℝ) ^ 2)

/-! ## The Eremenko–Lempert Theorem -/

/-- Erdős Problem 115 (PROVED by Eremenko–Lempert):
    For connected lemniscates, max |p'| ≤ (1/2 + o(1)) · n² -/
axiom ErdosProblem115_proved :
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : ComplexPoly n, IsLemniscateConnected p →
      maxDerivOnLemniscate p ≤ (1 / 2 + ε) * ((n : ℝ) ^ 2)

/-- The bound is sharp: Chebyshev polynomials show n²/2 is the correct constant -/
theorem ErdosProblem115_sharp :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ p : ComplexPoly n, IsLemniscateConnected p ∧
        (1 / 2 - ε) * ((n : ℝ) ^ 2) ≤ maxDerivOnLemniscate p := by
  intro ε hε
  obtain ⟨N, hN⟩ := chebyshev_deriv_asymptotic ε hε
  exact ⟨N, fun n hn => ⟨chebyshev_poly n, chebyshev_connected n (by omega),
    (hN n hn).1⟩⟩
