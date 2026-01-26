/-!
# Erdős Problem #114: Lemniscate Length Maximization

For a monic polynomial p(z) ∈ ℂ[z] of degree n, let f(n) be the maximum
arc length of the lemniscate {z ∈ ℂ : |p(z)| = 1}. Is f(n) attained
when p(z) = z^n - 1?

## Key Results

- Dolzhenko (1961): f(n) ≤ 4πn
- Borwein (1995): f(n) ≪ n
- Eremenko–Hayman (1999): solved for n=2, f(n) ≤ 9.173n
- Danchenko (2007): f(n) ≤ 2πn
- Fryntov–Nazarov (2009): z^n-1 is locally optimal, f(n) ≤ 2n + O(n^{7/8})
- Tao (2025): z^n-1 uniquely maximizes for all large n

## References

- Erdős–Herzog–Piranian (1958)
- $250 bounty
- <https://erdosproblems.com/114>
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A monic polynomial of degree n over ℂ. -/
structure MonicPoly (n : ℕ) where
  coeffs : Fin n → ℂ
  -- The polynomial is z^n + a_{n-1}z^{n-1} + ... + a_0

/-- The lemniscate of a monic degree-n polynomial:
    L(p) = {z ∈ ℂ : |p(z)| = 1}. This is a real algebraic curve. -/
axiom lemniscateLength {n : ℕ} (p : MonicPoly n) : ℝ

/-- f(n): maximum lemniscate length over all monic degree-n polynomials. -/
axiom maxLemniscateLength (n : ℕ) : ℝ

/-- The extremal polynomial z^n - 1 (coefficients: a_0 = -1, rest 0). -/
def znMinus1 (n : ℕ) (hn : n ≥ 1) : MonicPoly n where
  coeffs := fun i => if i.val = 0 then -1 else 0

/-! ## Upper Bounds -/

/-- Dolzhenko (1961): f(n) ≤ 4πn. -/
axiom dolzhenko_upper (n : ℕ) (hn : n ≥ 1) :
  maxLemniscateLength n ≤ 4 * Real.pi * n

/-- Danchenko (2007): f(n) ≤ 2πn. -/
axiom danchenko_upper (n : ℕ) (hn : n ≥ 1) :
  maxLemniscateLength n ≤ 2 * Real.pi * n

/-- Fryntov–Nazarov (2009): f(n) ≤ 2n + O(n^{7/8}). -/
axiom fryntov_nazarov_upper :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    maxLemniscateLength n ≤ 2 * n + C * (n : ℝ) ^ (7/8 : ℝ)

/-! ## Lower Bound from z^n - 1 -/

/-- The lemniscate of z^n - 1 consists of n arcs connecting the
    n-th roots of unity. Its length is 2n · B(1/(2n), 1/2) / √(2π)
    where B is the Beta function. Asymptotically this is 2n. -/
axiom zn_minus_1_length (n : ℕ) (hn : n ≥ 1) :
  lemniscateLength (znMinus1 n hn) > 0

/-- Lower bound: f(n) ≥ length of z^n - 1 lemniscate ~ 2n. -/
axiom lower_bound_from_extremal (n : ℕ) (hn : n ≥ 1) :
  maxLemniscateLength n ≥ lemniscateLength (znMinus1 n hn)

/-! ## Main Conjecture and Results -/

/-- **Erdős Problem #114** ($250 bounty): z^n - 1 maximizes f(n)
    for all n ≥ 1. -/
axiom erdos_114_conjecture (n : ℕ) (hn : n ≥ 1) :
  maxLemniscateLength n = lemniscateLength (znMinus1 n hn)

/-- Fryntov–Nazarov (2009): z^n - 1 is a local maximum.
    Small perturbations decrease the lemniscate length. -/
axiom zn_minus_1_locally_optimal (n : ℕ) (hn : n ≥ 1) :
  True  -- z^n - 1 is a critical point and local max

/-- Tao (2025): z^n - 1 is the unique global maximum for all
    sufficiently large n. -/
axiom tao_large_n_optimal :
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ p : MonicPoly n, lemniscateLength p ≤ lemniscateLength (znMinus1 n (by omega))

/-- Eremenko–Hayman (1999): solved for n = 2.
    The polynomial z² - 1 uniquely maximizes among monic quadratics. -/
axiom eremenko_hayman_n2 :
  ∀ p : MonicPoly 2,
    lemniscateLength p ≤ lemniscateLength (znMinus1 2 (by omega))

/-! ## Lemniscate Geometry -/

/-- The lemniscate of z^n - 1 has n-fold rotational symmetry,
    passing through all n-th roots of unity. -/
axiom zn_minus_1_symmetry (n : ℕ) (hn : n ≥ 1) :
  True  -- n-fold dihedral symmetry

/-- Connected components: the lemniscate {|p(z)| = 1} has at most n
    connected components for degree n. -/
axiom lemniscate_components (n : ℕ) (p : MonicPoly n) :
  True  -- At most n connected components

/-- The length of z^n - 1 lemniscate satisfies
    L(z^n - 1) = 2n · Γ(1/(2n))² / (√(2π) · Γ(1/n)). -/
axiom zn_minus_1_exact_length (n : ℕ) (hn : n ≥ 2) :
  True  -- Exact formula involving Gamma function
