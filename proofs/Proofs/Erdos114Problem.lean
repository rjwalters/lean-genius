/-
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

/- ## Core Definitions -/

/-- A monic polynomial of degree n over ℂ. -/
structure MonicPoly (n : ℕ) where
  coeffs : Fin n → ℂ
  -- The polynomial is z^n + a_{n-1}z^{n-1} + ... + a_0

/-- The lemniscate of a monic degree-n polynomial:
    L(p) = {z ∈ ℂ : |p(z)| = 1}. This is a real algebraic curve. -/
/-- f(n): maximum lemniscate length over all monic degree-n polynomials. -/
/-- The extremal polynomial z^n - 1 (coefficients: a_0 = -1, rest 0). -/
def znMinus1 (n : ℕ) (hn : n ≥ 1) : MonicPoly n where
  coeffs := fun i => if i.val = 0 then -1 else 0

/- ## Upper Bounds -/

/- ## Lower Bound from z^n - 1 -/

/- ## Main Conjecture and Results -/

/- ## Lemniscate Geometry -/
