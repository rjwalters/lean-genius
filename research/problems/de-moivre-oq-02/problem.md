# Chebyshev Polynomials via De Moivre's Theorem

## Problem Statement

Prove that the Chebyshev polynomials of the first kind satisfy the identity:

$$T_n(\cos\theta) = \cos(n\theta)$$

where $T_n$ is the $n$-th Chebyshev polynomial, defined by the three-term recurrence:
- $T_0(x) = 1$
- $T_1(x) = x$  
- $T_n(x) = 2x \cdot T_{n-1}(x) - T_{n-2}(x)$

This connection follows from De Moivre's theorem: $(\cos\theta + i\sin\theta)^n = \cos(n\theta) + i\sin(n\theta)$.

## Source

- **Base Proof**: `de-moivre` - De Moivre's Theorem
- **Extension Type**: Cross-domain connection (complex analysis → polynomial theory)
- **Category**: Extension/Formalization

## Lean Formalization Goal

Formally prove in Lean 4/Mathlib that `∀ n : ℕ, ∀ θ : ℝ, Polynomial.eval (cos θ) (chebyshevT ℤ n) = cos (n * θ)`.

Mathlib likely has `Polynomial.Chebyshev` with `chebyshevT` defined. The key connection to prove is that the evaluation at cos(θ) satisfies the De Moivre recurrence.

## Related Mathlib

- `Complex.cos_add`, `Complex.sin_add` (for De Moivre)
- `Polynomial.Chebyshev.chebyshevT` (Chebyshev polynomials)
- `Real.cos_nat_mul` or similar

## Significance: 8/10
Strong cross-domain result connecting complex analysis and polynomial theory, with practical applications in numerical analysis and approximation theory.

## Tractability: 7/10
Mathlib has both De Moivre machinery and Chebyshev polynomials. The main challenge is connecting them via the recurrence, which should be inductive.
