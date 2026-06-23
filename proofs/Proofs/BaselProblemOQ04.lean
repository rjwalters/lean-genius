/-
Basel Problem OQ-04: Euler Product Form

The Euler product representation of ζ(2):

  ∏_p (1 - p⁻²)⁻¹ = π²/6

where the product is over all primes p. This connects the Basel sum
∑ 1/n² = π²/6 to the prime numbers via the fundamental theorem of
arithmetic.

Proof: combine the Euler product for ζ(s) at s = 2 with the Basel
identity ζ(2) = π²/6. Both results are in Mathlib.

References:
- Euler, L. "Variae observationes circa series infinitas" (1737)
- Mathlib: Mathlib.NumberTheory.EulerProduct.DirichletLSeries
- Mathlib: Mathlib.NumberTheory.LSeries.HurwitzZetaValues
-/

import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Complex Real Nat Filter

namespace BaselProblemOQ04

/-
## The Main Theorem
-/

/-- The real part of 2 exceeds 1 (needed for Euler product convergence). -/
theorem two_re_gt_one : 1 < (2 : ℂ).re := by norm_num

/-- **Euler Product for ζ(2)** (tprod form):
    ∏_p (1 - p⁻²)⁻¹ = π²/6.

    Proof: combine Mathlib's Euler product `riemannZeta_eulerProduct_tprod`
    at s = 2 with `riemannZeta_two` (ζ(2) = π²/6). -/
theorem euler_product_pi_sq_div_six :
    ∏' (p : Nat.Primes), (1 - (↑↑p : ℂ) ^ (-(2 : ℂ)))⁻¹ =
    ↑Real.pi ^ 2 / 6 := by
  rw [← riemannZeta_two]
  exact riemannZeta_eulerProduct_tprod two_re_gt_one

/-- **Euler Product for ζ(2)** (HasProd form):
    The infinite product converges to π²/6. -/
theorem euler_product_hasProd :
    HasProd (fun (p : Nat.Primes) => (1 - (↑↑p : ℂ) ^ (-(2 : ℂ)))⁻¹)
    (↑Real.pi ^ 2 / 6) := by
  rw [← riemannZeta_two]
  exact riemannZeta_eulerProduct_hasProd two_re_gt_one

/-- **Euler Product for ζ(2)** (Tendsto form):
    Finite products over primes below n converge to π²/6. -/
theorem euler_product_tendsto :
    Tendsto
      (fun (n : ℕ) => ∏ p ∈ n.primesBelow, (1 - (↑p : ℂ) ^ (-(2 : ℂ)))⁻¹)
      atTop
      (nhds (↑Real.pi ^ 2 / 6)) := by
  rw [← riemannZeta_two]
  exact riemannZeta_eulerProduct two_re_gt_one

/-
## The Basel Sum (from Mathlib)
-/

/-- The Basel sum: ∑ 1/n² = π²/6. -/
theorem basel_sum : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
  hasSum_zeta_two

/-
## Historical Context

Euler (1737) discovered the product representation

  ∏_p 1/(1-p⁻ˢ) = ∑_{n=1}^∞ 1/nˢ

by expanding each factor as a geometric series:
  1/(1-p⁻ˢ) = 1 + p⁻ˢ + p⁻²ˢ + ...

and using unique prime factorization to see that the product over
all primes generates exactly the terms 1/nˢ for all n ≥ 1.

At s = 2 this gives:
  ∏_p (1 - 1/p²)⁻¹ = ∑ 1/n² = π²/6

Equivalently: ∏_p (p²-1)/p² = 6/π² ≈ 0.6079.

This also equals the probability that two randomly chosen positive
integers are coprime (Cesàro 1881).
-/

/-
## Summary

Axiom count: 0
Sorry count: 0

This is a fully verified proof combining two Mathlib results:
1. riemannZeta_eulerProduct_tprod (Euler product for ζ(s))
2. riemannZeta_two (ζ(2) = π²/6)
-/

end BaselProblemOQ04
