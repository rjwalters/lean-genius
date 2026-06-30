/-
  Euler's Product for the Basel Problem
  =====================================

  fundamental-arithmetic-oq-03

  Open question (third open question of the Fundamental Theorem of Arithmetic
  gallery entry):

    "Can the connection to the Riemann zeta function Euler product
     ζ(s) = ∏ₚ (1 - p^{-s})⁻¹ be formalized as a consequence of the FTA?"

  Mathlib supplies the general Euler product `riemannZeta_eulerProduct_tprod`,
  whose proof is exactly the Fundamental Theorem of Arithmetic reorganization of
  the Dirichlet series ∑ₙ n^{-s} into a product over primes (the engine is
  `EulerProduct.eulerProduct_completely_multiplicative`, which uses unique
  factorization to identify the partial products over smooth numbers with the
  partial sums).  What Mathlib does *not* record is the historically decisive
  consequence: evaluating the Euler product at s = 2 and s = 4 against the
  closed-form special values ζ(2) = π²/6 and ζ(4) = π⁴/90.

  This is Euler's 1737 discovery — the first concrete payoff of the
  FTA → Euler-product bridge — that the product of p²/(p²−1) over all primes
  equals π²/6.  It ties three gallery threads together: the Fundamental Theorem
  of Arithmetic (the bijection underlying the Euler product), the Basel problem
  (the value π²/6), and the Riemann zeta function.

  Everything here is fully verified (0 axioms, 0 sorries) and assembled from
  Mathlib's `riemannZeta_eulerProduct_*` and `riemannZeta_two`/`riemannZeta_four`.
-/
import Mathlib

open Real Complex Filter Topology

namespace FundamentalArithmeticOQ03

/-! ## s = 2 : Euler's product for the Basel value π²/6 -/

/-- The convergence hypothesis `1 < (2 : ℂ).re` for the Euler product at `s = 2`. -/
private lemma one_lt_re_two : 1 < (2 : ℂ).re := by norm_num

/-- **Euler's product for the Basel problem.**

The infinite product over the primes of `(1 - p^{-2})⁻¹` equals `π²/6`.
Combining the FTA-driven Euler product (`riemannZeta_eulerProduct_tprod`) at
`s = 2` with the Basel value `riemannZeta_two`. -/
theorem euler_basel_product_tprod :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(2 : ℂ)))⁻¹ = (π : ℂ) ^ 2 / 6 := by
  rw [riemannZeta_eulerProduct_tprod one_lt_re_two, riemannZeta_two]

/-- `HasProd` form of Euler's Basel product: the family `p ↦ (1 - p^{-2})⁻¹`
has product `π²/6`.  This is the unconditional convergence statement (any
reordering of the prime factors gives the same value). -/
theorem euler_basel_product_hasProd :
    HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-(2 : ℂ)))⁻¹) ((π : ℂ) ^ 2 / 6) := by
  have h := riemannZeta_eulerProduct_hasProd one_lt_re_two
  rwa [riemannZeta_two] at h

/-- Finite partial-product form: the products `∏_{p < n} (1 - p^{-2})⁻¹` over the
primes below `n` converge to `π²/6` as `n → ∞`.  This is the form closest to
Euler's original computation. -/
theorem euler_basel_product_tendsto :
    Tendsto (fun n : ℕ ↦ ∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-(2 : ℂ)))⁻¹)
      atTop (𝓝 ((π : ℂ) ^ 2 / 6)) := by
  have h := riemannZeta_eulerProduct one_lt_re_two
  rwa [riemannZeta_two] at h

/-! ## s = 4 : Euler's product for ζ(4) = π⁴/90 -/

/-- The convergence hypothesis `1 < (4 : ℂ).re` for the Euler product at `s = 4`. -/
private lemma one_lt_re_four : 1 < (4 : ℂ).re := by norm_num

/-- **Euler's product at `s = 4`.**

The infinite product over the primes of `(1 - p^{-4})⁻¹` equals `π⁴/90`,
combining the Euler product at `s = 4` with `riemannZeta_four`. -/
theorem euler_zeta_four_product_tprod :
    ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-(4 : ℂ)))⁻¹ = (π : ℂ) ^ 4 / 90 := by
  rw [riemannZeta_eulerProduct_tprod one_lt_re_four, riemannZeta_four]

/-- `HasProd` form of the Euler product at `s = 4`. -/
theorem euler_zeta_four_product_hasProd :
    HasProd (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-(4 : ℂ)))⁻¹) ((π : ℂ) ^ 4 / 90) := by
  have h := riemannZeta_eulerProduct_hasProd one_lt_re_four
  rwa [riemannZeta_four] at h

/-! ## Structural consequences

The Euler product makes the non-vanishing of these special values transparent:
a convergent product of nonzero factors is nonzero.  Here we record the values
`π²/6` and `π⁴/90` as nonzero, witnessed through the zeta function. -/

/-- `π²/6 ≠ 0`, seen through the Euler product / zeta non-vanishing for `Re s > 1`. -/
theorem basel_value_ne_zero : ((π : ℂ) ^ 2 / 6) ≠ 0 := by
  rw [← riemannZeta_two]
  exact riemannZeta_ne_zero_of_one_lt_re one_lt_re_two

/-- `π⁴/90 ≠ 0`, seen through the zeta non-vanishing for `Re s > 1`. -/
theorem zeta_four_value_ne_zero : ((π : ℂ) ^ 4 / 90) ≠ 0 := by
  rw [← riemannZeta_four]
  exact riemannZeta_ne_zero_of_one_lt_re one_lt_re_four

end FundamentalArithmeticOQ03
