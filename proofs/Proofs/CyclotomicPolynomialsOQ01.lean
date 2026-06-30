/-
Cyclotomic Polynomials OQ-01: Degree, Prime Form, and the Divisor Product

The n-th cyclotomic polynomial Φ_n is the minimal monic polynomial whose roots
are the primitive n-th roots of unity. Three of its most fundamental structural
facts are:

  • Degree.        deg Φ_n = φ(n)   (Euler's totient), so Φ_n has exactly φ(n)
                   primitive-root coefficients.
  • Prime form.    For a prime p,  Φ_p = 1 + X + X² + ⋯ + X^{p-1}  (the p-term
                   geometric sum), hence deg Φ_p = p − 1 and Φ_p(1) = p.
  • Divisor product.  ∏_{d ∣ n} Φ_d = Xⁿ − 1, the factorization of Xⁿ − 1 into
                   cyclotomic factors indexed by the divisors of n.

This entry packages these facts from Mathlib's cyclotomic library into a single
coherent topic entry (the gallery previously used `cyclotomic` only as machinery
inside Galois/trisection proofs, never as a subject in its own right) and derives
a genuine structural consequence:

  • Gauss's identity.  Taking degrees of the divisor product gives
                   ∑_{d ∣ n} φ(d) = n
                   — the classical totient-divisor-sum identity, obtained here
                   purely from the cyclotomic factorization of Xⁿ − 1.

Main results:
  • `cyclotomic_natDegree`         — deg Φ_n = φ(n) over any nontrivial ring.
  • `cyclotomic_prime_natDegree`   — deg Φ_p = p − 1 for prime p.
  • `cyclotomic_prime_geom_sum`    — Φ_p = ∑_{i<p} Xⁱ for prime p.
  • `cyclotomic_prime_eval_one`    — Φ_p(1) = p for prime p.
  • `prod_cyclotomic_divisors`     — ∏_{d ∣ n} Φ_d = Xⁿ − 1 for n > 0.
  • `sum_totient_divisors`         — ∑_{d ∣ n} φ(d) = n (Gauss), via degrees.
  Plus concrete witnesses Φ₁, Φ₂, Φ₃ and sample degree/eval computations.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Mathlib `Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean` and `Eval.lean`.
- Gauss's totient-divisor-sum identity ∑_{d∣n} φ(d) = n.
-/

import Mathlib

open Polynomial Finset Nat

namespace CyclotomicPolynomialsOQ01

/-! ### Degree of the cyclotomic polynomial -/

/-- The degree of the n-th cyclotomic polynomial is Euler's totient φ(n). -/
theorem cyclotomic_natDegree (n : ℕ) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic n R).natDegree = Nat.totient n :=
  natDegree_cyclotomic n R

/-- For a prime p, the cyclotomic polynomial Φ_p has degree p − 1. -/
theorem cyclotomic_prime_natDegree (p : ℕ) (hp : p.Prime) (R : Type*) [Ring R] [Nontrivial R] :
    (cyclotomic p R).natDegree = p - 1 := by
  rw [natDegree_cyclotomic, Nat.totient_prime hp]

/-! ### Prime cyclotomic polynomials are geometric sums -/

/-- For a prime p, `Φ_p = 1 + X + X² + ⋯ + X^{p-1}`, the p-term geometric sum. -/
theorem cyclotomic_prime_geom_sum (R : Type*) [Ring R] (p : ℕ) [Fact p.Prime] :
    cyclotomic p R = ∑ i ∈ range p, X ^ i :=
  cyclotomic_prime R p

/-- Evaluating a prime cyclotomic polynomial at 1 gives the prime: `Φ_p(1) = p`. -/
theorem cyclotomic_prime_eval_one (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] :
    (cyclotomic p R).eval 1 = p :=
  eval_one_cyclotomic_prime

/-! ### The divisor product Xⁿ − 1 = ∏_{d ∣ n} Φ_d -/

/-- The factorization of `Xⁿ − 1` into cyclotomic polynomials indexed by the
divisors of n. -/
theorem prod_cyclotomic_divisors (n : ℕ) (hn : 0 < n) (R : Type*) [CommRing R] :
    ∏ d ∈ n.divisors, cyclotomic d R = X ^ n - 1 :=
  prod_cyclotomic_eq_X_pow_sub_one hn R

/-! ### Gauss's totient-divisor-sum identity, via cyclotomic degrees -/

/-- **Gauss's identity** `∑_{d ∣ n} φ(d) = n`, obtained by taking degrees in the
cyclotomic factorization `∏_{d ∣ n} Φ_d = Xⁿ − 1` over `ℤ`. The product's degree
is the sum of the factor degrees (each `Φ_d ≠ 0` in the domain `ℤ`), and each
factor contributes `deg Φ_d = φ(d)`; the right-hand side `Xⁿ − 1` has degree `n`. -/
theorem sum_totient_divisors (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, Nat.totient d = n := by
  have key : ∏ d ∈ n.divisors, cyclotomic d ℤ = X ^ n - 1 :=
    prod_cyclotomic_eq_X_pow_sub_one hn ℤ
  have hdeg := congrArg natDegree key
  rw [natDegree_prod _ _ (fun d _ => cyclotomic_ne_zero d ℤ)] at hdeg
  simp only [natDegree_cyclotomic] at hdeg
  rwa [show (X : ℤ[X]) ^ n - 1 = X ^ n - C 1 by simp, natDegree_X_pow_sub_C] at hdeg

/-! ### Concrete witnesses -/

/-- `Φ₁ = X − 1`. -/
example : cyclotomic 1 ℤ = X - 1 := cyclotomic_one ℤ

/-- `Φ₂ = X + 1`. -/
example : cyclotomic 2 ℤ = X + 1 := cyclotomic_two ℤ

/-- `Φ₃ = 1 + X + X²`. -/
theorem cyclotomic_three : cyclotomic 3 ℤ = 1 + X + X ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [cyclotomic_prime ℤ 3]
  simp [Finset.sum_range_succ]

/-- Sample degree computation: `deg Φ₇ = 6`. -/
theorem cyclotomic_seven_natDegree : (cyclotomic 7 ℤ).natDegree = 6 :=
  cyclotomic_prime_natDegree 7 (by norm_num) ℤ

/-- Sample evaluation: `Φ₅(1) = 5`. -/
theorem cyclotomic_five_eval_one : (cyclotomic 5 ℤ).eval 1 = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact cyclotomic_prime_eval_one ℤ 5

/-- Sample Gauss identity: `∑_{d ∣ 12} φ(d) = 12`. -/
theorem sum_totient_twelve : ∑ d ∈ (12 : ℕ).divisors, Nat.totient d = 12 :=
  sum_totient_divisors 12 (by norm_num)

end CyclotomicPolynomialsOQ01
