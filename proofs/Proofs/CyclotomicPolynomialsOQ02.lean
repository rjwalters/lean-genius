/-
Cyclotomic Polynomials OQ-02: Prime-Power Cyclotomics and the Eval-at-One Law

The companion entry OQ-01 packaged the basic structural facts of Φ_n (degree
φ(n), the prime form Φ_p = 1 + X + ⋯ + X^{p-1}, and the divisor product
∏_{d∣n} Φ_d = Xⁿ − 1). This entry zooms in on the prime-power case Φ_{p^k} and
on the value Φ_n(1), which exhibits a striking dichotomy.

  • Prime-power form.   For a prime p and k ≥ 1,
                        Φ_{p^k}(X) = ∑_{i<p} X^{i·p^{k-1}}
                        — the p-term geometric sum in the variable X^{p^{k-1}}.
  • Prime-power degree. deg Φ_{p^k} = φ(p^k) = p^{k-1}(p − 1).
  • Eval-at-one law.    Φ_{p^k}(1) = p, whereas Φ_n(1) = 1 as soon as n has at
                        least two distinct prime factors.

The eval-at-one dichotomy {p, 1} is the polynomial shadow of the von Mangoldt
function: Φ_n(1) = e^{Λ(n)}, equal to the prime p exactly when n is a prime
power p^k (k ≥ 1), and equal to 1 otherwise. Here we prove the two clean ends of
that statement: the prime-power value p, and the value 1 for any n with ≥ 2
distinct prime factors.

Main results:
  • `cyclotomic_prime_pow_geom_sum`  — Φ_{p^{k+1}} = ∑_{i<p} (X^{p^k})^i.
  • `cyclotomic_prime_pow_natDegree` — deg Φ_{p^{k+1}} = p^k·(p − 1).
  • `cyclotomic_prime_pow_eval_one`  — Φ_{p^{k+1}}(1) = p.
  • `cyclotomic_eval_one_eq_one_of_two_le_primeFactors`
                                      — Φ_n(1) = 1 when n has ≥ 2 distinct primes.
  Plus concrete witnesses Φ₄, Φ₈, Φ₉ and sample degree/eval computations
  illustrating both ends of the dichotomy (Φ₈(1)=2 vs Φ₁₅(1)=1).

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Mathlib `Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean` and `Eval.lean`.
- The value Φ_n(1) and its connection to the von Mangoldt function Λ(n).
-/

import Mathlib

open Polynomial Finset Nat

namespace CyclotomicPolynomialsOQ02

/-! ### The prime-power cyclotomic polynomial as a geometric sum -/

/-- For a prime `p`, the prime-power cyclotomic polynomial is a geometric sum in
the variable `X^{p^k}`:  `Φ_{p^{k+1}} = ∑_{i<p} (X^{p^k})^i`.  Equivalently the
exponents are the multiples `0, p^k, 2·p^k, …, (p−1)·p^k`. -/
theorem cyclotomic_prime_pow_geom_sum (R : Type*) [CommRing R] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    cyclotomic (p ^ (k + 1)) R = ∑ i ∈ range p, (X ^ p ^ k) ^ i :=
  cyclotomic_prime_pow_eq_geom_sum hp

/-! ### Degree of the prime-power cyclotomic polynomial -/

/-- The degree of `Φ_{p^{k+1}}` is Euler's totient `φ(p^{k+1}) = p^k·(p − 1)`. -/
theorem cyclotomic_prime_pow_natDegree (R : Type*) [Ring R] [Nontrivial R] {p : ℕ} (hp : p.Prime)
    (k : ℕ) : (cyclotomic (p ^ (k + 1)) R).natDegree = p ^ k * (p - 1) := by
  rw [natDegree_cyclotomic, totient_prime_pow_succ hp]

/-! ### The eval-at-one law: prime powers evaluate to the prime -/

/-- **Prime-power value.** Evaluating `Φ_{p^{k+1}}` at `1` gives the prime `p`. -/
theorem cyclotomic_prime_pow_eval_one (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] (k : ℕ) :
    (cyclotomic (p ^ (k + 1)) R).eval 1 = p :=
  eval_one_cyclotomic_prime_pow k

/-! ### The eval-at-one law: the value 1 for ≥ 2 distinct prime factors -/

/-- **Composite value.** If `n` has at least two distinct prime factors then it is
not a prime power, so `Φ_n(1) = 1`.  Together with `cyclotomic_prime_pow_eval_one`
(value `p` on prime powers) this is the eval-at-one dichotomy `Φ_n(1) ∈ {p, 1}`. -/
theorem cyclotomic_eval_one_eq_one_of_two_le_primeFactors (R : Type*) [Ring R] {n : ℕ}
    (hn : 2 ≤ n.primeFactors.card) : (cyclotomic n R).eval 1 = 1 := by
  apply eval_one_cyclotomic_not_prime_pow
  intro p hp k hpk
  -- From `p ^ k = n` derive that `n` has at most one prime factor, contradicting `hn`.
  apply absurd hn
  rw [← hpk]
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [Nat.primeFactors_prime_pow hk hp]
    simp

/-- Helper: two distinct prime factors witness `2 ≤ n.primeFactors.card`. -/
private theorem two_le_primeFactors_card {n a b : ℕ} (hab : a ≠ b)
    (ha : a ∈ n.primeFactors) (hb : b ∈ n.primeFactors) : 2 ≤ n.primeFactors.card := by
  have hsub : ({a, b} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  calc (2 : ℕ) = ({a, b} : Finset ℕ).card := (Finset.card_pair hab).symm
    _ ≤ n.primeFactors.card := Finset.card_le_card hsub

/-! ### Concrete witnesses: prime-power geometric form -/

/-- `Φ₄ = X² + 1`  (the case `p = 2, k = 2`: `Φ_{2²} = 1 + (X²)`). -/
theorem cyclotomic_four : cyclotomic 4 ℤ = 1 + X ^ 2 := by
  have h : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_geom_sum ℤ (by norm_num) 1]
  simp [Finset.sum_range_succ]

/-- `Φ₉ = 1 + X³ + X⁶`  (the case `p = 3, k = 2`: `Φ_{3²} = 1 + X³ + (X³)²`). -/
theorem cyclotomic_nine : cyclotomic 9 ℤ = 1 + X ^ 3 + X ^ 6 := by
  have h : (9 : ℕ) = 3 ^ (1 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_geom_sum ℤ (by norm_num) 1]
  simp [Finset.sum_range_succ]
  ring

/-! ### Concrete witnesses: degree -/

/-- Sample degree: `deg Φ₈ = φ(8) = 4`  (`p = 2, k = 3`). -/
theorem cyclotomic_eight_natDegree : (cyclotomic 8 ℤ).natDegree = 4 := by
  have h : (8 : ℕ) = 2 ^ (2 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_natDegree ℤ (by norm_num) 2]
  norm_num

/-- Sample degree: `deg Φ₂₇ = φ(27) = 18`  (`p = 3, k = 3`). -/
theorem cyclotomic_twentyseven_natDegree : (cyclotomic 27 ℤ).natDegree = 18 := by
  have h : (27 : ℕ) = 3 ^ (2 + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_natDegree ℤ (by norm_num) 2]
  norm_num

/-! ### Concrete witnesses: the eval-at-one dichotomy -/

/-- Prime-power end of the dichotomy: `Φ₈(1) = 2`. -/
theorem cyclotomic_eight_eval_one : (cyclotomic 8 ℤ).eval 1 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h : (8 : ℕ) = 2 ^ (2 + 1) := by norm_num
  rw [h]
  exact cyclotomic_prime_pow_eval_one ℤ 2 2

/-- Composite end of the dichotomy: `Φ₁₅(1) = 1`  (`15 = 3·5`, two prime factors). -/
theorem cyclotomic_fifteen_eval_one : (cyclotomic 15 ℤ).eval 1 = 1 := by
  apply cyclotomic_eval_one_eq_one_of_two_le_primeFactors
  exact two_le_primeFactors_card (a := 3) (b := 5) (by norm_num)
    (by rw [Nat.mem_primeFactors]; norm_num) (by rw [Nat.mem_primeFactors]; norm_num)

/-- Composite end of the dichotomy: `Φ₆(1) = 1`  (`6 = 2·3`, two prime factors). -/
theorem cyclotomic_six_eval_one : (cyclotomic 6 ℤ).eval 1 = 1 := by
  apply cyclotomic_eval_one_eq_one_of_two_le_primeFactors
  exact two_le_primeFactors_card (a := 2) (b := 3) (by norm_num)
    (by rw [Nat.mem_primeFactors]; norm_num) (by rw [Nat.mem_primeFactors]; norm_num)

end CyclotomicPolynomialsOQ02
