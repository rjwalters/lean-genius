/-
# Erdős Problem 913: Distinct Exponents in n(n+1) Factorizations

*Reference:* [erdosproblems.com/913](https://www.erdosproblems.com/913)

Are there infinitely many `n` such that if `n(n+1) = ∏ pᵢ^kᵢ` is the
factorization into distinct primes, then all exponents `kᵢ` are distinct?

From Erdős [Er82c, p.28]. A likely sufficient condition: if there are infinitely
many primes `p` such that `8p² - 1` is also prime, then using exponents
`{1, 2, 3}` with `n = 8p² - 1` produces an example. The conditional result
is proved in detail below.

This remains an open problem.

Axioms: 1 (infinite_8p_sq_minus_1_primes — Bunyakovsky-type conjecture, genuinely open)
Sorries: 0
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-
## Section 1: Distinct exponent property

We define the property that the prime factorization of `n(n+1)` has
all exponents distinct, using Mathlib's `factorization` and `primeFactors`.
-/

namespace Erdos913

open Nat Finset

/-- `n` has the distinct-exponent property if the factorization map
    `n(n+1).factorization` is injective on the prime factors of `n(n+1)`. -/
def HasDistinctExponents (n : ℕ) : Prop :=
  Set.InjOn (n * (n + 1)).factorization (n * (n + 1)).primeFactors

/-- The set of all n with the distinct-exponent property. -/
def DistinctExponentSet : Set ℕ :=
  { n | HasDistinctExponents n }

/-
## Section 2: The main conjecture

Erdős Problem 913 asks whether the set of n with distinct exponents is infinite.
-/

/-- Erdős Problem 913: Are there infinitely many n such that the prime
    factorization of n(n+1) has all exponents distinct? -/
def ErdosProblem913 : Prop := DistinctExponentSet.Infinite

/-
## Section 3: The 8p²-1 prime hypothesis

A likely sufficient condition: infinitely many primes p with 8p²-1 also prime.
-/

/-- The set of primes p such that 8p² - 1 is also prime. -/
def PrimePairs8 : Set ℕ := { p | p.Prime ∧ (8 * p ^ 2 - 1).Prime }

/-- Hypothesis: there are infinitely many primes p with 8p² - 1 prime. -/
axiom infinite_8p_sq_minus_1_primes : PrimePairs8.Infinite

/-
## Section 4: Conditional proof

If PrimePairs8 is infinite, then DistinctExponentSet is infinite.
For each such p, take n = 8p² - 1. Then:
  n(n+1) = (8p² - 1)(8p²) = (8p² - 1) · p² · 8 = (8p² - 1) · p² · 2³

So the prime factorization has exponents {1, 2, 3} on primes {8p²-1, p, 2},
which are all distinct.
-/

/-- Helper: prove distinct exponents from a triple of prime factors with
    pairwise distinct factorization values. -/
private theorem hasDistinctExponents_of_primeFactors_triple
    {n : ℕ} {m p q r : ℕ} (hm : n * (n + 1) = m)
    (hpf : m.primeFactors = {p, q, r})
    (hpq : m.factorization p ≠ m.factorization q)
    (hpr : m.factorization p ≠ m.factorization r)
    (hqr : m.factorization q ≠ m.factorization r) :
    HasDistinctExponents n := by
  unfold HasDistinctExponents
  rw [hm, hpf]
  intro x hx y hy heq
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
             Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  · rfl
  · exact absurd heq hpq
  · exact absurd heq hpr
  · exact absurd heq hpq.symm
  · rfl
  · exact absurd heq hqr
  · exact absurd heq hpr.symm
  · exact absurd heq hqr.symm
  · rfl

/-- The map p ↦ 8p²-1 is injective on naturals ≥ 1. -/
private theorem injective_8p_sq_minus_1 : Function.Injective (fun p : ℕ => 8 * p ^ 2 - 1) := by
  intro a b hab
  simp only at hab
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : a ^ 2 < b ^ 2 := by nlinarith
    omega
  · have : b ^ 2 < a ^ 2 := by nlinarith
    omega

/-- When p is prime and 8p²-1 is prime, n = 8p²-1 gives a product
    n(n+1) with exactly three prime factors {8p²-1, p, 2}. -/
theorem exponent_structure (p : ℕ) (hp : p.Prime) (hp' : (8 * p ^ 2 - 1).Prime)
    (hp'' : p ≠ 2) :
    let n := 8 * p ^ 2 - 1
    (n * (n + 1)).primeFactors = {8 * p ^ 2 - 1, p, 2} := by
  simp only []
  have hn_succ : 8 * p ^ 2 - 1 + 1 = 8 * p ^ 2 :=
    Nat.sub_add_cancel (show 1 ≤ 8 * p ^ 2 by nlinarith [hp.pos])
  rw [hn_succ]
  have hne1 : 8 * p ^ 2 - 1 ≠ 0 := by nlinarith [hp.pos]
  have hne2 : 8 * p ^ 2 ≠ 0 := by nlinarith [hp.pos]
  rw [primeFactors_mul hne1 hne2, hp'.primeFactors,
      primeFactors_mul (by norm_num : (8 : ℕ) ≠ 0) (pow_ne_zero 2 hp.ne_zero),
      show (8 : ℕ).primeFactors = {2} from by native_decide,
      primeFactors_pow _ (show (2 : ℕ) ≠ 0 from by norm_num), hp.primeFactors]
  ext x
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  tauto

/-- Helper: for p prime, p ≠ 2, 8p²-1 prime, n = 8p²-1 has distinct exponents. -/
private theorem hasDistinctExponents_8p_sq (p : ℕ) (hp : p.Prime) (hp' : (8 * p ^ 2 - 1).Prime)
    (hp'' : p ≠ 2) : HasDistinctExponents (8 * p ^ 2 - 1) := by
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hne1 : 8 * p ^ 2 - 1 ≠ 0 := by omega
  have hne2 : 8 * p ^ 2 ≠ 0 := by omega
  have hm : (8 * p ^ 2 - 1) * ((8 * p ^ 2 - 1) + 1) = (8 * p ^ 2 - 1) * (8 * p ^ 2) := by
    congr 1; omega
  set m := (8 * p ^ 2 - 1) * (8 * p ^ 2) with hm_def
  -- Coprimality: consecutive integers are coprime
  have hcop : Nat.Coprime (8 * p ^ 2 - 1) (8 * p ^ 2) := by
    rw [show 8 * p ^ 2 = (8 * p ^ 2 - 1) + 1 from by omega]
    exact (coprime_self_add_right.mpr (coprime_one_right _))
  -- Non-divisibility via coprimality and primality
  have hndvd_main : ¬((8 * p ^ 2 - 1) ∣ (8 * p ^ 2)) := by
    intro hd; exact absurd (Nat.le_of_dvd one_pos (hcop ▸ Nat.dvd_gcd dvd_rfl hd)) (by omega)
  have hndvd_p8 : ¬(p ∣ (8 : ℕ)) := by
    intro hd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from hd)
    exact hp'' ((Nat.prime_two.eq_one_or_self_of_dvd p h2).resolve_left hp.one_lt.ne')
  -- Factorization value at (8p²-1) = 1
  have hv1 : m.factorization (8 * p ^ 2 - 1) = 1 := by
    rw [hm_def, factorization_mul hne1 hne2, Finsupp.add_apply, hp'.factorization,
        Finsupp.single_apply, if_pos rfl, factorization_eq_zero_of_not_dvd hndvd_main, add_zero]
  -- Factorization value at p = 2
  have hv2 : m.factorization p = 2 := by
    rw [hm_def, factorization_mul hne1 hne2, Finsupp.add_apply, hp'.factorization,
        Finsupp.single_apply, if_neg (show 8 * p ^ 2 - 1 ≠ p by nlinarith [hp.two_le]),
        zero_add, show (8 : ℕ) * p ^ 2 = 8 * (p * p) from by ring,
        factorization_mul (by norm_num) (mul_ne_zero hp.ne_zero hp.ne_zero), Finsupp.add_apply,
        factorization_eq_zero_of_not_dvd hndvd_p8, zero_add,
        factorization_mul hp.ne_zero hp.ne_zero, Finsupp.add_apply,
        hp.factorization, Finsupp.single_apply, if_pos rfl]
  -- Factorization value at 2 = 3
  have hv3 : m.factorization 2 = 3 := by
    rw [hm_def, factorization_mul hne1 hne2, Finsupp.add_apply, hp'.factorization,
        Finsupp.single_apply, if_neg (show 8 * p ^ 2 - 1 ≠ 2 by omega), zero_add,
        show (8 : ℕ) * p ^ 2 = 8 * (p * p) from by ring,
        factorization_mul (by norm_num) (mul_ne_zero hp.ne_zero hp.ne_zero), Finsupp.add_apply,
        show (8 : ℕ).factorization 2 = 3 from by native_decide,
        factorization_mul hp.ne_zero hp.ne_zero, Finsupp.add_apply,
        hp.factorization, Finsupp.single_apply, if_neg hp'']
    norm_num
  -- Apply the triple helper
  have hpf := exponent_structure p hp hp' hp''
  simp only at hpf
  rw [show 8 * p ^ 2 - 1 + 1 = 8 * p ^ 2 from by omega] at hpf
  rw [← hm_def] at hpf
  exact hasDistinctExponents_of_primeFactors_triple hm hpf (by omega) (by omega) (by omega)

/-- Conditional result: if there are infinitely many primes p with
    8p² - 1 prime, then infinitely many n have distinct exponents. -/
theorem erdos_913_conditional (h : PrimePairs8.Infinite) :
    DistinctExponentSet.Infinite := by
  have hS : (PrimePairs8 \ {2}).Infinite := h.diff (Set.finite_singleton 2)
  have hinj : Set.InjOn (fun p => 8 * p ^ 2 - 1) (PrimePairs8 \ {2}) :=
    fun _ _ _ _ h => injective_8p_sq_minus_1 h
  have himg : ((fun p => 8 * p ^ 2 - 1) '' (PrimePairs8 \ {2})).Infinite := hS.image hinj
  exact himg.mono (by
    rintro _ ⟨p, ⟨⟨hp, hp'⟩, hp''⟩, rfl⟩
    simp only [PrimePairs8, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff] at hp hp' hp''
    exact hasDistinctExponents_8p_sq p hp hp' hp'')

/-
## Section 5: Known examples

Small examples of n with distinct exponents in n(n+1):
- n = 3: 3·4 = 2²·3, exponents {2,1} distinct
- n = 7: 7·8 = 2³·7, exponents {3,1} distinct
- n = 8: 8·9 = 2³·3², exponents {3,2} distinct
- n = 31: 31·32 = 2⁵·31, exponents {5,1} distinct
- n = 127: 127·128 = 2⁷·127, exponents {7,1} distinct
-/

/-- Helper: prove distinct exponents by reducing to concrete prime factor enumeration. -/
private theorem hasDistinctExponents_of_primeFactors_pair
    {n : ℕ} {m p q : ℕ} (hm : n * (n + 1) = m) (hpf : m.primeFactors = {p, q})
    (hne : m.factorization p ≠ m.factorization q) :
    HasDistinctExponents n := by
  unfold HasDistinctExponents
  rw [hm, hpf]
  intro x hx y hy heq
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
             Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact absurd heq hne
  · exact absurd heq (Ne.symm hne)
  · rfl

/-- n = 3 has distinct exponents: 3·4 = 2²·3¹. -/
theorem example_n3 : HasDistinctExponents 3 :=
  hasDistinctExponents_of_primeFactors_pair (m := 12) (p := 2) (q := 3)
    (by norm_num) (by native_decide) (by native_decide)

/-- n = 7 has distinct exponents: 7·8 = 2³·7¹. -/
theorem example_n7 : HasDistinctExponents 7 :=
  hasDistinctExponents_of_primeFactors_pair (m := 56) (p := 2) (q := 7)
    (by norm_num) (by native_decide) (by native_decide)

/-- n = 8 has distinct exponents: 8·9 = 2³·3². -/
theorem example_n8 : HasDistinctExponents 8 :=
  hasDistinctExponents_of_primeFactors_pair (m := 72) (p := 2) (q := 3)
    (by norm_num) (by native_decide) (by native_decide)

/-- n = 31 has distinct exponents: 31·32 = 2⁵·31¹. -/
theorem example_n31 : HasDistinctExponents 31 :=
  hasDistinctExponents_of_primeFactors_pair (m := 992) (p := 2) (q := 31)
    (by norm_num) (by native_decide) (by native_decide)

/-- n = 71 has distinct exponents: 71·72 = 2³·3²·71¹ (3-factor case).
    This is the instance from the 8p²-1 construction with p = 3:
    n = 8·9-1 = 71, n+1 = 72 = 8·9 = 2³·3². -/
theorem example_n71 : HasDistinctExponents 71 :=
  hasDistinctExponents_of_primeFactors_triple (m := 5112) (p := 2) (q := 3) (r := 71)
    (by norm_num) (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- n = 127 has distinct exponents: 127·128 = 2⁷·127¹. -/
theorem example_n127 : HasDistinctExponents 127 :=
  hasDistinctExponents_of_primeFactors_pair (m := 16256) (p := 2) (q := 127)
    (by norm_num) (by native_decide) (by native_decide)

/-
## Section 6: Connection to Bunyakovsky conjecture

The hypothesis that infinitely many p have 8p² - 1 prime is a special case
of the Bunyakovsky conjecture (or Bateman–Horn conjecture) for the polynomial
f(x) = 8x² - 1. These conjectures predict infinitely many prime values
for irreducible polynomials satisfying a fixed-divisor condition.
-/

/-- The Bunyakovsky-type hypothesis for 8x² - 1: there are infinitely
    many prime values of 8x² - 1 as x ranges over the primes.
    This is a weaker form than the full Bunyakovsky conjecture. -/
def Bunyakovsky8 : Prop := PrimePairs8.Infinite

/-
## Section 7: Mersenne prime conditional

For k ≥ 2 with 2^k - 1 prime (Mersenne prime), n = 2^k - 1 gives
n(n+1) = (2^k - 1)·2^k with exponents {1, k}, automatically distinct.
This provides a second conditional path to Erdős #913, independent of
the 8p²-1 hypothesis: if infinitely many Mersenne primes exist, the
conjecture is true.
-/

/-- The set of exponents k ≥ 2 where 2^k - 1 is a Mersenne prime. -/
def MersennePrimeExponents : Set ℕ := { k | k ≥ 2 ∧ (2 ^ k - 1).Prime }

/-- The map k ↦ 2^k - 1 is injective on ℕ. -/
private theorem injective_mersenne : Function.Injective (fun k : ℕ => 2 ^ k - 1) := by
  intro a b hab
  simp only at hab
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
    omega
  · have : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
    omega

/-- For a Mersenne prime 2^k - 1 with k ≥ 2, n = 2^k - 1 has distinct exponents:
    n(n+1) = (2^k - 1)·2^k with exponents {1, k}. -/
theorem hasDistinctExponents_mersenne (k : ℕ) (hk : k ≥ 2) (hp : (2 ^ k - 1).Prime) :
    HasDistinctExponents (2 ^ k - 1) := by
  have hne1 : 2 ^ k - 1 ≠ 0 := hp.ne_zero
  have hne2 : (2 : ℕ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hm : (2 ^ k - 1) * ((2 ^ k - 1) + 1) = (2 ^ k - 1) * 2 ^ k := by congr 1; omega
  set m := (2 ^ k - 1) * 2 ^ k with hm_def
  -- (2^k - 1) doesn't divide 2^k: it's an odd prime > 2
  have hndvd : ¬((2 ^ k - 1) ∣ 2 ^ k) := by
    intro h
    have := Nat.le_of_dvd (by positivity) (hp.dvd_of_dvd_pow h)
    omega
  -- Factorization at (2^k - 1) = 1
  have hv1 : m.factorization (2 ^ k - 1) = 1 := by
    rw [hm_def, factorization_mul hne1 hne2, Finsupp.add_apply,
        hp.factorization, Finsupp.single_apply, if_pos rfl,
        factorization_eq_zero_of_not_dvd hndvd, add_zero]
  -- Factorization at 2 = k
  have hv2 : m.factorization 2 = k := by
    rw [hm_def, factorization_mul hne1 hne2, Finsupp.add_apply,
        hp.factorization, Finsupp.single_apply, if_neg (show 2 ^ k - 1 ≠ 2 from by omega),
        zero_add]
    simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        Nat.prime_two.factorization, Finsupp.single_eq_same, mul_one]
  -- Prime factors
  have hpf : m.primeFactors = {2 ^ k - 1, 2} := by
    rw [hm_def, primeFactors_mul hne1 hne2, hp.primeFactors,
        primeFactors_pow (show (2 : ℕ) ≠ 0 from by norm_num) (show k ≠ 0 from by omega),
        Nat.prime_two.primeFactors, Finset.singleton_union]
  exact hasDistinctExponents_of_primeFactors_pair hm hpf (by omega)

/-- Conditional: infinitely many Mersenne primes implies Erdős #913 is true. -/
theorem erdos_913_conditional_mersenne (h : MersennePrimeExponents.Infinite) :
    DistinctExponentSet.Infinite := by
  have hinj : Set.InjOn (fun k => 2 ^ k - 1) MersennePrimeExponents :=
    fun _ _ _ _ h => injective_mersenne h
  have himg : ((fun k => 2 ^ k - 1) '' MersennePrimeExponents).Infinite := h.image hinj
  exact himg.mono (by
    rintro _ ⟨k, hk_mem, rfl⟩
    exact hasDistinctExponents_mersenne k hk_mem.1 hk_mem.2)

/-- The distinct exponent set is nonempty (witnessed by n = 3). -/
theorem nonempty_distinctExponentSet : DistinctExponentSet.Nonempty :=
  ⟨3, example_n3⟩

end Erdos913
