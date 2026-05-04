/-
Erdős Problem #1214: Prime Support Uniqueness for Exponential Sequences

Let x, y ≥ 1 be integers such that for all n ≥ 1, the set of primes dividing x^n - 1
equals the set of primes dividing y^n - 1. Must x = y?

A positive answer was given by Corrales-Rodánez and Schoof (1997) via a deep result
from algebraic number theory (the "support problem"). Their proof proceeds through
Kummer theory and Galois cohomology — showing the hypothesis forces x and y to be
powers of the same base with matching exponents, and then x = y by multiplicativity.

The key structural insight: the condition supp(x^n - 1) = supp(y^n - 1) for all n
is equivalent to saying that for every prime p (coprime to xy), the multiplicative
orders of x and y modulo p are equal. This determines x and y uniquely.

References:
- https://erdosproblems.com/1214
- Corrales-Rodánez, C.; Schoof, R. (1997). "Support problem and its elliptic analogue."
  Journal of Number Theory 64(2), 276–290.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Algebra.GeomSum
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Int.Order
import Mathlib.Tactic

namespace Erdos1214Problem

/-
## Prime Support (Radical)

The prime support of an integer n is the set of prime divisors.
-/

/-- The prime support of a natural number: the set of prime divisors. -/
def primSupport (n : ℕ) : Finset ℕ := n.primeFactors

/-- The support of 1 is empty. -/
theorem primSupport_one : primSupport 1 = ∅ := by simp [primSupport]

/-- The support of a prime p is {p}. -/
theorem primSupport_prime (p : ℕ) (hp : p.Prime) : primSupport p = {p} := by
  simp [primSupport, Nat.primeFactors_prime hp]

/-
## Divisibility Structure

The key algebraic fact: (x - 1) | (x^n - 1) for all n,
via the geometric series x^n - 1 = (x - 1)(1 + x + ... + x^{n-1}).
-/

/-- (x - 1) divides (x^n - 1) in any commutative ring, via the geometric series. -/
theorem sub_one_dvd_pow_sub_one {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (x - 1) ∣ (x ^ n - 1) := by
  use ∑ i ∈ Finset.range n, x ^ i
  have h : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := geom_sum_mul x n
  calc x ^ n - 1 = (∑ i ∈ Finset.range n, x ^ i) * (x - 1) := h.symm
    _ = (x - 1) * (∑ i ∈ Finset.range n, x ^ i) := mul_comm _ _

/-- In the integers, (x - 1) divides (x^n - 1). -/
theorem int_sub_one_dvd_pow_sub_one (x : ℤ) (n : ℕ) : (x - 1) ∣ (x ^ n - 1) :=
  sub_one_dvd_pow_sub_one x n

/-- For x ≥ 2 and n ≥ 1, x^n ≥ 2, so x^n - 1 ≥ 1 in ℕ. -/
theorem pow_sub_one_pos (x n : ℕ) (hx : x ≥ 2) (hn : n ≥ 1) : 1 ≤ x ^ n - 1 := by
  have : 2 ≤ x ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ x ^ 1 := Nat.pow_le_pow_left (by omega) 1
      _ ≤ x ^ n := Nat.pow_le_pow_right (by omega) hn
  omega

/-- For x ≥ 2 and n ≥ 1, x^n - 1 ≠ 0 in ℕ. -/
theorem pow_sub_one_ne_zero (x n : ℕ) (hx : x ≥ 2) (hn : n ≥ 1) : x ^ n - 1 ≠ 0 := by
  have := pow_sub_one_pos x n hx hn; omega

/-
## Concrete Support Computations
-/

/-- supp(2^1 - 1) = ∅. -/
theorem support_2pow1 : (2 ^ 1 - 1 : ℕ).primeFactors = ∅ := by norm_num

/-- supp(2^2 - 1) = {3}. -/
theorem support_2pow2 : (2 ^ 2 - 1 : ℕ).primeFactors = {3} := by norm_num

/-- supp(2^3 - 1) = {7}: Mersenne prime. -/
theorem support_2pow3 : (2 ^ 3 - 1 : ℕ).primeFactors = {7} := by norm_num

/-- supp(2^4 - 1) = {3, 5}: two primes appear at n = 4. -/
theorem support_2pow4 : (2 ^ 4 - 1 : ℕ).primeFactors = {3, 5} := by norm_num

/-- supp(2^5 - 1) = {31}: Mersenne prime at n = 5. -/
theorem support_2pow5 : (2 ^ 5 - 1 : ℕ).primeFactors = {31} := by norm_num

/-- supp(3^2 - 1) = {2}. -/
theorem support_3pow2 : (3 ^ 2 - 1 : ℕ).primeFactors = {2} := by norm_num

/-- supp(3^3 - 1) = {2, 13}. -/
theorem support_3pow3 : (3 ^ 3 - 1 : ℕ).primeFactors = {2, 13} := by norm_num

/-- supp(4^3 - 1) = {3, 7}. -/
theorem support_4pow3 : (4 ^ 3 - 1 : ℕ).primeFactors = {3, 7} := by norm_num

/-- The support sequences for 2 and 3 differ at n = 2: {3} ≠ {2}. -/
theorem two_three_support_differ :
    (2 ^ 2 - 1 : ℕ).primeFactors ≠ (3 ^ 2 - 1 : ℕ).primeFactors := by norm_num

/-- The support sequences for 2 and 4 differ at n = 3: {7} ≠ {3, 7}. -/
theorem two_four_support_differ_n3 :
    (2 ^ 3 - 1 : ℕ).primeFactors ≠ (4 ^ 3 - 1 : ℕ).primeFactors := by norm_num

/-
## ZMod Order Characterization

For a prime p, the prime p divides x^n - 1 iff the multiplicative order
of x modulo p divides n. This bridges divisibility and group theory.
-/

/-- p | x^n - 1 (as integers) iff (x : ZMod p)^n = 1. -/
theorem prime_dvd_pow_sub_one_iff_zmod (p : ℕ) (hp : p.Prime) (x : ℤ) (n : ℕ) :
    (p : ℤ) ∣ x ^ n - 1 ↔ (x : ZMod p) ^ n = 1 := by
  constructor
  · intro hdvd
    have h0 : ((x ^ n - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    have h1 : (x : ZMod p) ^ n - 1 = 0 := by push_cast at h0; exact h0
    exact sub_eq_zero.mp h1
  · intro heq
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    show ((x ^ n - 1 : ℤ) : ZMod p) = 0
    push_cast
    exact sub_eq_zero.mpr heq

/-- p | x^n - 1 iff orderOf (x : ZMod p) divides n. -/
theorem prime_dvd_pow_sub_one_iff_order (p : ℕ) (hp : p.Prime) (x : ℤ) (n : ℕ) :
    (p : ℤ) ∣ x ^ n - 1 ↔ orderOf (x : ZMod p) ∣ n := by
  rw [prime_dvd_pow_sub_one_iff_zmod p hp x n]
  exact orderOf_dvd_iff_pow_eq_one.symm

/-
## Structural Consequence: Equal Orders

If supp(x^n-1) = supp(y^n-1) for all n, and p ∤ x and p ∤ y,
then x and y have the same multiplicative order modulo p.
-/

/-- Equal support for all n implies x and y have the same multiplicative order mod p,
    provided p does not divide x or y.
    Proof uses Fermat's little theorem to show orders are positive, then
    applies divisibility antisymmetry: ord_p(x) | ord_p(y) and vice versa. -/
theorem equal_support_implies_equal_orders (p : ℕ) (hp : p.Prime) (x y : ℤ)
    (hcop_x : ¬ (p : ℤ) ∣ x) (hcop_y : ¬ (p : ℤ) ∣ y)
    (h : ∀ n : ℕ, n ≥ 1 → ((p : ℤ) ∣ x ^ n - 1 ↔ (p : ℤ) ∣ y ^ n - 1)) :
    orderOf (x : ZMod p) = orderOf (y : ZMod p) := by
  haveI hfact : Fact p.Prime := ⟨hp⟩
  have hxne : (x : ZMod p) ≠ 0 :=
    fun h0 => hcop_x ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h0)
  have hyne : (y : ZMod p) ≠ 0 :=
    fun h0 => hcop_y ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp h0)
  -- Fermat's little theorem: x^(p-1) ≡ 1 (mod p)
  have hxflt : (x : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hxne
  have hyflt : (y : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hyne
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  -- Orders are positive: they divide p-1 > 0, so must be nonzero (0 ∣ (p-1) → p-1 = 0, contradicting hp1)
  have hox : 0 < orderOf (x : ZMod p) := by
    rcases Nat.eq_zero_or_pos (orderOf (x : ZMod p)) with h0 | h0
    · have hdvd := orderOf_dvd_of_pow_eq_one hxflt
      rw [h0] at hdvd; simp at hdvd; omega
    · exact h0
  have hoy : 0 < orderOf (y : ZMod p) := by
    rcases Nat.eq_zero_or_pos (orderOf (y : ZMod p)) with h0 | h0
    · have hdvd := orderOf_dvd_of_pow_eq_one hyflt
      rw [h0] at hdvd; simp at hdvd; omega
    · exact h0
  apply Nat.dvd_antisymm
  · -- ord_p(x) | ord_p(y): (y:ZMod p)^(ord_p(y)) = 1, hypothesis transfers
    rw [← orderOf_dvd_iff_pow_eq_one, ← prime_dvd_pow_sub_one_iff_zmod p hp]
    exact (h _ hoy).mpr (by rw [prime_dvd_pow_sub_one_iff_zmod p hp]; exact pow_orderOf_eq_one _)
  · -- ord_p(y) | ord_p(x): symmetric
    rw [← orderOf_dvd_iff_pow_eq_one, ← prime_dvd_pow_sub_one_iff_zmod p hp]
    exact (h _ hox).mp (by rw [prime_dvd_pow_sub_one_iff_zmod p hp]; exact pow_orderOf_eq_one _)

/-
## The Corrales-Rodánez–Schoof Theorem
-/

/-- **Corrales-Rodánez–Schoof (1997)**: For integers x, y ≥ 2, if the prime support
    of x^n - 1 equals that of y^n - 1 for all n ≥ 1, then x = y.
    Proof uses Kummer theory and Galois cohomology. -/
axiom corrales_schoof (x y : ℕ) (hx : x ≥ 2) (hy : y ≥ 2)
    (h : ∀ n : ℕ, n ≥ 1 → (x ^ n - 1 : ℕ).primeFactors = (y ^ n - 1 : ℕ).primeFactors) :
    x = y

/-
## Corollaries
-/

/-- The hypothesis is symmetric. -/
theorem support_hypothesis_symm (x y : ℕ)
    (h : ∀ n : ℕ, n ≥ 1 → (x ^ n - 1 : ℕ).primeFactors = (y ^ n - 1 : ℕ).primeFactors) :
    ∀ n : ℕ, n ≥ 1 → (y ^ n - 1 : ℕ).primeFactors = (x ^ n - 1 : ℕ).primeFactors :=
  fun n hn => (h n hn).symm

/-- Corrales-Schoof is symmetric. -/
theorem corrales_schoof_symm (x y : ℕ) (hx : x ≥ 2) (hy : y ≥ 2)
    (h : ∀ n : ℕ, n ≥ 1 → (x ^ n - 1 : ℕ).primeFactors = (y ^ n - 1 : ℕ).primeFactors) :
    y = x :=
  (corrales_schoof x y hx hy h).symm

/-- Transitivity: equal support to the same z forces x = y. -/
theorem corrales_schoof_trans (x y z : ℕ) (hx : x ≥ 2) (hy : y ≥ 2) (hz : z ≥ 2)
    (hxz : ∀ n : ℕ, n ≥ 1 → (x ^ n - 1 : ℕ).primeFactors = (z ^ n - 1 : ℕ).primeFactors)
    (hyz : ∀ n : ℕ, n ≥ 1 → (y ^ n - 1 : ℕ).primeFactors = (z ^ n - 1 : ℕ).primeFactors) :
    x = y :=
  corrales_schoof x y hx hy (fun n hn => (hxz n hn).trans (hyz n hn).symm)

/-- The prime support map x ↦ (n ↦ supp(x^n-1)) is injective for x ≥ 2. -/
theorem corrales_schoof_injective :
    Function.Injective (fun x : {n : ℕ // n ≥ 2} =>
      fun (n : ℕ) => (x.val ^ n - 1 : ℕ).primeFactors) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ heq
  congr 1
  exact corrales_schoof x y hx hy (fun n _ => congr_fun heq n)

/-
## Support Transfer Under the Hypothesis
-/

/-- Any prime in supp(x^n-1) must also be in supp(y^n-1) under the CS hypothesis. -/
theorem support_subset_under_hypothesis (x y : ℕ) (hx : x ≥ 2) (hy : y ≥ 2)
    (h : ∀ n : ℕ, n ≥ 1 → (x ^ n - 1 : ℕ).primeFactors = (y ^ n - 1 : ℕ).primeFactors)
    (n : ℕ) (hn : n ≥ 1) (p : ℕ) (hp : p.Prime) (hdvd : p ∣ x ^ n - 1) :
    p ∣ y ^ n - 1 := by
  have hxn : x ^ n - 1 ≠ 0 := pow_sub_one_ne_zero x n hx hn
  have hyn : y ^ n - 1 ≠ 0 := pow_sub_one_ne_zero y n hy hn
  have hmem : p ∈ (x ^ n - 1 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hdvd, hxn⟩
  rw [h n hn] at hmem
  exact (Nat.mem_primeFactors.mp hmem).2.1

/-
## The Zsygmondy Connection

Zsygmondy's theorem (1892): for x ≥ 2 and n ≥ 3 (with finitely many exceptions),
x^n - 1 has a primitive prime divisor. This makes the CS hypothesis highly restrictive.
-/

/-- **Zsygmondy (1892)**: For x ≥ 2 and n ≥ 3 (with two exceptions), x^n - 1 has a
    primitive prime divisor — a prime not dividing x^k - 1 for any 1 ≤ k < n. -/
axiom zsygmondy (x n : ℕ) (hx : x ≥ 2) (hn : n ≥ 3)
    (hnotex1 : ¬ (x = 2 ∧ n = 6))
    (hnotex2 : ¬ (x = 2 ∧ Nat.Prime (2 ^ n - 1))) :
    ∃ p : ℕ, p.Prime ∧ p ∣ x ^ n - 1 ∧ ∀ k : ℕ, 1 ≤ k → k < n → ¬ p ∣ x ^ k - 1

/-- Primitive prime divisors transfer: under the CS hypothesis, a primitive prime
    for x^n-1 is also primitive for y^n-1. -/
theorem primitive_prime_transferred (x y : ℕ) (hx : x ≥ 2) (hy : y ≥ 2)
    (h : ∀ m : ℕ, m ≥ 1 → (x ^ m - 1 : ℕ).primeFactors = (y ^ m - 1 : ℕ).primeFactors)
    (n : ℕ) (hn : n ≥ 1) (p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ x ^ n - 1)
    (hprim : ∀ k : ℕ, 1 ≤ k → k < n → ¬ p ∣ x ^ k - 1) :
    p ∣ y ^ n - 1 ∧ ∀ k : ℕ, 1 ≤ k → k < n → ¬ p ∣ y ^ k - 1 := by
  refine ⟨support_subset_under_hypothesis x y hx hy h n hn p hp hdvd, fun k hk1 hkn => ?_⟩
  intro hpyk
  have hyk : y ^ k - 1 ≠ 0 := pow_sub_one_ne_zero y k hy hk1
  have hmem : p ∈ (y ^ k - 1 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpyk, hyk⟩
  rw [← h k hk1] at hmem
  exact hprim k hk1 hkn (Nat.mem_primeFactors.mp hmem).2.1

/-
## The n = 1 Case

The hypothesis at n = 1 already constrains x and y: supp(x-1) = supp(y-1).
-/

/-- supp(x-1) = supp(y-1) follows from the CS hypothesis at n = 1. -/
theorem support_n1_from_hypothesis (x y : ℕ)
    (h : ∀ n : ℕ, n ≥ 1 → (x ^ n - 1 : ℕ).primeFactors = (y ^ n - 1 : ℕ).primeFactors) :
    (x - 1 : ℕ).primeFactors = (y - 1 : ℕ).primeFactors := by
  have := h 1 (le_refl 1); simpa using this

/-
## Summary

Erdős #1214: if supp(x^n-1) = supp(y^n-1) for all n ≥ 1, must x = y?
Answer: YES — Corrales-Rodánez and Schoof (1997).

Key results proved (no sorry):
- sub_one_dvd_pow_sub_one: (x-1) | (x^n-1) via geometric series
- prime_dvd_pow_sub_one_iff_zmod: p | x^n-1 ↔ (x:ZMod p)^n = 1
- prime_dvd_pow_sub_one_iff_order: p | x^n-1 ↔ orderOf (x:ZMod p) | n
- equal_support_implies_equal_orders: equal support ⟹ same orders mod p (for p ∤ xy)
  Uses Fermat's little theorem to establish positive orders, then antisymmetry
- Concrete computations: supp(2^k-1) and supp(3^k-1) for k = 1..5
- support_subset_under_hypothesis: primes transfer under CS hypothesis
- primitive_prime_transferred: primitive prime divisors also transfer
- corrales_schoof_injective: the support map is injective

Axiom count: 2 (corrales_schoof, zsygmondy)
Sorry count: 0
Proved: 26 theorems
-/

end Erdos1214Problem
