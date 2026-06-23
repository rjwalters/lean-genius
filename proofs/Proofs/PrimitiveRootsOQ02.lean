import Mathlib

/-!
# Primitive Roots: Testing Criterion and Finding Generators (OQ-02)

## Open Question (primitive-roots-oq-02)

**How can we efficiently determine whether a given element g is a primitive root modulo p?**

The naive check — compute g, g², ..., g^(p-2) and verify none equals 1 — requires O(p)
multiplications per candidate. The **prime factor testing criterion** reduces this to
O(k · log p) multiplications, where k is the number of distinct prime factors of p-1:

> g is a primitive root mod p ⟺ g^{(p-1)/q} ≢ 1 (mod p) for every prime q ∣ (p-1).

## Why This Works

The key insight: if g is NOT a primitive root, then orderOf g < p-1. Since orderOf g ∣ p-1,
there exists a prime q ∣ p-1 with orderOf g ∣ (p-1)/q. This means g^{(p-1)/q} = 1.

Conversely, if g^{(p-1)/q} ≠ 1 for all primes q ∣ p-1, then orderOf g cannot be any
proper divisor of p-1 (since every proper divisor of p-1 divides (p-1)/q for some prime q).
Combined with g^{p-1} = 1 (Fermat's little theorem), orderOf g = p-1.

## Algorithm Consequence

For a prime p with p-1 = q₁^{a₁} · ... · qₖ^{aₖ} (k distinct prime factors):
1. Compute g^{(p-1)/qᵢ} mod p for each i = 1, ..., k.
2. If any equals 1, g is NOT a primitive root.
3. If none equals 1, g IS a primitive root.

**Expected search time**: By the Mertens-type bound φ(p-1)/(p-1) ≥ C/log log p,
the expected number of candidates to test is O(log log p) — extremely efficient.

## Connection to Parent Proof

The parent proof (primitive-roots) establishes:
- (ZMod p)ˣ is cyclic
- There are exactly φ(p-1) primitive roots

This file answers the algorithmic question: how to FIND one of those φ(p-1) roots.

Tags: number-theory, primitive-roots, cyclic-groups, computational-number-theory, algorithm
-/

namespace PrimitiveRootsOQ02

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-! ## Setup: Generators and Fermat's Little Theorem -/

/-- A generator of (ℤ/pℤ)* is an element of multiplicative order p-1. -/
def IsGenerator (g : (ZMod p)ˣ) : Prop := orderOf g = p - 1

/-- Fermat's Little Theorem: every unit in ℤ/pℤ satisfies g^(p-1) = 1. -/
lemma pow_pred_prime_eq_one (g : (ZMod p)ˣ) : g ^ (p - 1) = 1 := by
  have hdvd : orderOf g ∣ p - 1 := by
    have h1 : orderOf g ∣ Fintype.card (ZMod p)ˣ := orderOf_dvd_card
    rwa [ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at h1
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]

/-! ## The Core Lemma: Prime Factor Testing for orderOf -/

/-- **Prime Factor Test for orderOf**

If g^n = 1 and for every prime q dividing n, g^(n/q) ≠ 1, then orderOf g = n.

This is the key lemma: testing n/q for prime factors q of n suffices to confirm
that n is the minimal order. The test rules out all proper divisors simultaneously,
since every proper divisor d ∣ n satisfies d ∣ n/q for some prime q ∣ n. -/
lemma orderOf_eq_of_prime_factor_test {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (hn : 0 < n) {g : G} (hpow : g ^ n = 1)
    (htest : ∀ q : ℕ, q.Prime → q ∣ n → g ^ (n / q) ≠ 1) :
    orderOf g = n := by
  apply Nat.dvd_antisymm
  · -- orderOf g ∣ n (since g^n = 1)
    exact orderOf_dvd_of_pow_eq_one hpow
  · -- n ∣ orderOf g (the hard direction)
    by_contra h_ndvd
    push_neg at h_ndvd
    have hdvd : orderOf g ∣ n := orderOf_dvd_of_pow_eq_one hpow
    -- Since orderOf g ∣ n but n ∤ orderOf g, orderOf g ≠ n, so orderOf g < n
    have hlt : orderOf g < n :=
      lt_of_le_of_ne (Nat.le_of_dvd hn hdvd) (fun h => h_ndvd (h ▸ dvd_refl n))
    -- n / orderOf g ≠ 1 (if it were 1, then n = orderOf g, contradicting hlt)
    have hquot_ne_one : n / orderOf g ≠ 1 := by
      intro h
      apply h_ndvd
      have := Nat.mul_div_cancel' hdvd
      rw [h, mul_one] at this
      exact this ▸ dvd_refl n
    -- Take q = smallest prime factor of n / orderOf g
    let q := Nat.minFac (n / orderOf g)
    have hq_prime : q.Prime := Nat.minFac_prime hquot_ne_one
    have hq_dvd_quot : q ∣ n / orderOf g := Nat.minFac_dvd _
    -- q divides n (since q ∣ n/orderOf g and orderOf g ∣ n, so q ∣ n)
    have hqn : q ∣ n := hq_dvd_quot.trans (Nat.div_dvd_of_dvd hdvd)
    -- orderOf g * q ∣ n (since orderOf g ∣ n and q ∣ n/orderOf g)
    have hmul_dvd : orderOf g * q ∣ n := by
      have := Nat.mul_dvd_mul_left (orderOf g) hq_dvd_quot
      rwa [Nat.mul_div_cancel' hdvd] at this
    -- orderOf g ∣ n/q (from orderOf g * q ∣ n)
    have hdvd_nq : orderOf g ∣ n / q := by
      obtain ⟨c, hc⟩ := hmul_dvd
      exact ⟨c, Nat.eq_of_mul_eq_mul_left hq_prime.pos (
        calc q * (n / q) = n               := Nat.mul_div_cancel' hqn
             _           = orderOf g * q * c := hc
             _           = q * (orderOf g * c) := by ring)⟩
    -- Therefore g^(n/q) = 1 — contradicting htest q hq_prime hqn
    obtain ⟨k, hk⟩ := hdvd_nq
    exact htest q hq_prime hqn (by rw [hk, pow_mul, pow_orderOf_eq_one, one_pow])

/-! ## Main Theorem: The Testing Criterion -/

/-- **Prime Factor Testing Criterion for Primitive Roots**

g is a primitive root modulo p (orderOf g = p-1) if and only if
for every prime q dividing p-1, g^{(p-1)/q} ≠ 1.

**Algorithmic significance**: This reduces the test from O(p) power computations
(checking all orders) to O(k · log p) where k = #{prime factors of p-1}. -/
theorem isGenerator_iff_prime_factor_test (g : (ZMod p)ˣ) :
    IsGenerator g ↔
    ∀ q : ℕ, q.Prime → q ∣ (p - 1) → g ^ ((p - 1) / q) ≠ 1 := by
  constructor
  · -- → If g is a generator, then g^{(p-1)/q} ≠ 1 for all prime q ∣ p-1
    intro hgen q hq hqdvd hcontra
    -- g^{(p-1)/q} = 1 ⟹ orderOf g ∣ (p-1)/q < p-1
    have hdvd_small := orderOf_dvd_of_pow_eq_one hcontra
    rw [hgen] at hdvd_small
    have hlt : (p - 1) / q < p - 1 :=
      Nat.div_lt_self (Nat.Prime.pred_pos hp.out) hq.one_lt
    have hpos : 0 < (p - 1) / q :=
      Nat.div_pos (Nat.le_of_dvd (Nat.Prime.pred_pos hp.out) hqdvd) hq.pos
    exact absurd (Nat.le_of_dvd hpos hdvd_small) (by omega)
  · -- ← If g passes the test for all primes, then orderOf g = p-1
    intro htest
    exact orderOf_eq_of_prime_factor_test
      (Nat.Prime.pred_pos hp.out)
      (pow_pred_prime_eq_one g)
      htest

/-- Equivalent form using `Nat.primeFactors`: the test set is exactly the
prime factors of p-1. -/
theorem isGenerator_iff_primeFactors_test (g : (ZMod p)ˣ) :
    IsGenerator g ↔
    ∀ q ∈ Nat.primeFactors (p - 1), g ^ ((p - 1) / q) ≠ 1 := by
  rw [isGenerator_iff_prime_factor_test]
  constructor
  · intro h q hq hne
    have hmem := Nat.mem_primeFactors.mp hq
    exact h q hmem.1 hmem.2.1 hne
  · intro h q hq hqdvd hne
    exact h q (Nat.mem_primeFactors.mpr ⟨hq, hqdvd, (Nat.Prime.pred_pos hp.out).ne'⟩) hne

/-! ## Existence: There Always Exists a Generator -/

/-- (ZMod p)ˣ is cyclic — inherited from the integral domain structure. -/
instance : IsCyclic (ZMod p)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom (ZMod p)) Units.ext

/-- **Existence of Generators**: There exists at least one primitive root mod p.

Combined with the testing criterion, this guarantees the search algorithm terminates. -/
theorem exists_generator : ∃ g : (ZMod p)ˣ, IsGenerator g := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  exact ⟨g, by
    unfold IsGenerator
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]⟩

/-! ## Decidability: The Algorithm is Computable -/

/-- `IsGenerator` is decidable — the algorithm can be implemented and terminates. -/
instance (g : (ZMod p)ˣ) : Decidable (IsGenerator g) :=
  inferInstance  -- follows from DecidableEq ℕ and Fintype (ZMod p)ˣ

/-! ## Concrete Verification: Small Primes -/

/-- For p = 3 (p-1 = 2 = 2¹): only prime factor is 2. We need g^1 ≠ 1. -/
example : Nat.totient (3 - 1) = 1 := by native_decide

/-- For p = 5 (p-1 = 4 = 2²): only prime factor of 4 is 2. Need g^2 ≠ 1. -/
example : Nat.primeFactors 4 = {2} := by native_decide

/-- For p = 7 (p-1 = 6 = 2 × 3): prime factors are {2, 3}. Need g^3 ≠ 1 and g^2 ≠ 1. -/
example : Nat.primeFactors 6 = {2, 3} := by native_decide

/-- For p = 11 (p-1 = 10 = 2 × 5): prime factors are {2, 5}. Only 2 tests needed. -/
example : Nat.primeFactors 10 = {2, 5} := by native_decide

/-- For p = 13 (p-1 = 12 = 2² × 3): prime factors are {2, 3}. Only 2 tests needed. -/
example : Nat.primeFactors 12 = {2, 3} := by native_decide

/-- For p = 23 (p-1 = 22 = 2 × 11): only 2 tests needed regardless of p's size. -/
example : Nat.primeFactors 22 = {2, 11} := by native_decide

/-- **Key efficiency observation**: p = 1000003 (prime) has p-1 = 2 × 3 × 166667.
    If 166667 is prime, only 3 tests are needed for any candidate, regardless of p. -/
example : Nat.primeFactors 1000002 = {2, 3, 166667} := by native_decide

/-! ## The Algorithm (Informal Description)

Given a prime p:
1. Factor p-1 = q₁^{a₁} · ... · qₖ^{aₖ} (find distinct prime factors q₁, ..., qₖ)
2. For each candidate g = 2, 3, ..., p-1 (or random sample):
   - For each qᵢ, compute gᵢ = g^{(p-1)/qᵢ} mod p using fast exponentiation
   - If any gᵢ = 1, skip this candidate (it's not a generator)
   - If all gᵢ ≠ 1, output g (it IS a generator by isGenerator_iff_prime_factor_test)
3. By exists_generator, this always terminates.

**Correctness**: Follows from `isGenerator_iff_prime_factor_test`.
**Termination**: Follows from `exists_generator` (φ(p-1) ≥ 1 generators exist).
**Expected candidates**: By Mertens-type bounds, O(log log p) on average. -/

/-! ## Summary -/

#check @orderOf_eq_of_prime_factor_test
#check @isGenerator_iff_prime_factor_test
#check @isGenerator_iff_primeFactors_test
#check @exists_generator

end PrimitiveRootsOQ02
