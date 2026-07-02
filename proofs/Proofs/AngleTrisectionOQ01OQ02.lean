/-
  Angle Trisection, Open Question 01 → OQ 02:
  The arithmetic (Wantzel) criterion behind the Gauss–Wantzel theorem.

  The Gauss–Wantzel theorem states that a regular n-gon is constructible with
  compass and straightedge iff n is the product of a power of 2 and distinct
  Fermat primes. The geometric ("constructible") half of that equivalence is not
  yet in Mathlib. Its **arithmetic engine**, however — the classification of
  those n for which the field degree [ℚ(ζₙ):ℚ] = φ(n) is a power of two — is a
  self-contained number-theoretic statement, and that is what we formalize here,
  with 0 axioms.

  Main theorem (`totient_isTwoPow_iff`): for n ≥ 1,

      φ(n) is a power of 2
        ↔  every prime p ∣ n is either 2, or a Fermat prime occurring to the
           first power.

  Since a regular n-gon is constructible exactly when φ(n) is a power of two,
  this is precisely the "n = 2ᵃ · (product of distinct Fermat primes)" clause of
  Gauss–Wantzel, phrased directly on the prime factorization.

  Ingredients:
    • `IsFermatPrime p := p.Prime ∧ ∃ m, p = 2^(2^m)+1`;
    • the local fact that for an odd prime p, `φ(p) = p - 1` is a power of two iff
      p is a Fermat prime (`totient_odd_prime_isTwoPow_iff`), which uses Mathlib's
      `Nat.pow_of_pow_add_prime` (a prime of the form 2ˢ+1 forces s to be a power
      of two);
    • Euler's product `φ(n) = ∏ p^{eₚ-1}(p-1)` and the fact that a positive
      natural is a power of two iff its only prime factor is 2.

  No axioms; fully machine-checked against Mathlib.

  Parent: angle-trisection-oq-01 (constructibility / Galois-theoretic obstructions).
  Reference: C. F. Gauss, Disquisitiones Arithmeticae (1801); P. Wantzel (1837).
-/

import Mathlib

open Nat Finset
open scoped Classical

set_option linter.unusedSectionVars false

namespace AngleTrisectionOQ01OQ02

/-- A **Fermat prime**: a prime of the form `2^(2^m) + 1 = fermatNumber m`. -/
def IsFermatPrime (p : ℕ) : Prop := p.Prime ∧ ∃ m : ℕ, p = Nat.fermatNumber m

/-- A positive natural number is a power of two iff its only prime factor is 2. -/
lemma isTwoPow_iff {m : ℕ} (hm : m ≠ 0) :
    (∃ k, m = 2 ^ k) ↔ ∀ q, q.Prime → q ∣ m → q = 2 := by
  constructor
  · rintro ⟨k, rfl⟩ q hq hqd
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqd)
  · intro h
    exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hm (fun {q} hq hqd => h q hq hqd)⟩

/-- A Fermat prime is odd (indeed `≥ 3`). -/
lemma IsFermatPrime.ne_two {p : ℕ} (hp : IsFermatPrime p) : p ≠ 2 := by
  obtain ⟨_, m, rfl⟩ := hp
  have := Nat.two_lt_fermatNumber m
  omega

/-- For a Fermat prime `p = 2^(2^m)+1`, the totient `φ(p) = p - 1 = 2^(2^m)` is a
    power of two. -/
lemma IsFermatPrime.totient_isTwoPow {p : ℕ} (hp : IsFermatPrime p) :
    ∃ k, Nat.totient p = 2 ^ k := by
  obtain ⟨hpp, m, rfl⟩ := hp
  refine ⟨2 ^ m, ?_⟩
  rw [Nat.totient_prime hpp, Nat.fermatNumber]
  simp

/-- **Local criterion.** For an odd prime `p`, `φ(p)` is a power of two iff `p` is
    a Fermat prime. -/
lemma totient_odd_prime_isTwoPow_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ k, Nat.totient p = 2 ^ k) ↔ IsFermatPrime p := by
  constructor
  · rintro ⟨k, hk⟩
    rw [Nat.totient_prime hp] at hk
    have hp3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact absurd h hp2
      · have := hp.two_le; omega
    -- p = 2^k + 1 with k ≥ 1
    have hpeq : p = 2 ^ k + 1 := by omega
    have hk0 : k ≠ 0 := by
      rintro rfl; simp at hk; omega
    have hPrime : (2 ^ k + 1).Prime := hpeq ▸ hp
    obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (a := 2) one_lt_two hk0 hPrime
    exact ⟨hp, m, by rw [hpeq, hm, Nat.fermatNumber]⟩
  · intro hf; exact hf.totient_isTwoPow

/-- Euler's product for the totient over the prime factors of `n`. -/
lemma totient_eq_prod_primeFactors {n : ℕ} (hn : n ≠ 0) :
    Nat.totient n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p - 1) := by
  rw [Nat.totient_eq_prod_factorization hn, Finsupp.prod, Nat.support_factorization]

/-- **The arithmetic Gauss–Wantzel criterion.** For `n ≥ 1`, the totient `φ(n)`
    is a power of two iff every prime factor of `n` is either `2` or a Fermat
    prime dividing `n` exactly once. Equivalently, `n = 2ᵃ · (product of distinct
    Fermat primes)`. -/
theorem totient_isTwoPow_iff {n : ℕ} (hn : n ≠ 0) :
    (∃ k, Nat.totient n = 2 ^ k) ↔
      ∀ p ∈ n.primeFactors, p = 2 ∨ (IsFermatPrime p ∧ n.factorization p = 1) := by
  have hφ : Nat.totient n ≠ 0 := (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
  have hprod := totient_eq_prod_primeFactors hn
  rw [isTwoPow_iff hφ, hprod]
  constructor
  · -- φ n is a power of two ⇒ the factorization condition
    intro hq p hp
    by_cases hp2 : p = 2
    · exact Or.inl hp2
    refine Or.inr ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    -- the p-factor divides the product
    have hdvd : p ^ (n.factorization p - 1) * (p - 1)
        ∣ ∏ q ∈ n.primeFactors, q ^ (n.factorization q - 1) * (q - 1) :=
      Finset.dvd_prod_of_mem _ hp
    -- multiplicity is 1: otherwise p ∣ product ⇒ p = 2
    have hfp1 : n.factorization p = 1 := by
      have hpos : 0 < n.factorization p :=
        hpp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
      by_contra hne
      have : p ∣ p ^ (n.factorization p - 1) * (p - 1) :=
        Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
      exact hp2 (hq p hpp (this.trans hdvd))
    refine ⟨?_, hfp1⟩
    -- p - 1 is a power of two, hence p is a Fermat prime
    apply (totient_odd_prime_isTwoPow_iff hpp hp2).mp
    rw [Nat.totient_prime hpp, isTwoPow_iff (show p - 1 ≠ 0 by have := hpp.two_le; omega)]
    intro q hqp hqd
    refine hq q hqp (dvd_trans ?_ hdvd)
    calc q ∣ p - 1 := hqd
      _ ∣ p ^ (n.factorization p - 1) * (p - 1) := dvd_mul_left _ _
  · -- the factorization condition ⇒ φ n is a power of two
    intro hcond q hqp hqd
    -- q divides the product, so it divides some p-factor
    rw [Prime.dvd_finset_prod_iff hqp.prime] at hqd
    obtain ⟨p, hp, hpdvd⟩ := hqd
    rcases hcond p hp with hp2 | ⟨hf, hfp1⟩
    · -- p = 2: factor is 2^(e-1)
      subst hp2
      have : q ∣ 2 ^ (n.factorization 2 - 1) := by simpa using hpdvd
      exact (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow this)
    · -- p a Fermat prime with multiplicity 1: factor is p - 1 = 2^(2^m)
      obtain ⟨hpp, m, rfl⟩ := hf
      rw [hfp1] at hpdvd
      have hfac : Nat.fermatNumber m ^ (1 - 1) * (Nat.fermatNumber m - 1)
          = 2 ^ (2 ^ m) := by rw [Nat.fermatNumber]; simp
      rw [hfac] at hpdvd
      exact (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow hpdvd)

/-- The main #1003-style consequence phrased for a **prime** `n = p`: a regular
    `p`-gon has `φ(p) = p-1` a power of two (the constructibility criterion) iff
    `p` is a Fermat prime. -/
theorem prime_totient_isTwoPow_iff {p : ℕ} (hp : p.Prime) :
    (∃ k, Nat.totient p = 2 ^ k) ↔ (p = 2 ∨ IsFermatPrime p) := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [Nat.totient_prime Nat.prime_two]
    constructor
    · intro _; exact Or.inl rfl
    · intro _; exact ⟨0, rfl⟩
  · rw [totient_odd_prime_isTwoPow_iff hp hp2]
    constructor
    · exact fun h => Or.inr h
    · rintro (h | h)
      · exact absurd h hp2
      · exact h

end AngleTrisectionOQ01OQ02
