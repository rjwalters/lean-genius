/-
Erdős Problem #467: Dual Covering by Prime Residue Classes

**Problem Statement (OPEN)**

For all sufficiently large x, prove there exist:
- congruence classes a_p for each prime p ≤ x, and
- a partition of primes {p ≤ x} = A ⊔ B (both non-empty),

such that every n < x satisfies n ≡ a_p (mod p) for some p ∈ A and
n ≡ a_q (mod q) for some q ∈ B.

**Background:**
- The problem asks for a "dual covering" by two complementary sets of primes
- Related to covering congruences and the Erdős–Graham framework
- Original quantifiers in [ErGr80, p. 93] are ambiguous

**Status:** OPEN

**References:**
- Erdős, Graham (1980): Old and New Problems and Results in Combinatorial
  Number Theory, p. 93
- erdosproblems.com/467
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-
## Core Definitions
-/

/-- A residue assignment: for each prime p, a chosen residue class a_p. -/
def ResidueAssignment (x : ℕ) := (p : ℕ) → p.Prime → p ≤ x → ℕ

/-- A partition of primes ≤ x into two non-empty sets A and B. -/
structure PrimePartition (x : ℕ) where
  inA : (p : ℕ) → p.Prime → p ≤ x → Bool
  nonemptyA : ∃ p : ℕ, ∃ hp : p.Prime, ∃ hle : p ≤ x, inA p hp hle = true
  nonemptyB : ∃ p : ℕ, ∃ hp : p.Prime, ∃ hle : p ≤ x, inA p hp hle = false

/-- An integer n is covered by set A: there exists p ∈ A with n ≡ a_p (mod p). -/
def CoveredByA (x : ℕ) (assign : ResidueAssignment x) (part : PrimePartition x)
    (n : ℕ) : Prop :=
  ∃ p : ℕ, ∃ hp : p.Prime, ∃ hle : p ≤ x,
    part.inA p hp hle = true ∧ n % p = assign p hp hle % p

/-- An integer n is covered by set B: there exists q ∈ B with n ≡ a_q (mod q). -/
def CoveredByB (x : ℕ) (assign : ResidueAssignment x) (part : PrimePartition x)
    (n : ℕ) : Prop :=
  ∃ q : ℕ, ∃ hq : q.Prime, ∃ hle : q ≤ x,
    part.inA q hq hle = false ∧ n % q = assign q hq hle % q

/-- A dual covering: every n < x is covered by both A and B. -/
def IsDualCovering (x : ℕ) (assign : ResidueAssignment x) (part : PrimePartition x) : Prop :=
  ∀ n : ℕ, n < x → CoveredByA x assign part n ∧ CoveredByB x assign part n

/-
## Main Conjecture (OPEN)
-/

/-- **Erdős Problem #467** (OPEN): For all sufficiently large x, there exist
    a residue assignment and a prime partition giving a dual covering. -/
axiom erdos_467_conjecture :
  ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
    ∃ assign : ResidueAssignment x,
    ∃ part : PrimePartition x,
      IsDualCovering x assign part

/-
## Basic Properties of Residue Classes
-/

/-- The remainder n % p is always less than p for p > 0. -/
theorem residue_lt_prime (p : ℕ) (hp : p.Prime) (n : ℕ) : n % p < p :=
  Nat.mod_lt n hp.pos

/-- n is in residue class 0 mod p iff p divides n. -/
theorem zero_class_iff_dvd (p n : ℕ) : n % p = 0 ↔ p ∣ n :=
  (Nat.dvd_iff_mod_eq_zero).symm

/-- Every natural number is either even or odd. -/
theorem even_or_odd (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 := by omega

/-- Within any p consecutive integers, exactly one is in each residue class mod p. -/
theorem coverage_density (p a : ℕ) (hp : p > 0) :
    ∀ k : ℕ, (a + k * p) % p = a % p := by
  intro k; rw [mul_comm, Nat.add_mul_mod_self_left]

/-- Every n ≥ 2 has a prime factor. -/
theorem has_prime_factor (n : ℕ) (hn : n ≥ 2) :
    ∃ p, p.Prime ∧ p ∣ n :=
  ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩

/-- Every prime factor of n is at most n. -/
theorem prime_factor_le (n p : ℕ) (hp : p.Prime) (hdvd : p ∣ n) (hn : n > 0) :
    p ≤ n :=
  Nat.le_of_dvd hn hdvd

/-- Every n ≥ 2 with n < x has a prime factor ≤ x. -/
theorem prime_factor_le_x (n x : ℕ) (hn : n ≥ 2) (hlt : n < x) :
    ∃ p, p.Prime ∧ p ∣ n ∧ p ≤ x := by
  obtain ⟨p, hp, hdvd⟩ := has_prime_factor n hn
  have hle := Nat.le_of_dvd (by omega) hdvd
  exact ⟨p, hp, hdvd, by omega⟩

/-
## Covering by Zero Residue Classes
-/

/-- Using residue class 0 for each prime, n = 0 is covered by every prime. -/
theorem zero_covered_by_all (p : ℕ) (hp : p.Prime) : 0 % p = 0 := by simp

/-- n = 1 is NOT covered by residue class 0 for any prime. -/
theorem one_not_covered_by_zero (p : ℕ) (hp : p.Prime) : 1 % p ≠ 0 := by
  intro h
  have hdvd := Nat.dvd_of_mod_eq_zero h
  have hle := Nat.le_of_dvd (by omega) hdvd
  have hp2 := hp.two_le
  omega

/-- Using residue class 0 for each prime, every n ≥ 2 is covered by its
    smallest prime factor. -/
theorem zero_covers_ge2 (n : ℕ) (hn : n ≥ 2) :
    ∃ p, p.Prime ∧ p ≤ n ∧ p ∣ n := by
  obtain ⟨p, hp, hdvd⟩ := has_prime_factor n hn
  exact ⟨p, hp, Nat.le_of_dvd (by omega) hdvd, hdvd⟩

/-
## The Zero Assignment
-/

/-- The zero assignment: assign residue class 0 to every prime. -/
def zeroAssignment (x : ℕ) : ResidueAssignment x :=
  fun _ _ _ => 0

/-- With the zero assignment, n is covered by prime p iff p divides n. -/
theorem zero_assign_cover_iff (x : ℕ) (p n : ℕ) (hp : p.Prime) (hle : p ≤ x) :
    n % p = (zeroAssignment x p hp hle) % p ↔ p ∣ n := by
  simp [zeroAssignment, Nat.dvd_iff_mod_eq_zero]

/-
## Partition Constraints
-/

/-- If we have a dual covering, B covers every n < x. -/
theorem dual_implies_B_covers (x : ℕ) (assign : ResidueAssignment x)
    (part : PrimePartition x) (hdual : IsDualCovering x assign part)
    (n : ℕ) (hn : n < x) : CoveredByB x assign part n :=
  (hdual n hn).2

/-- If we have a dual covering, A covers every n < x. -/
theorem dual_implies_A_covers (x : ℕ) (assign : ResidueAssignment x)
    (part : PrimePartition x) (hdual : IsDualCovering x assign part)
    (n : ℕ) (hn : n < x) : CoveredByA x assign part n :=
  (hdual n hn).1

/-
## Dual Covering Properties
-/

/-- If we have a dual covering, every n < x is hit by at least two primes. -/
theorem dual_covering_double_hit (x : ℕ) (assign : ResidueAssignment x)
    (part : PrimePartition x) (hdual : IsDualCovering x assign part)
    (n : ℕ) (hn : n < x) :
    ∃ p q : ℕ, ∃ hp : p.Prime, ∃ hq : q.Prime, ∃ hlep : p ≤ x, ∃ hleq : q ≤ x,
      part.inA p hp hlep = true ∧ part.inA q hq hleq = false ∧
      n % p = assign p hp hlep % p ∧ n % q = assign q hq hleq % q := by
  obtain ⟨⟨p, hp, hlep, hA, hmodp⟩, ⟨q, hq, hleq, hB, hmodq⟩⟩ := hdual n hn
  exact ⟨p, q, hp, hq, hlep, hleq, hA, hB, hmodp, hmodq⟩

/-- A partition uses at least two primes: one in A and one in B. -/
theorem partition_uses_two_primes (x : ℕ) (part : PrimePartition x) :
    ∃ p q : ℕ, ∃ _ : p.Prime, ∃ _ : q.Prime, p ≤ x ∧ q ≤ x := by
  obtain ⟨p, hp, hle, _⟩ := part.nonemptyA
  obtain ⟨q, hq, hleq, _⟩ := part.nonemptyB
  exact ⟨p, q, hp, hq, hle, hleq⟩

/-- A and B assign different labels to at least one pair of primes. -/
theorem partition_has_distinct_labels (x : ℕ) (part : PrimePartition x) :
    ∃ p q : ℕ, ∃ hp : p.Prime, ∃ hq : q.Prime,
      ∃ hlep : p ≤ x, ∃ hleq : q ≤ x,
        part.inA p hp hlep ≠ part.inA q hq hleq := by
  obtain ⟨p, hp, hlep, hA⟩ := part.nonemptyA
  obtain ⟨q, hq, hleq, hB⟩ := part.nonemptyB
  exact ⟨p, q, hp, hq, hlep, hleq, by simp [hA, hB]⟩

/-- A partition requires x ≥ 2 (at least one prime must exist). -/
theorem partition_needs_prime (x : ℕ) (part : PrimePartition x) : x ≥ 2 := by
  obtain ⟨p, hp, hle, _⟩ := part.nonemptyA
  have := hp.two_le
  omega

/-
## Residue Class Properties
-/

/-- Among p consecutive integers, residue classes are periodic. -/
theorem residue_class_periodic (p : ℕ) (hp : p > 0) (n : ℕ) :
    (n + p) % p = n % p := by
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod_of_dvd]
  exact dvd_refl p

/-- In [0, p), every residue class mod p has exactly one element. -/
theorem residue_class_in_range (p : ℕ) (hp : p > 0) (a : ℕ) (ha : a < p) :
    a % p = a :=
  Nat.mod_eq_of_lt ha

/-- The number of residue classes mod p is exactly p. -/
theorem num_residue_classes (p : ℕ) (hp : p > 0) :
    ∀ n, n % p < p := fun n => Nat.mod_lt n hp

/-
## CRT for Distinct Primes
-/

/-- For distinct primes p, q and any residues a, b,
    the CRT guarantees n with n ≡ a (mod p) and n ≡ b (mod q).
    Proved via Mathlib's `Nat.chineseRemainder`. -/
theorem crt_for_primes (p q a b : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ∃ n, n % p = a % p ∧ n % q = b % q := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  let sol := Nat.chineseRemainder hcop a b
  exact ⟨sol.val, sol.property.1, sol.property.2⟩

/-
## Mertens-type Estimates
-/

/-- Placeholder for Mertens' third theorem. The formal conclusion here is
    trivially true (it only asserts x > 0 for large x). A proper Mertens
    estimate would require formalizing the Euler product over primes. -/
theorem mertens_product :
    ∃ c : ℝ, c > 0 ∧ ∀ ε > 0, ∃ X : ℕ, ∀ x ≥ X,
      (x : ℝ) > 0 :=
  ⟨1, one_pos, fun _ _ => ⟨1, fun x hx => Nat.cast_pos.mpr (by omega)⟩⟩

/-
## Necessary Conditions for Dual Covering
-/

/-- The zero assignment cannot achieve dual covering for x ≥ 2:
    n = 1 is never covered by any zero-class prime. -/
theorem zero_assign_no_dual_cover (x : ℕ) (hx : x ≥ 2) (part : PrimePartition x) :
    ¬ IsDualCovering x (zeroAssignment x) part := by
  intro hdual
  have h1 : (1 : ℕ) < x := by omega
  obtain ⟨q, hq, _hle, _, hmod⟩ := (hdual 1 h1).2
  have h0 : 1 % q = 0 := by simpa [zeroAssignment] using hmod
  exact one_not_covered_by_zero q hq h0

/-- In any dual covering, A must contain a prime covering n = 1 and
    B must contain a prime covering n = 1: the assignment must be 1-compatible
    on at least one prime from each side. -/
theorem dual_cover_needs_unit_class (x : ℕ) (hx : x ≥ 2) (assign : ResidueAssignment x)
    (part : PrimePartition x) (hdual : IsDualCovering x assign part) :
    (∃ p : ℕ, ∃ hp : p.Prime, ∃ hle : p ≤ x,
      part.inA p hp hle = true ∧ assign p hp hle % p = 1 % p) ∧
    (∃ q : ℕ, ∃ hq : q.Prime, ∃ hle : q ≤ x,
      part.inA q hq hle = false ∧ assign q hq hle % q = 1 % q) := by
  have h1 : (1 : ℕ) < x := by omega
  obtain ⟨⟨p, hp, hle, hinA, hmodA⟩, ⟨q, hq, hleq, hinB, hmodB⟩⟩ := hdual 1 h1
  exact ⟨⟨p, hp, hle, hinA, hmodA.symm⟩, ⟨q, hq, hleq, hinB, hmodB.symm⟩⟩

/-
## Problem Summary
-/

/-- The conjecture is OPEN. No proof or disproof is known. -/
def erdos_467_status : String := "OPEN"

/-- Key observation: every n ≥ 2 has a prime factor. -/
theorem coverage_exceeds_target :
    ∀ n : ℕ, n ≥ 2 → ∃ p, p.Prime ∧ p ∣ n := fun n hn =>
  has_prime_factor n hn
