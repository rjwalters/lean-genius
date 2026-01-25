/-
Erdős Problem #203: Covering Systems and Prime Avoidance

**Problem Statement (OPEN)**

Is there an integer m >= 1 with (m, 6) = 1 such that none of 2^k * 3^l * m + 1
are prime, for any k, l >= 0?

**Background:**
- Relates to Sierpinski numbers: odd m where no 2^k * m + 1 is prime
- Generalizes to expressions involving multiple prime powers
- Connected to covering systems of congruences

**Status:** OPEN

**Reference:** Erdős-Graham 1980, p. 27

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Nat

namespace Erdos203

/-!
# Part 1: Basic Definitions

Define the candidate numbers 2^k * 3^l * m + 1.
-/

-- The family of numbers: 2^k * 3^l * m + 1
def candidateNumber (m k l : ℕ) : ℕ := 2^k * 3^l * m + 1

-- A number m avoids primes if no candidate is prime
def AvoidsPrimes (m : ℕ) : Prop :=
  m.Coprime 6 ∧ ∀ k l, ¬ (candidateNumber m k l).Prime

-- The set of numbers avoiding primes
def AvoidingSet : Set ℕ := {m | AvoidsPrimes m}

/-!
# Part 2: The Main Conjecture

Erdős asked whether AvoidingSet is nonempty.
-/

-- The conjecture: there exists such an m
def ErdosConjecture203 : Prop :=
  ∃ m, AvoidsPrimes m

-- Equivalent formulation
theorem conjecture_equiv :
    ErdosConjecture203 ↔
    ∃ m, m.Coprime 6 ∧ ∀ k l, ¬ (2^k * 3^l * m + 1).Prime := by
  constructor
  · intro ⟨m, hm⟩
    exact ⟨m, hm.1, fun k l => hm.2 k l⟩
  · intro ⟨m, hcop, hprime⟩
    exact ⟨m, hcop, hprime⟩

/-!
# Part 3: Sierpinski Numbers

The classical Sierpinski problem: find odd m such that 2^k * m + 1 is never prime.
-/

-- Sierpinski numbers: odd m where no 2^k * m + 1 is prime
def IsSierpinskiNumber (m : ℕ) : Prop :=
  Odd m ∧ ∀ k, ¬ (2^k * m + 1).Prime

-- The set of Sierpinski numbers
def SierpinskiSet : Set ℕ := {m | IsSierpinskiNumber m}

-- The smallest known Sierpinski number (Selfridge 1962)
def selfridge_sierpinski : ℕ := 78557

-- Selfridge's result: 78557 is Sierpinski
axiom selfridge_sierpinski_is_sierpinski : IsSierpinskiNumber selfridge_sierpinski

-- Sierpinski numbers exist
axiom sierpinski_exists : SierpinskiSet.Nonempty

-- Connection: if m is Sierpinski and coprime to 3, it might work for 203
-- But we also need 3^l factor, which complicates things
theorem sierpinski_necessary_not_sufficient (m : ℕ) (h : IsSierpinskiNumber m) :
    ∀ k, ¬ (2^k * m + 1).Prime := h.2

/-!
# Part 4: Covering Systems

Covering systems are used to prove Sierpinski-type results.
-/

-- A covering system: set of congruences covering all integers
def IsCoveringSystem (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ n : ℤ, ∃ p ∈ S, (n : ℤ) ≡ (p.1 : ℤ) [ZMOD (p.2 : ℤ)]

-- A prime covering system: each modulus has an associated prime
def PrimeCovering (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ → ℕ) : Prop :=
  IsCoveringSystem S ∧
  (∀ p ∈ S, (P p).Prime) ∧
  (∀ p ∈ S, P p ∣ (2^(p.2) - 1))

-- If we have a prime covering, we can construct Sierpinski numbers
axiom covering_implies_sierpinski :
  ∀ S P, PrimeCovering S P → ∃ m, IsSierpinskiNumber m

/-!
# Part 5: The Extended Problem

For Problem 203, we need coverings that work with both 2 and 3.
-/

-- Extended candidate: 2^k * 3^l * m + 1
def IsExtendedAvoiding (m : ℕ) : Prop :=
  m.Coprime 6 ∧ ∀ k l, ¬ (2^k * 3^l * m + 1).Prime

-- The challenge: covering systems for products of prime powers
-- This is more complex than the single-base case

-- For the extended problem, we'd need primes dividing 2^a * 3^b - 1
-- for appropriate a, b combinations
def ExtendedDivisibility (p : ℕ) (a b : ℕ) : Prop :=
  p.Prime ∧ p ∣ (2^a * 3^b - 1)

-- The order of 2 modulo p
noncomputable def ord2 (p : ℕ) (hp : p.Prime) (hp2 : ¬ p ∣ 2) : ℕ :=
  Nat.find (Nat.exists_pow_eq_one_of_coprime (Nat.Coprime.pow_right 1
    (Nat.coprime_comm.mp (Nat.Prime.coprime_iff_not_dvd hp).mpr hp2)) hp)

-- The order of 3 modulo p
noncomputable def ord3 (p : ℕ) (hp : p.Prime) (hp3 : ¬ p ∣ 3) : ℕ :=
  Nat.find (Nat.exists_pow_eq_one_of_coprime (Nat.Coprime.pow_right 1
    (Nat.coprime_comm.mp (Nat.Prime.coprime_iff_not_dvd hp).mpr hp3)) hp)

/-!
# Part 6: Small Cases and Constraints

The coprimality condition (m, 6) = 1 means m is not divisible by 2 or 3.
-/

-- m must be coprime to 6
theorem coprime_6_equiv (m : ℕ) :
    m.Coprime 6 ↔ m.Coprime 2 ∧ m.Coprime 3 := by
  constructor
  · intro h
    constructor
    · exact Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) h
    · exact Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) h
  · intro ⟨h2, h3⟩
    have : 6 = 2 * 3 := by norm_num
    rw [this]
    exact Nat.Coprime.mul_right h2 h3

-- k = l = 0 case: we need m + 1 to not be prime
theorem base_case (m : ℕ) (h : AvoidsPrimes m) : ¬ (m + 1).Prime := by
  have := h.2 0 0
  simp only [candidateNumber, pow_zero, one_mul] at this
  exact this

-- Small examples that don't work
-- m = 1: 1 + 1 = 2 is prime
theorem one_fails : ¬ AvoidsPrimes 1 := by
  intro ⟨_, h⟩
  have := h 0 0
  simp only [candidateNumber, pow_zero, one_mul] at this
  exact this Nat.prime_two

-- m = 5: 5 + 1 = 6 not prime, but 2*5 + 1 = 11 is prime
theorem five_fails : ¬ AvoidsPrimes 5 := by
  intro ⟨_, h⟩
  have := h 1 0
  simp only [candidateNumber, pow_zero, one_mul, pow_one] at this
  have : (2 * 5 + 1 : ℕ) = 11 := by norm_num
  rw [this] at this
  exact this (by decide : Nat.Prime 11)

/-!
# Part 7: Generalized Problems

Erdős-Graham also asked about more general forms.
-/

-- General form: p₁^{k₁} * ... * p_r^{k_r} * m + 1
def IsGeneralizedAvoiding (primes : List ℕ) (m : ℕ) : Prop :=
  m.Coprime (primes.foldl (·*·) 1) ∧
  ∀ exps : List ℕ, exps.length = primes.length →
    ¬ ((List.zipWith (·^·) primes exps).foldl (·*·) 1 * m + 1).Prime

-- Variant: q₁ * ... * q_r * m + 1 where q_i ≡ 1 (mod 4)
def IsQuadraticResidue (q : ℕ) : Prop := q.Prime ∧ q % 4 = 1

def QuadraticProductAvoiding (qs : List ℕ) (m : ℕ) : Prop :=
  (∀ q ∈ qs, IsQuadraticResidue q) ∧
  m.Coprime (qs.foldl (·*·) 1) ∧
  ¬ (qs.foldl (·*·) 1 * m + 1).Prime

/-!
# Part 8: Problem Status

The problem remains OPEN. No such m has been found or proven to not exist.
-/

-- The problem is open
def erdos_203_status : String := "OPEN"

-- The main formal statement
theorem erdos_203_statement :
    ErdosConjecture203 ↔
    ∃ m, m.Coprime 6 ∧ ∀ k l, ¬ (2^k * 3^l * m + 1).Prime := by
  exact conjecture_equiv

-- Summary of what's known
-- - Sierpinski numbers exist (using covering systems)
-- - No m satisfying Problem 203 has been found
-- - The problem is likely very difficult due to two-dimensional nature

end Erdos203
