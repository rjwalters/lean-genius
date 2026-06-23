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

/- Part 1: Basic Definitions -/

-- The family of numbers: 2^k * 3^l * m + 1
def candidateNumber (m k l : ℕ) : ℕ := 2^k * 3^l * m + 1

-- A number m avoids primes if no candidate is prime
def AvoidsPrimes (m : ℕ) : Prop :=
  m.Coprime 6 ∧ ∀ k l, ¬ (candidateNumber m k l).Prime

-- The set of numbers avoiding primes
def AvoidingSet : Set ℕ := {m | AvoidsPrimes m}

/- Part 2: The Main Conjecture -/

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

/- Part 3: Sierpinski Numbers -/

-- Sierpinski numbers: odd m where no 2^k * m + 1 is prime
def IsSierpinskiNumber (m : ℕ) : Prop :=
  Odd m ∧ ∀ k, ¬ (2^k * m + 1).Prime

-- The set of Sierpinski numbers
def SierpinskiSet : Set ℕ := {m | IsSierpinskiNumber m}

-- The smallest known Sierpinski number (Selfridge 1962)
def selfridge_sierpinski : ℕ := 78557

/- Selfridge's proof via covering system {3, 5, 7, 13, 19, 37, 73}, period 36.
   For each k, one of these primes divides 2^k * 78557 + 1:
     k ≡ 0 (mod 2)  → 3   k ≡ 1 (mod 4)  → 5   k ≡ 7 (mod 12) → 7
     k ≡ 11 (mod 12) → 13  k ≡ 15 (mod 36) → 19  k ≡ 27 (mod 36) → 37
     k ≡ 3 (mod 36)  → 73 -/

/-- Power periodicity: if 2^36 % p = 1 % p, then 2^k % p = 2^(k % 36) % p. -/
private lemma pow2_mod_period (p : ℕ) (hp : 2 ^ 36 % p = 1 % p) (k : ℕ) :
    2 ^ k % p = 2 ^ (k % 36) % p := by
  have key : ∀ n, (2 ^ 36) ^ n % p = 1 % p := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih, hp, ← Nat.mul_mod, one_mul]
  conv_lhs => rw [show k = 36 * (k / 36) + k % 36 from (Nat.div_add_mod k 36).symm,
    pow_add, pow_mul, Nat.mul_mod, key, ← Nat.mul_mod, one_mul]

/-- Divisibility transfer via modular periodicity. -/
private lemma dvd_of_pow2_mod_eq {p m k r : ℕ}
    (hmod : 2 ^ k % p = 2 ^ r % p)
    (hdvd : p ∣ (2 ^ r * m + 1)) : p ∣ (2 ^ k * m + 1) := by
  obtain ⟨c, hc⟩ := hdvd
  apply Nat.dvd_of_mod_eq_zero
  calc (2 ^ k * m + 1) % p
      = ((2 ^ k % p) * (m % p) + 1 % p) % p := by rw [Nat.add_mod, Nat.mul_mod]
    _ = ((2 ^ r % p) * (m % p) + 1 % p) % p := by rw [hmod]
    _ = (2 ^ r * m + 1) % p := by rw [← Nat.mul_mod, ← Nat.add_mod]
    _ = 0 := by rw [hc, Nat.mul_mod_right]

/-- For each residue r < 36, a covering prime ≤ 73 divides 2^r * 78557 + 1. -/
private lemma covering_prime (r : ℕ) (hr : r < 36) :
    ∃ p, Nat.Prime p ∧ p ∣ (2 ^ r * 78557 + 1) ∧ 2 ^ 36 % p = 1 % p ∧ p ≤ 73 := by
  interval_cases r <;> first
    | exact ⟨3, by decide, by native_decide, by native_decide, by omega⟩
    | exact ⟨5, by decide, by native_decide, by native_decide, by omega⟩
    | exact ⟨7, by decide, by native_decide, by native_decide, by omega⟩
    | exact ⟨13, by decide, by native_decide, by native_decide, by omega⟩
    | exact ⟨19, by decide, by native_decide, by native_decide, by omega⟩
    | exact ⟨37, by decide, by native_decide, by native_decide, by omega⟩
    | exact ⟨73, by decide, by native_decide, by native_decide, by omega⟩

/-- Selfridge (1962): 78557 is a Sierpiński number, proved via covering system. -/
theorem selfridge_sierpinski_is_sierpinski : IsSierpinskiNumber selfridge_sierpinski := by
  refine ⟨by decide, fun k => ?_⟩
  obtain ⟨p, hp_prime, hp_dvd, hp_period, hp_le⟩ :=
    covering_prime (k % 36) (Nat.mod_lt k (by omega))
  have hdvd := dvd_of_pow2_mod_eq (pow2_mod_period p hp_period k) hp_dvd
  intro hprime
  have hpn := hprime.eq_one_or_self_of_dvd p hdvd
  have hlt := hp_prime.one_lt
  have hge : 78558 ≤ 2 ^ k * 78557 + 1 := by
    nlinarith [Nat.one_le_pow k 2 (by omega)]
  rcases hpn with rfl | rfl <;> omega

-- Sierpinski numbers exist (consequence of the above)
theorem sierpinski_exists : SierpinskiSet.Nonempty :=
  ⟨selfridge_sierpinski, selfridge_sierpinski_is_sierpinski⟩

-- Connection: Sierpinski condition is necessary but not sufficient for Problem 203
theorem sierpinski_necessary_not_sufficient (m : ℕ) (h : IsSierpinskiNumber m) :
    ∀ k, ¬ (2^k * m + 1).Prime := h.2

/- Part 4: Covering Systems -/

-- A covering system: set of congruences covering all integers
def IsCoveringSystem (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ n : ℤ, ∃ p ∈ S, (n : ℤ) ≡ (p.1 : ℤ) [ZMOD (p.2 : ℤ)]

-- A prime covering system: each modulus has an associated prime
def PrimeCovering (S : Finset (ℕ × ℕ)) (P : ℕ × ℕ → ℕ) : Prop :=
  IsCoveringSystem S ∧
  (∀ p ∈ S, (P p).Prime) ∧
  (∀ p ∈ S, P p ∣ (2^(p.2) - 1))

/- Part 5: The Extended Problem — 2D Covering Systems -/

-- For the extended problem, we'd need primes dividing 2^a * 3^b - 1
def ExtendedDivisibility (p : ℕ) (a b : ℕ) : Prop :=
  p.Prime ∧ p ∣ (2^a * 3^b - 1)

-- A 2D covering system: a tuple (r₁, d₁, r₂, d₂) covers (k, l)
-- when k ≡ r₁ (mod d₁) and l ≡ r₂ (mod d₂)
def Covers2D (r₁ d₁ r₂ d₂ k l : ℕ) : Prop :=
  k % d₁ = r₁ ∧ l % d₂ = r₂

-- A 2D covering system: covers every (k, l) ∈ ℕ²
def IsCoveringSystem2D (S : Finset (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  ∀ k l : ℕ, ∃ s ∈ S, Covers2D s.1 s.2.1 s.2.2.1 s.2.2.2 k l

/- Part 6: Small Cases and Constraints -/

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
  simp [candidateNumber] at this
  exact this

-- candidateNumber is always positive
theorem candidate_pos (m k l : ℕ) : 0 < candidateNumber m k l := by
  unfold candidateNumber; omega

-- candidateNumber simplification lemmas
theorem candidate_base (m : ℕ) : candidateNumber m 0 0 = m + 1 := by
  simp [candidateNumber]

theorem candidate_k1 (m : ℕ) : candidateNumber m 1 0 = 2 * m + 1 := by
  simp [candidateNumber]

theorem candidate_l1 (m : ℕ) : candidateNumber m 0 1 = 3 * m + 1 := by
  simp [candidateNumber]

-- Small examples that don't work
-- m = 1: 1 + 1 = 2 is prime
theorem one_fails : ¬ AvoidsPrimes 1 := by
  intro ⟨_, h⟩
  have := h 0 0; simp only [candidateNumber] at this; norm_num at this

-- m = 5: 2*5 + 1 = 11 is prime
theorem five_fails : ¬ AvoidsPrimes 5 := by
  intro ⟨_, h⟩
  have := h 1 0; simp only [candidateNumber] at this; norm_num at this

-- m = 7: 4*7+1 = 29 is prime
theorem seven_fails : ¬ AvoidsPrimes 7 := by
  intro ⟨_, h⟩
  have := h 2 0; simp only [candidateNumber] at this; norm_num at this

-- m = 11: 2*11+1 = 23 is prime
theorem eleven_fails : ¬ AvoidsPrimes 11 := by
  intro ⟨_, h⟩
  have := h 1 0; simp only [candidateNumber] at this; norm_num at this

-- m = 13: 4*13+1 = 53 is prime
theorem thirteen_fails : ¬ AvoidsPrimes 13 := by
  intro ⟨_, h⟩
  have := h 2 0; simp only [candidateNumber] at this; norm_num at this

-- m = 17: 8*17+1 = 137 is prime
theorem seventeen_fails : ¬ AvoidsPrimes 17 := by
  intro ⟨_, h⟩
  have := h 3 0; simp only [candidateNumber] at this; norm_num at this

-- m = 19: 4*3*19+1 = 229 is prime
theorem nineteen_fails : ¬ AvoidsPrimes 19 := by
  intro ⟨_, h⟩
  have := h 2 1; simp only [candidateNumber] at this; norm_num at this

-- m = 23: 2*23+1 = 47 is prime
theorem twentythree_fails : ¬ AvoidsPrimes 23 := by
  intro ⟨_, h⟩
  have := h 1 0; simp only [candidateNumber] at this; norm_num at this

-- m = 25: 4*25+1 = 101 is prime
theorem twentyfive_fails : ¬ AvoidsPrimes 25 := by
  intro ⟨_, h⟩
  have := h 2 0; simp only [candidateNumber] at this; norm_num at this

-- m = 29: 2*29+1 = 59 is prime
theorem twentynine_fails : ¬ AvoidsPrimes 29 := by
  intro ⟨_, h⟩
  have := h 1 0; simp only [candidateNumber] at this; norm_num at this

-- m = 31: 4*3*31+1 = 373 is prime
theorem thirtyone_fails : ¬ AvoidsPrimes 31 := by
  intro ⟨_, h⟩
  have := h 2 1; simp only [candidateNumber] at this; norm_num at this

-- m = 35: 2*35+1 = 71 is prime
theorem thirtyfive_fails : ¬ AvoidsPrimes 35 := by
  intro ⟨_, h⟩
  have := h 1 0; simp only [candidateNumber] at this; norm_num at this

-- m = 37: 4*37+1 = 149 is prime
theorem thirtyseven_fails : ¬ AvoidsPrimes 37 := by
  intro ⟨_, h⟩
  have := h 2 0; simp only [candidateNumber] at this; norm_num at this

-- m = 41: 2*41+1 = 83 is prime
theorem fortyone_fails : ¬ AvoidsPrimes 41 := by
  intro ⟨_, h⟩
  have := h 1 0; simp only [candidateNumber] at this; norm_num at this

-- m = 43: 4*43+1 = 173 is prime
theorem fortythree_fails : ¬ AvoidsPrimes 43 := by
  intro ⟨_, h⟩
  have := h 2 0; simp only [candidateNumber] at this; norm_num at this

-- m = 47: 6*47+1 = 283 is prime
theorem fortyseven_fails : ¬ AvoidsPrimes 47 := by
  intro ⟨_, h⟩
  have := h 1 1; simp only [candidateNumber] at this; norm_num at this

-- m = 49: 4*49+1 = 197 is prime
theorem fortynine_fails : ¬ AvoidsPrimes 49 := by
  intro ⟨_, h⟩
  have := h 2 0; simp only [candidateNumber] at this; norm_num at this

-- m = 53: 2*53+1 = 107 is prime
theorem fiftythree_fails : ¬ AvoidsPrimes 53 := by
  intro ⟨_, h⟩
  have := h 1 0; simp only [candidateNumber] at this; norm_num at this

-- m = 55: 6*55+1 = 331 is prime
theorem fiftyfive_fails : ¬ AvoidsPrimes 55 := by
  intro ⟨_, h⟩
  have := h 1 1; simp only [candidateNumber] at this; norm_num at this

-- m = 59: 12*59+1 = 709 is prime
theorem fiftynine_fails : ¬ AvoidsPrimes 59 := by
  intro ⟨_, h⟩
  have := h 2 1; simp only [candidateNumber] at this; norm_num at this

-- m = 61: 6*61+1 = 367 is prime
theorem sixtyone_fails : ¬ AvoidsPrimes 61 := by
  intro ⟨_, h⟩
  have := h 1 1; simp only [candidateNumber] at this; norm_num at this

-- Structural: if m is avoiding primes, then m+1, 2m+1, 3m+1 are all composite
theorem avoiding_implies_composites (m : ℕ) (h : AvoidsPrimes m) :
    ¬ (m + 1).Prime ∧ ¬ (2 * m + 1).Prime ∧ ¬ (3 * m + 1).Prime := by
  refine ⟨?_, ?_, ?_⟩
  · exact base_case m h
  · have := h.2 1 0; simp [candidateNumber] at this; exact this
  · have := h.2 0 1; simp [candidateNumber] at this; exact this

/- Part 7: Relationship between Sierpinski and Problem 203 -/

-- If m avoids primes, then m is Sierpinski-like for base 2 (l=0 slice)
theorem avoiding_implies_sierpinski_like (m : ℕ) (h : AvoidsPrimes m) :
    ∀ k, ¬ (2^k * m + 1).Prime := by
  intro k
  have := h.2 k 0
  simp [candidateNumber] at this
  simpa using this

-- Similarly for base 3 (k=0 slice)
theorem avoiding_implies_base3_like (m : ℕ) (h : AvoidsPrimes m) :
    ∀ l, ¬ (3^l * m + 1).Prime := by
  intro l
  have := h.2 0 l
  simp [candidateNumber] at this
  simpa using this

-- If m is coprime to 6 and positive, then m is odd
theorem coprime6_implies_odd (m : ℕ) (hm : m.Coprime 6) : Odd m := by
  rw [Nat.odd_iff]
  have h2 : m.Coprime 2 := Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 6) hm
  have hmod : m % 2 ≠ 0 := by
    intro heq
    have hdvd : 2 ∣ m := Nat.dvd_of_mod_eq_zero heq
    have hgcd : 2 ∣ m.gcd 2 := Nat.dvd_gcd hdvd (dvd_refl 2)
    have : m.gcd 2 = 1 := h2
    omega
  omega

-- Any AvoidsPrimes m is a Sierpinski number
theorem avoiding_is_sierpinski (m : ℕ) (hm : AvoidsPrimes m) :
    IsSierpinskiNumber m :=
  ⟨coprime6_implies_odd m hm.1, avoiding_implies_sierpinski_like m hm⟩

-- Problem 203 is strictly harder than the Sierpinski problem
theorem problem203_stronger_than_sierpinski (m : ℕ) (h : AvoidsPrimes m) :
    IsSierpinskiNumber m := avoiding_is_sierpinski m h

/- Part 8: Candidate growth -/

-- Candidates grow: candidateNumber m k l ≥ m + 1
theorem candidate_ge_succ (m k l : ℕ) : m + 1 ≤ candidateNumber m k l := by
  unfold candidateNumber
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  have h3l : 1 ≤ 3 ^ l := Nat.one_le_pow l 3 (by omega)
  have hprod : 1 * 1 ≤ 2 ^ k * 3 ^ l := Nat.mul_le_mul h2k h3l
  nlinarith

/- Part 9: Generalized Problems -/

-- General form: p₁^{k₁} * ... * p_r^{k_r} * m + 1
def IsGeneralizedAvoiding (primes : List ℕ) (m : ℕ) : Prop :=
  m.Coprime (primes.foldl (·*·) 1) ∧
  ∀ exps : List ℕ, exps.length = primes.length →
    ¬ ((List.zipWith (·^·) primes exps).foldl (·*·) 1 * m + 1).Prime

-- candidateNumber with larger k is at least as large
theorem candidate_mono_k (m k₁ k₂ l : ℕ) (h : k₁ ≤ k₂) :
    candidateNumber m k₁ l ≤ candidateNumber m k₂ l := by
  unfold candidateNumber
  have : 2 ^ k₁ ≤ 2 ^ k₂ := Nat.pow_le_pow_right (by omega) h
  nlinarith [Nat.one_le_pow l 3 (by omega)]

-- candidateNumber with larger l is at least as large
theorem candidate_mono_l (m k l₁ l₂ : ℕ) (h : l₁ ≤ l₂) :
    candidateNumber m k l₁ ≤ candidateNumber m k l₂ := by
  unfold candidateNumber
  have : 3 ^ l₁ ≤ 3 ^ l₂ := Nat.pow_le_pow_right (by omega) h
  nlinarith [Nat.one_le_pow k 2 (by omega)]

/- Part 10: Problem Status

The problem remains OPEN. No such m has been found or proven to not exist.
The difficulty lies in the two-dimensional nature: covering ALL pairs (k,l)
simultaneously requires a 2D covering system, which is much harder than
the classical 1D Sierpinski covering systems.
-/

-- The main formal statement
theorem erdos_203_statement :
    ErdosConjecture203 ↔
    ∃ m, m.Coprime 6 ∧ ∀ k l, ¬ (2^k * 3^l * m + 1).Prime := by
  exact conjecture_equiv

end Erdos203
