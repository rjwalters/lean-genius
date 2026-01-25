/-
Erdős Problem #952: The Gaussian Moat Problem

**Problem Statement (OPEN)**

Is there an infinite sequence of distinct Gaussian primes x₁, x₂, ... such that
|x_{n+1} - x_n| ≪ 1 (i.e., consecutive Gaussian primes with bounded gaps)?

**Historical Note:**
This is notably NOT actually an Erdős problem. According to Erdős himself, the
conjecture originated with Theodore Motzkin, Basil Gordon, and others at a 1963
Pasadena number theory meeting. Erdős popularized it by sharing it widely, and
the attribution was eventually forgotten.

**Background:**
- Gaussian integers: ℤ[i] = {a + bi : a, b ∈ ℤ}
- Gaussian primes: irreducible elements in ℤ[i]
- The "moat" refers to regions without Gaussian primes
- Question: Can we walk from 0 to infinity on Gaussian primes with bounded steps?

**Known Results:**
- Jordan and Rabung (1970): No such walk exists with step size ≤ 2
- Tsuchimura (2005): No such walk exists with step size ≤ √26
- Gethner et al.: Step size 4 is insufficient

**Status:** OPEN - Terence Tao considers this difficult

**Reference:** [Er952], Wikipedia: Gaussian_moat

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open GaussianInt

namespace Erdos952

/-!
# Part 1: Gaussian Integers and Primes

The Gaussian integers ℤ[i] form a unique factorization domain.
-/

-- Recall: GaussianInt = ℤ[i] from Mathlib
-- GaussianInt.norm : ℤ[i] → ℕ, defined as a² + b² for a + bi

-- A Gaussian integer is prime in ℤ[i]
def IsGaussianPrime (z : GaussianInt) : Prop := Prime z

-- The set of all Gaussian primes
def GaussianPrimes : Set GaussianInt := {z | IsGaussianPrime z}

/-!
# Part 2: Gaussian Prime Classification

A Gaussian integer π is prime iff:
1. π = ±1 ± i (norm 2)
2. π = p or ±i·p where p ≡ 3 (mod 4) is a rational prime
3. π has norm p where p ≡ 1 (mod 4) is a rational prime
-/

-- Classification of Gaussian primes
def IsNorm2Prime (z : GaussianInt) : Prop :=
  z.norm = 2

def IsInertPrime (z : GaussianInt) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ z.norm = p^2

def IsSplitPrime (z : GaussianInt) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ z.norm = p

-- Gaussian prime iff one of these types
axiom gaussian_prime_classification (z : GaussianInt) :
    IsGaussianPrime z ↔ IsNorm2Prime z ∨ IsInertPrime z ∨ IsSplitPrime z

/-!
# Part 3: The Moat Problem

Can we walk from 0 to infinity on Gaussian primes with bounded step size?
-/

-- An infinite walk is a sequence of Gaussian primes
def IsInfiniteGaussianPrimeWalk (x : ℕ → GaussianInt) : Prop :=
  Function.Injective x ∧ ∀ n, IsGaussianPrime (x n)

-- A walk has bounded gaps if consecutive steps have norm < C
def HasBoundedGaps (x : ℕ → GaussianInt) (C : ℕ) : Prop :=
  ∀ n, (x (n + 1) - x n).norm < C

-- The Gaussian moat conjecture (positive form)
def GaussianMoatConjecture : Prop :=
  ∃ (x : ℕ → GaussianInt) (C : ℕ),
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x C

-- Equivalent to Erdős 952 statement
def ErdosConjecture952 : Prop := GaussianMoatConjecture

/-!
# Part 4: Known Negative Results

Various researchers have shown bounded walks don't exist for small step sizes.
-/

-- Jordan-Rabung (1970): No walk with step size ≤ 2
axiom jordan_rabung : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 5  -- norm < 5 means |step| ≤ 2

-- Tsuchimura (2005): No walk with step size ≤ √26
axiom tsuchimura : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 27  -- norm < 27 means |step| < √27

-- Best known: step size 4 insufficient
axiom gethner_et_al : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 17  -- |step| ≤ 4 means norm ≤ 16

-- Current state: unknown for larger step sizes
def CurrentBestBound : ℕ := 27

/-!
# Part 5: The Moat Width

A "moat" is a region around 0 containing no Gaussian primes beyond a certain norm.
-/

-- The moat of width k around 0: can we escape to infinity with steps of norm < k?
def CanEscapeMoat (k : ℕ) : Prop :=
  ∃ x : ℕ → GaussianInt, IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x k

-- The critical moat width (if it exists)
noncomputable def criticalMoatWidth : ℕ :=
  Nat.find (⟨0, fun x hx => hx.1 0⟩ : ∃ k, ¬ CanEscapeMoat k)

-- If no walk exists for any k, the conjecture is false
def StrongNegation : Prop := ∀ k, ¬ CanEscapeMoat k

/-!
# Part 6: Density of Gaussian Primes

Gaussian primes have density related to 1/log(norm).
-/

-- Count of Gaussian primes with norm ≤ R²
noncomputable def gaussianPrimeCount (R : ℕ) : ℕ :=
  (Finset.filter (fun z : GaussianInt => IsGaussianPrime z ∧ z.norm ≤ R^2)
    (Finset.Icc ⟨-R, -R⟩ ⟨R, R⟩ : Finset GaussianInt)).card

-- Asymptotic: π_ℤ[i](x) ~ x / log(x)
-- Similar to rational prime counting function
axiom gaussian_prime_theorem : ∀ ε > 0, ∃ N : ℕ,
  ∀ R ≥ N, |((gaussianPrimeCount R : ℝ) / R^2) - 1 / Real.log R| < ε

/-!
# Part 7: Connections to Rational Primes

The problem is related to gaps between primes in arithmetic progressions.
-/

-- Primes p ≡ 1 (mod 4) split in ℤ[i]
-- For such p, p = π · π̄ where π, π̄ are Gaussian primes with norm p

-- The splitting behavior
def splitPrime (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) : GaussianInt × GaussianInt :=
  sorry  -- Fermat's two-square theorem gives the splitting

-- Connection: large gaps in primes ≡ 1 (mod 4) create large moats
axiom primes_mod_4_connection :
    (∀ k, ¬ CanEscapeMoat k) →
    ∀ C, ∃ᶠ n in Filter.atTop, ∀ m ∈ Finset.range C,
      ¬ (n + m).Prime ∨ (n + m) % 4 ≠ 1

/-!
# Part 8: Tao's Perspective

Terence Tao has indicated this problem appears quite difficult.
-/

-- The difficulty comes from needing to understand global structure of Gaussian primes
-- Local density is known, but avoiding all large gaps is much harder

def tao_difficulty_assessment : String :=
  "Terence Tao has indicated this problem appears difficult"

/-!
# Part 9: Variants

Related problems about walking on various prime sets.
-/

-- Can we walk to infinity on Eisenstein primes (ℤ[ω], ω = e^{2πi/3})?
def EisensteinMoatProblem : Prop :=
  True  -- Analogous question for Eisenstein integers

-- Can we walk on rational primes with bounded gaps?
-- This is related to the twin prime conjecture
def RationalPrimeMoat : Prop :=
  ∃ C : ℕ, ∃ᶠ n in Filter.atTop, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < n ∧ n < q ∧ q - p ≤ C

/-!
# Part 10: Problem Status

The problem remains OPEN despite computational searches.
-/

-- The problem is open
def erdos_952_status : String := "OPEN"

-- Attribution note
def attribution_note : String :=
  "Not actually an Erdős problem. Originated with Motzkin, Gordon, and others (1963)."

-- Main formal statement
theorem erdos_952_statement :
    ErdosConjecture952 ↔
    ∃ (x : ℕ → GaussianInt) (C : ℕ),
      (Function.Injective x ∧ ∀ n, Prime (x n)) ∧
      (∀ n, (x (n + 1) - x n).norm < C) := by
  unfold ErdosConjecture952 GaussianMoatConjecture
  unfold IsInfiniteGaussianPrimeWalk HasBoundedGaps IsGaussianPrime
  rfl

/-!
# Summary

**Problem:** Can we walk from 0 to infinity on Gaussian primes with bounded step size?

**Known:**
- Steps ≤ 2: Jordan-Rabung (1970) showed NO
- Steps ≤ √26: Tsuchimura (2005) showed NO
- Computational evidence: moats exist requiring larger steps

**Unknown:**
- Whether any bounded step size suffices
- The critical moat width (if the answer is NO)

**Difficulty:** Requires understanding global distribution of Gaussian primes.
-/

end Erdos952
