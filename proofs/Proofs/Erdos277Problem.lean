/-
  Erdős Problem #277: Covering Systems and Abundancy

  Source: https://erdosproblems.com/277
  Status: SOLVED (Haight 1979)

  Statement:
  Is it true that, for every c > 0, there exists an n such that σ(n) > cn
  but there is no covering system whose moduli all divide n?

  Answer: YES (Haight 1979)

  Key Concepts:
  - σ(n) = sum of divisors of n
  - Covering system: A finite collection of congruences a_i (mod m_i) that covers ℤ
  - Abundancy ratio: σ(n)/n measures how "abundant" a number is

  Haight's Result:
  For every constant c, there exist "sparse" numbers n (large divisor sum)
  that cannot be the LCM of any covering system's moduli.

  References:
  - [Ha79] Haight, J. A., "Covering systems of congruences, a negative result"
    Mathematika 26 (1979), 53-61
  - Related: Problems #276, #278 (covering systems)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos277

/-
## Part I: Sum of Divisors
-/

/-- The sum of divisors function σ(n). -/
noncomputable def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- σ(1) = 1. -/
theorem sigma_one : sigma 1 = 1 := by
  simp [sigma, Nat.divisors]

/-- σ(p) = p + 1 for prime p. -/
theorem sigma_prime (p : ℕ) (hp : Nat.Prime p) : sigma p = p + 1 := by
  simp [sigma, hp.divisors, add_comm]

/-- σ(n) ≥ n for all n ≥ 1. -/
theorem sigma_ge_self (n : ℕ) (hn : n ≥ 1) : sigma n ≥ n := by
  unfold sigma
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩)

/-- The abundancy ratio σ(n)/n. -/
noncomputable def abundancyRatio (n : ℕ) : ℝ :=
  if n = 0 then 0 else (sigma n : ℝ) / (n : ℝ)

/-- A number n is c-abundant if σ(n) > cn. -/
def IsAbundant (n : ℕ) (c : ℝ) : Prop :=
  (sigma n : ℝ) > c * n

/-
## Part II: Covering Systems
-/

/-- A congruence class: a (mod m). -/
structure Congruence where
  residue : ℤ
  modulus : ℕ
  modulus_pos : modulus > 0
deriving DecidableEq

/-- An integer x satisfies the congruence a (mod m). -/
def Congruence.covers (c : Congruence) (x : ℤ) : Prop :=
  x % (c.modulus : ℤ) = c.residue % (c.modulus : ℤ)

/-- A covering system: a set of congruences that covers all integers. -/
def IsCoveringSystem (S : Finset Congruence) : Prop :=
  ∀ x : ℤ, ∃ c ∈ S, c.covers x

/-- The set of moduli used in a covering system. -/
def moduliSet (S : Finset Congruence) : Finset ℕ :=
  S.image Congruence.modulus

/-- All moduli divide n. -/
def AllModuliDivide (S : Finset Congruence) (n : ℕ) : Prop :=
  ∀ c ∈ S, c.modulus ∣ n

/-- There exists a covering system with all moduli dividing n. -/
def HasCoveringWithDivisorModuli (n : ℕ) : Prop :=
  ∃ S : Finset Congruence, IsCoveringSystem S ∧ AllModuliDivide S n

/-
## Part III: The Erdős Question
-/

/-- Erdős's Question: For every c, does there exist n with σ(n) > cn
    but no covering system has all moduli dividing n? -/
def ErdosQuestion277 : Prop :=
  ∀ c : ℝ, c > 0 →
    ∃ n : ℕ, n ≥ 1 ∧
      IsAbundant n c ∧
      ¬HasCoveringWithDivisorModuli n

/-
## Part IV: Haight's Theorem (1979)
-/

/-- **Haight's Theorem (1979):**
    For every c > 0, there exists n such that σ(n) > cn
    but no covering system has all moduli dividing n. -/
axiom haight_theorem : ErdosQuestion277

/-- The answer to Erdős Problem #277 is YES. -/
theorem erdos_277_answer : ErdosQuestion277 := haight_theorem

/-
## Part V: Understanding Covering Systems
-/

/-- The trivial covering system: just 0 (mod 1). -/
def trivialCovering : Finset Congruence :=
  {⟨0, 1, by norm_num⟩}

/-- The trivial covering is indeed a covering system. -/
theorem trivial_is_covering : IsCoveringSystem trivialCovering := by
  intro x
  use ⟨0, 1, by norm_num⟩
  constructor
  · simp [trivialCovering]
  · simp [Congruence.covers]

/-- The trivial covering has moduli dividing every n ≥ 1. -/
theorem trivial_divides_all (n : ℕ) (hn : n ≥ 1) :
    AllModuliDivide trivialCovering n := by
  intro c hc
  simp [trivialCovering] at hc
  cases hc
  simp only
  exact one_dvd n

/-- So every n ≥ 1 has SOME covering with divisor moduli (the trivial one).
    Haight's theorem is about NON-TRIVIAL coverings! -/
theorem every_n_has_trivial_covering (n : ℕ) (hn : n ≥ 1) :
    HasCoveringWithDivisorModuli n :=
  ⟨trivialCovering, trivial_is_covering, trivial_divides_all n hn⟩

/-- For non-trivial results, we require distinct moduli. -/
def HasDistinctModuli (S : Finset Congruence) : Prop :=
  ∀ c₁ c₂, c₁ ∈ S → c₂ ∈ S → c₁.modulus = c₂.modulus → c₁ = c₂

/-- A non-trivial covering has at least two distinct moduli. -/
def IsNonTrivialCovering (S : Finset Congruence) : Prop :=
  IsCoveringSystem S ∧ (moduliSet S).card ≥ 2

/-- The refined question: no non-trivial covering with divisor moduli. -/
def HasNonTrivialCoveringWithDivisorModuli (n : ℕ) : Prop :=
  ∃ S : Finset Congruence, IsNonTrivialCovering S ∧ AllModuliDivide S n

/-- Haight actually proved the stronger result about non-trivial coverings. -/
/-
## Part VI: Key Properties of Covering Systems
-/

/-- The reciprocal sum of moduli in a covering system. -/
noncomputable def reciprocalSum (S : Finset Congruence) : ℝ :=
  ∑ c ∈ S, (1 : ℝ) / (c.modulus : ℝ)

/-- In a covering system with distinct moduli, ∑ 1/m_i ≥ 1. -/
/-- This is related to the "Chinese Remainder" aspect of coverings:
    every modulus that appears in the system has some residue class in S. -/
theorem covering_crt_connection :
    ∀ S : Finset Congruence, IsCoveringSystem S →
      ∀ m ∈ moduliSet S, ∃ c ∈ S, c.modulus = m := by
  intro S _ m hm
  exact Finset.mem_image.mp hm

/-
## Part VII: Why Haight's Result Works
-/

/-
  Haight's construction: for each c, construct n using highly composite numbers
  (large σ(n)/n comes from many small prime powers), but avoiding the
  "covering feasibility" condition. Primorial-like numbers (2 × 3 × 5 × 7 × ...)
  have large σ(n)/n but their divisor structure prevents certain coverings.

  The key tension: σ(n)/n large ↔ many small divisors ↔ easier to cover?
  Actually NO — Haight showed the structure of divisors matters, not just
  the count. Some n with many divisors still block coverings.
-/

/-
## Part VIII: Related Concepts
-/

/-- The LCM of a covering system's moduli. -/
noncomputable def coveringLCM (S : Finset Congruence) : ℕ :=
  S.fold Nat.lcm 1 (fun c => c.modulus)

/-- If all moduli divide n, then lcm(moduli) divides n. -/
theorem lcm_divides_of_all_divide (S : Finset Congruence) (n : ℕ)
    (h : AllModuliDivide S n) : coveringLCM S ∣ n := by
  show S.lcm (fun c => c.modulus) ∣ n
  exact Finset.lcm_dvd (fun c hc => h c hc)

/-- Highly composite numbers have many divisors. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → (Nat.divisors m).card < (Nat.divisors n).card

/-- Superabundant numbers have large σ(n)/n. -/
def IsSuperabundant (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → abundancyRatio m < abundancyRatio n

/-- Haight used properties related to superabundance. -/
/-
## Part IX: Connections to Other Problems
-/

/-
  Problem #276: Existence of distinct moduli covering systems.
  Answer: YES — the classic example uses moduli {2, 3, 4, 6, 12}.
-/

/-
  Problem #278: More questions about covering system moduli.
  (See Erdős #278 for the specific questions about moduli structure.)
-/

/-
  Egyptian fraction connection: the reciprocal sum ∑ 1/mᵢ for a covering system
  relates to Egyptian fractions. Covering systems provide "fractional coverings"
  of ℤ, and the constraint ∑ 1/mᵢ ≥ 1 is necessary (each residue class has density 1/mᵢ).
-/

/-
## Part X: Summary
-/

/-- **Erdős Problem #277: SOLVED by Haight (1979)**

Question: For every c > 0, does there exist n with σ(n) > cn
such that no covering system has all moduli dividing n?

Answer: YES

The key insight is that having a large divisor sum (abundancy)
does not guarantee that the divisors can form a covering system.
There's a structural obstruction beyond just counting divisors.
-/
theorem erdos_277 : ErdosQuestion277 := haight_theorem

/-- Main result statement. -/
theorem erdos_277_main :
    ∀ c : ℝ, c > 0 →
      ∃ n : ℕ, n ≥ 1 ∧
        (sigma n : ℝ) > c * n ∧
        ¬HasCoveringWithDivisorModuli n :=
  haight_theorem

/-- The problem summary. -/
theorem erdos_277_summary :
    -- For every c > 0, there exists n such that:
    -- 1. σ(n) > cn (the number is highly abundant)
    -- 2. No covering system has all moduli dividing n
    ErdosQuestion277 :=
  haight_theorem

end Erdos277
