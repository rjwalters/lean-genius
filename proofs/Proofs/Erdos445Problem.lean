/-
Erdős Problem #445: Multiplicative Inverses in Short Intervals

Source: https://erdosproblems.com/445
Status: OPEN (for c ∈ (1/2, 3/4])

Statement:
For any c > 1/2, if p is a sufficiently large prime, then for any n ≥ 0,
there exist a, b ∈ (n, n + p^c) such that ab ≡ 1 (mod p).

Known Results:
- Heilbronn (unpublished): True for c sufficiently close to 1
- Heath-Brown (2000): True for all c > 3/4 using Kloosterman sums
- c ∈ (1/2, 3/4]: OPEN

References:
- Heath-Brown [HB00]: Pairs of integers with no large prime factors
- Heilbronn: Unpublished result for c close to 1

Tags: number-theory, modular-arithmetic, kloosterman-sums
-/

import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos445

open Nat Finset Real

/- ## Part 1: Basic Definitions -/

/-- An element a has multiplicative inverse b mod p -/
def HasInverse (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℕ) : Prop :=
  (a * b) % p = 1

/-- The interval (n, n + L) -/
def OpenInterval (n L : ℕ) : Finset ℕ :=
  (Finset.range L).filter (fun k => k > 0) |>.image (fun k => n + k)

/-- There exist inverse pairs in the interval (n, n + p^c) -/
def HasInversePairInInterval (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) (c : ℝ) : Prop :=
  ∃ a b : ℕ, a ∈ OpenInterval n (Nat.floor (p ^ c)) ∧
             b ∈ OpenInterval n (Nat.floor (p ^ c)) ∧
             HasInverse p a b

/- ## Part 2: The Main Conjecture -/

/-- The main conjecture: for c > 1/2, there exist inverses in (n, n + p^c) -/
def MainConjecture : Prop :=
  ∀ c : ℝ, c > 1/2 →
    ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] → p > P₀ →
      ∀ n : ℕ, HasInversePairInInterval p n c

/-- The strong conjecture: c = 1/2 is the exact threshold -/
def StrongConjecture : Prop :=
  MainConjecture ∧
  ¬(∀ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] → p > P₀ →
      ∀ n : ℕ, HasInversePairInInterval p n (1/2))

/- ## Part 3: Heilbronn's Result -/

/-- Heilbronn's threshold: some c₀ close to 1 -/
axiom heilbronn_threshold : ℝ

/-- Heilbronn: c₀ < 1 and the conjecture holds for c > c₀ -/
axiom heilbronn_unpublished :
  heilbronn_threshold < 1 ∧
  ∀ c : ℝ, c > heilbronn_threshold →
    ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] → p > P₀ →
      ∀ n : ℕ, HasInversePairInInterval p n c

/- ## Part 4: Heath-Brown's Result -/

/-- Kloosterman sum K(m, n; p) = Σₓ e^{2πi(mx + nx⁻¹)/p}.
    Axiomatized as it requires exponential sum machinery. -/
axiom KloostermanSum (p : ℕ) [Fact (Nat.Prime p)] (m n : ℤ) : ℂ

/-- Weil's bound: |K(m, n; p)| ≤ 2√p -/
axiom weil_bound (p : ℕ) [Fact (Nat.Prime p)] (m n : ℤ) :
  Complex.abs (KloostermanSum p m n) ≤ 2 * Real.sqrt p

/-- Heath-Brown (2000): The conjecture holds for all c > 3/4 -/
axiom heath_brown_2000 :
  ∀ c : ℝ, c > 3/4 →
    ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] → p > P₀ →
      ∀ n : ℕ, HasInversePairInInterval p n c

/-- Heath-Brown's bound is 3/4 -/
theorem heath_brown_threshold : ∃ c₀ : ℝ, c₀ = 3/4 ∧
    (∀ c > c₀, ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] → p > P₀ →
      ∀ n : ℕ, HasInversePairInInterval p n c) := by
  use 3/4
  constructor
  · rfl
  · exact heath_brown_2000

/- ## Part 5: The Open Range -/

/-- The open range c ∈ (1/2, 3/4] -/
def OpenRange : Set ℝ := Set.Ioc (1/2) (3/4)

/-- What we know: c > 3/4 works, and OpenRange ⊆ (1/2, 1) -/
theorem current_knowledge :
    (∀ c > (3/4 : ℝ), ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] → p > P₀ →
      ∀ n : ℕ, HasInversePairInInterval p n c) ∧
    OpenRange ⊆ Set.Ioc (1/2) 1 := by
  constructor
  · exact heath_brown_2000
  · intro x hx
    constructor
    · exact hx.1
    · calc x ≤ 3/4 := hx.2
           _ < 1 := by norm_num

/- ## Part 6: Summary -/

/-- **Summary of Erdős Problem #445:**

PROBLEM: For c > 1/2, do inverse pairs a,b with ab ≡ 1 (mod p)
exist in every interval (n, n + p^c) for large primes p?

STATUS: OPEN for c ∈ (1/2, 3/4]

KNOWN:
1. Heilbronn: holds for c close to 1 (unpublished, c₀ < 1)
2. Heath-Brown (2000): holds for all c > 3/4

This theorem packages both known results. -/
theorem erdos_445_summary :
    (∃ c₀ : ℝ, c₀ < 1 ∧ ∀ c : ℝ, c > c₀ →
      ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] → p > P₀ →
        ∀ n : ℕ, HasInversePairInInterval p n c) ∧
    (∀ c : ℝ, c > 3/4 →
      ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] → p > P₀ →
        ∀ n : ℕ, HasInversePairInInterval p n c) :=
  ⟨⟨heilbronn_threshold, heilbronn_unpublished.1, heilbronn_unpublished.2⟩, heath_brown_2000⟩

end Erdos445
