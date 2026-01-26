/-!
# Erdős Problem #346 — Complete Sequences and the Golden Ratio

Let A = {a₁ < a₂ < ⋯} be a sequence such that:
- A \ B is complete for any finite subset B (strongly complete)
- A \ B is not complete for any infinite subset B

If a_{n+1}/a_n ≥ 1 + ε for some ε > 0 and all n (lacunary), must
lim a_{n+1}/a_n = φ = (1 + √5)/2?

## Known results

- Graham (1964): The sequence a_n = F_n − (−1)^n satisfies both properties.
- If a_{n+1}/a_n > φ for all n, the second property holds automatically.
- Very irregular sequences satisfying both properties exist.

Reference: https://erdosproblems.com/346
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Complete sequences -/

/-- Subset sums of a set of natural numbers. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
    { s | ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧ S.sum id = s }

/-- A set is complete if it represents all sufficiently large integers. -/
def IsComplete (A : Set ℕ) : Prop :=
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → n ∈ subsetSums A

/-! ## Strong completeness and fragility -/

/-- A is strongly complete: removing any finite subset preserves completeness. -/
def IsStronglyComplete (A : Set ℕ) : Prop :=
    ∀ B : Finset ℕ, IsComplete (A \ (↑B : Set ℕ))

/-- A is fragile: removing any infinite subset destroys completeness. -/
def IsFragile (A : Set ℕ) : Prop :=
    ∀ B : Set ℕ, Set.Infinite B → ¬IsComplete (A \ B)

/-! ## Lacunary sequences -/

/-- A sequence is lacunary with gap ≥ 1 + ε. -/
def IsLacunary (a : ℕ → ℕ) (ε : ℚ) : Prop :=
    0 < ε ∧ ∀ n : ℕ, (1 + ε) * (a n : ℚ) ≤ (a (n + 1) : ℚ)

/-- The golden ratio φ = (1 + √5)/2 ≈ 1.618. -/
noncomputable def goldenRatio : ℚ := 1618 / 1000

/-! ## Graham's example -/

/-- Graham's sequence: a_n = F_n − (−1)^n. -/
def grahamSeq (n : ℕ) : ℕ :=
    if n % 2 = 0 then Nat.fib n - 1 else Nat.fib n + 1

/-- Graham (1964): grahamSeq satisfies strong completeness. -/
axiom graham_strongly_complete :
    IsStronglyComplete { n | ∃ k, n = grahamSeq k ∧ 0 < n }

/-- Graham (1964): grahamSeq satisfies fragility. -/
axiom graham_fragile :
    IsFragile { n | ∃ k, n = grahamSeq k ∧ 0 < n }

/-! ## Golden ratio threshold -/

/-- If a_{n+1}/a_n > φ for all n, then A is automatically fragile. -/
axiom golden_ratio_fragile (a : ℕ → ℕ)
    (h : ∀ n : ℕ, goldenRatio * (a n : ℚ) < (a (n + 1) : ℚ)) :
    IsFragile { n | ∃ k, n = a k }

/-! ## Main conjecture -/

/-- Erdős Problem 346: if A is lacunary, strongly complete, and fragile,
    then lim a_{n+1}/a_n = φ.
    Formally: for every ε > 0, eventually |a_{n+1}/a_n − φ| < ε. -/
def ErdosProblem346 : Prop :=
    ∀ (a : ℕ → ℕ),
      (∃ ε : ℚ, IsLacunary a ε) →
      IsStronglyComplete { n | ∃ k, n = a k } →
      IsFragile { n | ∃ k, n = a k } →
        ∀ δ : ℚ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < a n →
          |((a (n + 1) : ℚ) / (a n : ℚ)) - goldenRatio| < δ

/-- There exist very irregular sequences satisfying both properties
    whose ratio does not converge. -/
axiom irregular_examples :
    ∃ (a : ℕ → ℕ),
      IsStronglyComplete { n | ∃ k, n = a k } ∧
      IsFragile { n | ∃ k, n = a k } ∧
      ¬(∀ δ : ℚ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < a n →
          |((a (n + 1) : ℚ) / (a n : ℚ)) - goldenRatio| < δ)
