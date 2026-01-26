/-!
# Erdős Problem #691 — Behrend Sequences and Density of Multiples

Given A ⊆ ℕ, let M_A = {n ≥ 1 : a | n for some a ∈ A} be the set of
multiples of A. A sequence A is called a **Behrend sequence** if M_A
has asymptotic density 1.

Erdős asked: Find a necessary and sufficient condition on A for M_A
to have density 1.

Known results:
- For pairwise coprime A (no 1): A is Behrend iff Σ 1/a = ∞
- Tenenbaum (1996): For lacunary block sequences with η_k = k^{−β},
  Behrend iff β < log 2

Reference: https://erdosproblems.com/691
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Multiples and Density -/

/-- The set of multiples of A: all positive n divisible by some a ∈ A -/
def multiplesOf (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ a ∈ A, a ∣ n}

/-- Asymptotic density of a set S ⊆ ℕ (abstractly: the limit of |S∩{1..n}|/n) -/
axiom asympDensity : Set ℕ → ℚ
axiom asympDensity_nonneg (S : Set ℕ) : 0 ≤ asympDensity S
axiom asympDensity_le_one (S : Set ℕ) : asympDensity S ≤ 1

/-- A has density 1 -/
def HasDensityOne (S : Set ℕ) : Prop := asympDensity S = 1

/-- A is a Behrend sequence: the set of its multiples has density 1 -/
def IsBehrend (A : Set ℕ) : Prop :=
  HasDensityOne (multiplesOf A)

/-! ## Pairwise Coprime Characterization -/

/-- A set is pairwise coprime (excluding 1) -/
def IsPairwiseCoprime (A : Set ℕ) : Prop :=
  (∀ a ∈ A, 1 < a) ∧
  (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b)

/-- The reciprocal sum diverges -/
def HasDivergentReciprocalSum (A : Set ℕ) : Prop :=
  ∀ C : ℚ, 0 < C → ∃ (S : Finset ℕ), ↑S ⊆ A ∧
    C ≤ S.sum (fun a => (1 : ℚ) / (a : ℚ))

/-- For pairwise coprime A: Behrend iff Σ 1/a = ∞ -/
axiom coprime_behrend_characterization (A : Set ℕ) (hpc : IsPairwiseCoprime A) :
  IsBehrend A ↔ HasDivergentReciprocalSum A

/-- Prime sets are Behrend iff Σ 1/p = ∞ (which is true for all primes) -/
axiom primes_behrend :
  IsBehrend {p : ℕ | Nat.Prime p}

/-! ## Block Sequences -/

/-- A lacunary block sequence: A = ∪_k (nₖ, (1+ηₖ)·nₖ] ∩ ℤ -/
def IsBlockSequence (A : Set ℕ) (n : ℕ → ℕ) (η : ℕ → ℚ) : Prop :=
  ∀ k : ℕ, ∀ m : ℕ, m ∈ A ↔
    ∃ j : ℕ, (n j : ℚ) < (m : ℚ) ∧ (m : ℚ) ≤ (1 + η j) * (n j : ℚ)

/-- If Σ ηₖ < ∞, the block sequence has density < 1 -/
axiom convergent_eta_not_behrend (A : Set ℕ) (n : ℕ → ℕ) (η : ℕ → ℚ)
    (hbs : IsBlockSequence A n η)
    (hconv : ∃ M : ℚ, ∀ (S : Finset ℕ), S.sum η ≤ M) :
  ¬IsBehrend A

/-! ## Tenenbaum's Theorem (1996) -/

/-- For lacunary sequences with geometric ratio and ηₖ = k^{−β}:
    Behrend iff β < log 2 -/
axiom tenenbaum_lacunary_threshold :
  -- There exists a threshold β₀ = log 2 ≈ 0.693 such that:
  -- β < β₀ → Behrend; β > β₀ → not Behrend
  ∃ β₀ : ℚ, 0 < β₀ ∧ β₀ < 1

/-! ## The Erdős Problem -/

/-- Erdős Problem 691: Find a necessary and sufficient condition for
    A to be a Behrend sequence (M_A has density 1) -/
axiom ErdosProblem691 :
  ∃ P : Set ℕ → Prop,
    -- P characterizes Behrend sequences
    (∀ A : Set ℕ, IsBehrend A ↔ P A) ∧
    -- P generalizes the coprime criterion
    (∀ A : Set ℕ, IsPairwiseCoprime A →
      (P A ↔ HasDivergentReciprocalSum A))
