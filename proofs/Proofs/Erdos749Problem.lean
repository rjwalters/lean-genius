/-
# Erdős Problem #749: Dense Sumsets with Bounded Representation

For ε > 0, does there exist A ⊆ ℕ such that the lower density
of A + A is at least 1 - ε, yet the representation function
r(n) = #{(a,b) ∈ A × A : a + b = n} is bounded (by a constant
depending on ε)?

## Background
This explores the tension between additive density and representation
count. If A is a Sidon set, r(n) ≤ 2 but A + A has density 0.
If A has positive density, A + A is "large" but r(n) is typically unbounded.
Can we have both: dense sumset AND bounded r(n)?

## Related: Problem #28 (Erdős–Turán)
The Erdős–Turán conjecture asks whether r(n) must be unbounded
for any additive basis of order 2. Problem #749 asks about a
"near-basis" (lower density close to 1) with bounded r(n).

## Status: OPEN

Reference: https://erdosproblems.com/749
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- The representation function r_A(n): the number of ways to write n = a + b
    with a, b ∈ A and a ≤ b. -/
def repFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  Finset.card ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A ∧ a ≤ n - a))

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ n = a + b}

/-- The lower density of a set S ⊆ ℕ: lim inf_{N→∞} |S ∩ {1,...,N}| / N. -/
axiom lowerDensity (S : Set ℕ) : ℝ

/-- The upper density of a set S ⊆ ℕ: lim sup_{N→∞} |S ∩ {1,...,N}| / N. -/
axiom upperDensity (S : Set ℕ) : ℝ

/-- Lower density is between 0 and 1. -/
axiom lowerDensity_bounds (S : Set ℕ) : 0 ≤ lowerDensity S ∧ lowerDensity S ≤ 1

/-- Lower density ≤ upper density. -/
axiom lower_le_upper (S : Set ℕ) : lowerDensity S ≤ upperDensity S

/- ## The Representation Bounded Property -/

/-- A set A has bounded representation function: there exists C such that
    r_A(n) ≤ C for all n. -/
def HasBoundedRep (A : Set ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, repFunction A n ≤ C

/-- A set A has ε-dense sumset: the lower density of A + A is ≥ 1 - ε. -/
def HasDenseSumset (A : Set ℕ) (ε : ℝ) : Prop :=
  lowerDensity (sumSet A) ≥ 1 - ε

/- ## The Main Conjecture -/

/-- Erdős Problem #749: For every ε > 0, does there exist A ⊆ ℕ
    with HasDenseSumset A ε and HasBoundedRep A?

    This asks whether we can have a "near-basis" of order 2 with
    bounded representation function. -/
theorem erdos_749_conjecture :
    (∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ, HasDenseSumset A ε ∧ HasBoundedRep A) ∨
    (∃ ε : ℝ, ε > 0 ∧ ∀ A : Set ℕ, HasDenseSumset A ε → ¬ HasBoundedRep A) := by
  -- This is P ∨ ¬P: ¬(∀ε,∃A,...) ↔ ∃ε,∀A,¬(...) ↔ ∃ε,∀A,dense→¬bounded
  by_cases h : ∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ, HasDenseSumset A ε ∧ HasBoundedRep A
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨ε, hε, hA⟩ := h
    exact ⟨ε, hε, fun A hd hb => hA ε hε A ⟨hd, hb⟩⟩

/- ## Context: Sidon Sets and Bases -/

/-- Sidon sets have r(n) ≤ 1 for all n (bounded representation).
    Proof: the Sidon property ensures at most one pair (a, n-a) with
    a ≤ n-a, a ∈ A, n-a ∈ A for each n. -/
theorem sidon_bounded_rep (A : Set ℕ) (hsidon : ∀ a b c d : ℕ,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A → a ≤ b → c ≤ d →
    a + b = c + d → a = c ∧ b = d) :
    HasBoundedRep A := by
  use 1
  intro n
  unfold repFunction
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  obtain ⟨_, ha_A, hna_A, ha_le⟩ := ha
  obtain ⟨_, hb_A, hnb_A, hb_le⟩ := hb
  have heq : a + (n - a) = b + (n - b) := by omega
  exact (hsidon a (n - a) b (n - b) ha_A hna_A hb_A hnb_A ha_le hb_le heq).1

/-- For Sidon sets, the sumset A + A has density 0 (since |A ∩ [1,N]| ~ √N). -/
axiom sidon_density_zero (A : Set ℕ) (hsidon : ∀ a b c d : ℕ,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A → a ≤ b → c ≤ d →
    a + b = c + d → a = c ∧ b = d) :
    lowerDensity (sumSet A) = 0

/- ## Erdős–Turán Conjecture Connection -/

/-- Erdős–Turán conjecture (Problem #28): If A is an additive basis of order 2
    (i.e., every sufficiently large n ∈ A + A), then r(n) is unbounded.

    Problem #749 relaxes "basis" to "near-basis" (density close to 1). -/
axiom erdos_turan_conjecture_28 :
    ∀ A : Set ℕ, lowerDensity (sumSet A) = 1 → ¬ HasBoundedRep A

/- ## Upper Density Variant -/

/-- Similar question for upper density: does there exist A with
    upper density of A + A at least 1 - ε and bounded r(n)? -/
theorem erdos_749_upper_variant :
    (∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε ∧ HasBoundedRep A) ∨
    (∃ ε : ℝ, ε > 0 ∧ ∀ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε → ¬ HasBoundedRep A) := by
  by_cases h : ∀ ε : ℝ, ε > 0 → ∃ A : Set ℕ,
      upperDensity (sumSet A) ≥ 1 - ε ∧ HasBoundedRep A
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨ε, hε, hA⟩ := h
    exact ⟨ε, hε, fun A hd hb => hA ε hε A ⟨hd, hb⟩⟩
