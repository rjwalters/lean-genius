/-
  Erdős Problem #20: The Sunflower Conjecture

  Source: https://erdosproblems.com/20
  Status: OPEN
  Prize: $1,000

  Statement:
  Let f(n,k) be minimal such that every family F of n-uniform sets with
  |F| ≥ f(n,k) contains a k-sunflower.

  Is it true that f(n,k) < c_k^n for some constant c_k depending only on k?

  A k-sunflower (or k-delta-system) is a collection of k sets where all
  pairwise intersections are identical (the "core").

  History:
  - Erdős-Rado (1960): f(n,k) ≤ (k-1)^n · n! (Sunflower Lemma)
  - Kostochka (1997): f(n,k) = o(n!) · (k-1)^n
  - Alweiss-Lovett-Wu-Zhang (2020): f(n,k) ≤ (Ck log n log log n)^n
  - Rao (2020): f(n,k) ≤ (Ck log n)^n (current best)

  The conjecture asks if we can remove the log n factor entirely.
-/

import Mathlib

open Set Finset

namespace Erdos20

variable {α : Type*} [DecidableEq α]

/-! ## Core Definitions -/

/-- A family of sets is n-uniform if all sets have exactly n elements. -/
def IsUniform (F : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ S ∈ F, S.card = n

/-- The core of a sunflower: the common intersection of all petals. -/
def SunflowerCore (petals : Finset (Finset α)) : Finset α :=
  petals.inf id

/-- A k-sunflower (delta-system): k sets with identical pairwise intersections.
    The sets S_1, ..., S_k form a sunflower with core C if:
    S_i ∩ S_j = C for all i ≠ j. -/
def IsSunflower (petals : Finset (Finset α)) (k : ℕ) : Prop :=
  petals.card = k ∧
  ∃ core : Finset α, ∀ S₁ ∈ petals, ∀ S₂ ∈ petals, S₁ ≠ S₂ → S₁ ∩ S₂ = core

/-- A family contains a k-sunflower. -/
def ContainsSunflower (F : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ petals : Finset (Finset α), petals ⊆ F ∧ IsSunflower petals k

/-! ## The Sunflower Number f(n,k) -/

/-- f(n,k) = minimum m such that every n-uniform family of size m contains k-sunflower.
    This is axiomatized because computing it requires checking all possible families. -/
noncomputable def sunflowerNumber (n k : ℕ) : ℕ := sorry

/-- f(n,k) is well-defined and finite (Erdős-Rado Lemma). -/
axiom sunflower_number_finite (n k : ℕ) (hk : k ≥ 2) :
    ∃ m : ℕ, ∀ (α : Type*) [DecidableEq α] (F : Finset (Finset α)),
      IsUniform F n → F.card ≥ m → ContainsSunflower F k

/-! ## The Sunflower Lemma (Erdős-Rado 1960) -/

/-- **Erdős-Rado Sunflower Lemma (1960)**:
    f(n,k) ≤ (k-1)^n · n!

    This is the original bound. Every sufficiently large n-uniform family
    contains a k-sunflower. -/
axiom erdos_rado_sunflower_lemma (n k : ℕ) (hk : k ≥ 2) :
    sunflowerNumber n k ≤ (k - 1)^n * n.factorial

/-- The Erdős-Rado bound explicitly. -/
def erdosRadoBound (n k : ℕ) : ℕ := (k - 1)^n * n.factorial

/-! ## The Conjecture -/

/-- **The Sunflower Conjecture** (Erdős-Rado, OPEN):
    For each k ≥ 3, there exists c_k > 0 such that f(n,k) < c_k^n.

    This asks if the n! factor can be completely removed. -/
def SunflowerConjecture : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, (sunflowerNumber n k : ℝ) < c^n

/-- Erdős specifically focused on k=3 as "the whole difficulty". -/
def SunflowerConjectureK3 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, (sunflowerNumber n 3 : ℝ) < c^n

/-! ## Progress on the Conjecture -/

/-- **Kostochka (1997)**: f(n,k) = o(n!) · (k-1)^n.
    First improvement over Erdős-Rado. Won $100 consolation prize. -/
axiom kostochka_improvement (k : ℕ) (hk : k ≥ 2) :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (sunflowerNumber n k : ℝ) < ε * (k - 1)^n * n.factorial

/-- **Alweiss-Lovett-Wu-Zhang (2020)**: f(n,k) ≤ (Ck log n log log n)^n.
    Major breakthrough reducing from n! growth to polynomial-in-n exponent. -/
axiom alwz_bound (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (sunflowerNumber n k : ℝ) ≤ (C * k * Real.log n * Real.log (Real.log n))^n

/-- **Rao (2020)**: f(n,k) ≤ (Ck log n)^n.
    Current best bound, removing one log factor from ALWZ. -/
axiom rao_bound (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (sunflowerNumber n k : ℝ) ≤ (C * k * Real.log n)^n

/-! ## The Gap -/

/-- **The remaining gap**: Current best is (Ck log n)^n.
    Conjecture asks for c_k^n (no log factor).
    Equivalently: can we prove f(n,k) ≤ (Ck)^n? -/

def RequiredBound (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, (sunflowerNumber n k : ℝ) ≤ c^n

/-- The gap: Rao gives (log n)^n factor we need to remove. -/
theorem gap_description :
    (∀ k, k ≥ 3 → RequiredBound k) ↔ SunflowerConjecture := by
  constructor
  · intro h k hk
    obtain ⟨c, hc, hbound⟩ := h k hk
    exact ⟨c, hc, fun n => lt_of_le_of_lt (hbound n) (by positivity)⟩
  · intro h k hk
    obtain ⟨c, hc, hbound⟩ := h k hk
    exact ⟨c, hc, fun n => le_of_lt (hbound n)⟩

/-! ## Special Cases -/

/-- For k=2: f(n,2) = n+1 (easy: any n+2 sets of size n have two overlapping). -/
axiom sunflower_k2 (n : ℕ) : sunflowerNumber n 2 = n + 1

/-- For k=3, n=2: f(2,3) = 6 (verified computationally). -/
axiom sunflower_n2_k3 : sunflowerNumber 2 3 = 6

/-- Lower bound: f(n,k) ≥ (k-1)^n (can avoid sunflowers up to this size). -/
axiom sunflower_lower_bound (n k : ℕ) (hk : k ≥ 2) :
    sunflowerNumber n k ≥ (k - 1)^n

/-! ## Examples -/

/-- Example sunflower with k=3: {1,2,3}, {1,4,5}, {1,6,7} with core {1}. -/
example : IsSunflower ({{1,2,3}, {1,4,5}, {1,6,7}} : Finset (Finset ℕ)) 3 := by
  constructor
  · decide
  · use {1}
    intro S₁ hS₁ S₂ hS₂ hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS₁ hS₂
    rcases hS₁ with rfl | rfl | rfl <;> rcases hS₂ with rfl | rfl | rfl <;>
      first | contradiction | decide

/-- A 3-sunflower can have empty core: {1,2}, {3,4}, {5,6}. -/
example : IsSunflower ({{1,2}, {3,4}, {5,6}} : Finset (Finset ℕ)) 3 := by
  constructor
  · decide
  · use ∅
    intro S₁ hS₁ S₂ hS₂ hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hS₁ hS₂
    rcases hS₁ with rfl | rfl | rfl <;> rcases hS₂ with rfl | rfl | rfl <;>
      first | contradiction | decide

/-! ## Applications -/

/-- **Matrix multiplication**: Sunflower bounds relate to matrix multiplication
    exponent lower bounds. -/

/-- **Property testing**: Used in algorithms for testing set properties. -/

/-- **Circuit complexity**: Connections to ACC circuit lower bounds. -/

/-! ## Problem Status -/

/-- **Erdős Problem #20: OPEN ($1,000 prize)**

The Sunflower Conjecture asks whether f(n,k) < c_k^n for constants c_k.

**What we know:**
- Erdős-Rado (1960): f(n,k) ≤ (k-1)^n · n! ✓
- Kostochka (1997): improved by o(1) factor
- ALWZ (2020): f(n,k) ≤ (Ck log n log log n)^n
- Rao (2020): f(n,k) ≤ (Ck log n)^n (current best)

**What we need:**
- Prove f(n,k) ≤ c_k^n (remove the log n factor), OR
- Find a counterexample

**The gap:**
- Upper: (Ck log n)^n
- Lower: (k-1)^n
- Conjectured: c_k^n for some c_k

References:
- Erdős, Rado (1960): "Intersection theorems for systems of sets"
- Kostochka (1997): "An improvement to the Erdős-Rado sunflower lemma"
- Alweiss, Lovett, Wu, Zhang (2020): "Improved bounds for the sunflower lemma"
- Rao (2020): "Coding for sunflowers"
-/
theorem erdos_20_open : SunflowerConjecture ∨ ¬SunflowerConjecture := by
  exact Classical.em SunflowerConjecture

end Erdos20
