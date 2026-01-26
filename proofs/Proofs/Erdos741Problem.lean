/-!
# Erdős Problem 741: Splitting Sumsets with Positive Density

**Part 1 (Density splitting):** If `A ⊆ ℕ` is such that `A + A` has positive
upper density, can one always decompose `A = A₁ ⊔ A₂` such that both
`A₁ + A₁` and `A₂ + A₂` have positive upper density?

**Part 2 (Basis splitting):** Is there a basis `A` of order 2 such that for
every decomposition `A = A₁ ⊔ A₂`, the sumsets `A₁ + A₁` and `A₂ + A₂`
cannot both have bounded gaps (be syndetic)?

This is a problem of Burr and Erdős. Erdős believed he could construct a
basis answering Part 2 affirmatively but "could never quite finish the proof."

*Reference:* [erdosproblems.com/741](https://www.erdosproblems.com/741)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Set Filter

/-! ## Density and sumset definitions -/

/-- Upper density of a set `A ⊆ ℕ`: `limsup |A ∩ [0,n]| / (n+1)`. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
    atTop.limsup (fun n => ((A ∩ Set.Iic n).ncard : ℝ) / (n + 1 : ℝ))

/-- `HasPosDensity A` means `A` has positive upper density. -/
def HasPosDensity (A : Set ℕ) : Prop :=
    0 < upperDensity A

/-- The sumset `A + B = { a + b : a ∈ A, b ∈ B }`. -/
def sumset (A B : Set ℕ) : Set ℕ :=
    { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

/-- `A` is a basis of order 2 if every sufficiently large natural number
is in `A + A`. -/
def IsBasisOrder2 (A : Set ℕ) : Prop :=
    ∀ᶠ n in atTop, n ∈ sumset A A

/-- A set `S ⊆ ℕ` is syndetic (has bounded gaps) if there exists `g` such that
every interval `[n, n+g]` intersects `S`. -/
def IsSyndetic (S : Set ℕ) : Prop :=
    ∃ g : ℕ, ∀ n : ℕ, ∃ m ∈ S, n ≤ m ∧ m ≤ n + g

/-! ## Main conjectures -/

/-- Part 1 (Density splitting): If `A + A` has positive density, can `A` be split
into `A₁ ⊔ A₂` with both `A₁ + A₁` and `A₂ + A₂` having positive density? -/
def ErdosProblem741_density : Prop :=
    ∀ A : Set ℕ, HasPosDensity (sumset A A) →
      ∃ A₁ A₂ : Set ℕ, A = A₁ ∪ A₂ ∧ Disjoint A₁ A₂ ∧
        HasPosDensity (sumset A₁ A₁) ∧ HasPosDensity (sumset A₂ A₂)

/-- Part 2 (Basis splitting): Does there exist a basis of order 2 such that
no partition `A = A₁ ⊔ A₂` makes both `A₁ + A₁` and `A₂ + A₂` syndetic? -/
def ErdosProblem741_basis : Prop :=
    ∃ A : Set ℕ, IsBasisOrder2 A ∧
      ∀ A₁ A₂ : Set ℕ, A = A₁ ∪ A₂ → Disjoint A₁ A₂ →
        ¬(IsSyndetic (sumset A₁ A₁) ∧ IsSyndetic (sumset A₂ A₂))

/-! ## Basic properties -/

/-- The sumset is commutative. -/
theorem sumset_comm (A B : Set ℕ) : sumset A B = sumset B A := by
  ext n; constructor
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨b, hb, a, ha, by omega⟩
  · rintro ⟨b, hb, a, ha, rfl⟩; exact ⟨a, ha, b, hb, by omega⟩

/-- The empty set has zero density. -/
axiom density_empty : upperDensity ∅ = 0

/-- The empty sumset has zero density. -/
theorem empty_sumset : sumset ∅ (∅ : Set ℕ) = ∅ := by
  ext n; simp [sumset]

/-- If `A ⊆ B`, then `sumset A A ⊆ sumset B B`. -/
theorem sumset_mono {A B : Set ℕ} (h : A ⊆ B) : sumset A A ⊆ sumset B B := by
  intro n ⟨a, ha, b, hb, hn⟩
  exact ⟨a, h ha, b, h hb, hn⟩

/-- A trivial partition always exists: `A = A ∪ ∅`. -/
theorem trivial_partition (A : Set ℕ) : A = A ∪ ∅ ∧ Disjoint A (∅ : Set ℕ) := by
  exact ⟨by simp, disjoint_bot_right⟩

/-- Every finite set has zero upper density. -/
axiom density_finite (A : Set ℕ) (hA : A.Finite) : upperDensity A = 0

/-- Density is monotone: `A ⊆ B` implies `upperDensity A ≤ upperDensity B`. -/
axiom density_mono {A B : Set ℕ} (h : A ⊆ B) : upperDensity A ≤ upperDensity B

/-- `ℕ` has density 1. -/
axiom density_univ : upperDensity Set.univ = 1
