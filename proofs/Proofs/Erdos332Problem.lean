/-
# Erdős Problem 332: Difference Sets and Bounded Gaps

Let `A ⊆ ℕ` and define `D(A)` as the set of integers that occur
infinitely often as `a₁ - a₂` with `a₁, a₂ ∈ A`.

What conditions on `A` are sufficient to ensure `D(A)` has bounded gaps?

A sufficient condition is that `A` has positive upper density (Prikry,
Tijdeman, Stewart).

*Reference:* [erdosproblems.com/332](https://www.erdosproblems.com/332)
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Set
open scoped Classical

/- ## Difference set D(A) -/

/-- The difference set `D(A)`: integers that appear infinitely often
as `a₁ - a₂` with `a₁, a₂ ∈ A`. -/
def diffSet (A : Set ℕ) : Set ℤ :=
    { d : ℤ | Set.Infinite
      { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = d } }

/- ## Bounded gaps (syndetic sets) -/

/-- A set `S ⊆ ℤ` has bounded gaps (is syndetic) if there exists
`M > 0` such that every interval of length `M` contains an element
of `S`. -/
def HasBoundedGaps (S : Set ℤ) : Prop :=
    ∃ M : ℕ, 0 < M ∧
      ∀ z : ℤ, ∃ s ∈ S, z ≤ s ∧ s < z + (M : ℤ)

/- ## Density conditions -/

/-- The counting function: `|A ∩ {1,…,N}|`. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
    (Finset.Icc 1 N |>.filter (· ∈ A)).card

/-- `A` has positive upper density: `limsup |A ∩ {1,…,N}| / N > 0`. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
    ∃ δ : ℚ, 0 < δ ∧
      ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
        δ * (N : ℚ) ≤ (countingFn A N : ℚ)

/-- `A` has positive lower density: `liminf |A ∩ {1,…,N}| / N > 0`. -/
def HasPositiveLowerDensity (A : Set ℕ) : Prop :=
    ∃ δ : ℚ, 0 < δ ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        δ * (N : ℚ) ≤ (countingFn A N : ℚ)

/- ## Known results -/

/-- Positive upper density implies `D(A)` has bounded gaps. This is
the known sufficient condition due to Prikry. -/
axiom positive_density_bounded_gaps (A : Set ℕ) :
    HasPositiveUpperDensity A → HasBoundedGaps (diffSet A)

/-- Positive upper density implies `D(A)` has positive density itself. -/
axiom positive_density_diffset_dense (A : Set ℕ) :
    HasPositiveUpperDensity A →
      HasPositiveUpperDensity { n : ℕ | (n : ℤ) ∈ diffSet A }

/-- The difference set is symmetric: `d ∈ D(A)` iff `-d ∈ D(A)`.
    Proof: the swap map `(a₁, a₂) ↦ (a₂, a₁)` sends pairs with
    difference `d` to pairs with difference `-d`, preserving membership. -/
theorem diffSet_symm (A : Set ℕ) (d : ℤ) :
    d ∈ diffSet A ↔ -d ∈ diffSet A := by
  suffices h : ∀ e : ℤ, e ∈ diffSet A → -e ∈ diffSet A from
    ⟨h d, fun hnd => neg_neg d ▸ h (-d) hnd⟩
  intro e he
  simp only [diffSet, Set.mem_setOf_eq] at he ⊢
  -- Set.Infinite = ¬ Set.Finite, so introduce S_{-e}.Finite and derive contradiction
  intro hfin
  -- S_e ⊆ Prod.swap '' S_{-e}, so S_e.Finite follows from S_{-e}.Finite
  exact he ((hfin.image Prod.swap).subset
    (fun ⟨a₁, a₂⟩ ⟨ha₁, ha₂, hd⟩ =>
      ⟨⟨a₂, a₁⟩, ⟨ha₂, ha₁, by push_cast at hd ⊢; linarith⟩, by simp [Prod.swap]⟩))

/-- Zero is always in `D(A)` when `A` is infinite.
    Proof: for each `a ∈ A`, the pair `(a, a)` has difference `0`.
    Since `A` is infinite, there are infinitely many such pairs. -/
theorem zero_mem_diffSet (A : Set ℕ) (hA : Set.Infinite A) :
    (0 : ℤ) ∈ diffSet A := by
  simp only [diffSet, Set.mem_setOf_eq]
  -- Set.Infinite = ¬ Set.Finite, so introduce S₀.Finite and derive contradiction
  intro hfin
  -- A ⊆ Prod.fst '' S₀, so A.Finite follows from S₀.Finite
  exact hA ((hfin.image Prod.fst).subset
    (fun a ha => ⟨⟨a, a⟩, ⟨ha, ha, by push_cast; ring⟩, rfl⟩))

/- ## Main problem -/

/-- Erdős Problem 332: What conditions on `A ⊆ ℕ` are sufficient to
ensure `D(A)` has bounded gaps?

The known sufficient condition is positive upper density. The open
question asks for the weakest possible condition. -/
def ErdosProblem332 : Prop :=
    ∀ (P : Set ℕ → Prop),
      (∀ A : Set ℕ, P A → HasBoundedGaps (diffSet A)) →
        ∀ A : Set ℕ, HasPositiveUpperDensity A → P A

/- ## Related questions -/

/-- Does `∑_{d ∈ D(A)} 1/d = ∞` when `A` has positive upper density? -/
axiom diffSet_harmonic_diverges (A : Set ℕ) :
    HasPositiveUpperDensity A →
      ∀ B : ℚ, ∃ (S : Finset ℕ),
        (∀ n ∈ S, (n : ℤ) ∈ diffSet A) ∧
          B ≤ S.sum (fun n => (1 : ℚ) / (n : ℚ))
