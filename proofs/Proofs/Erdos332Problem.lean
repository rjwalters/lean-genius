/-!
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

/-! ## Difference set D(A) -/

/-- The difference set `D(A)`: integers that appear infinitely often
as `a₁ - a₂` with `a₁, a₂ ∈ A`. -/
def diffSet (A : Set ℕ) : Set ℤ :=
    { d : ℤ | Set.Infinite
      { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = d } }

/-! ## Bounded gaps (syndetic sets) -/

/-- A set `S ⊆ ℤ` has bounded gaps (is syndetic) if there exists
`M > 0` such that every interval of length `M` contains an element
of `S`. -/
def HasBoundedGaps (S : Set ℤ) : Prop :=
    ∃ M : ℕ, 0 < M ∧
      ∀ z : ℤ, ∃ s ∈ S, z ≤ s ∧ s < z + (M : ℤ)

/-! ## Density conditions -/

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

/-! ## Known results -/

/-- Positive upper density implies `D(A)` has bounded gaps. This is
the known sufficient condition due to Prikry. -/
axiom positive_density_bounded_gaps (A : Set ℕ) :
    HasPositiveUpperDensity A → HasBoundedGaps (diffSet A)

/-- Positive upper density implies `D(A)` has positive density itself. -/
axiom positive_density_diffset_dense (A : Set ℕ) :
    HasPositiveUpperDensity A →
      HasPositiveUpperDensity { n : ℕ | (n : ℤ) ∈ diffSet A }

/-- The difference set is symmetric: `d ∈ D(A)` iff `-d ∈ D(A)`. -/
axiom diffSet_symm (A : Set ℕ) (d : ℤ) :
    d ∈ diffSet A ↔ -d ∈ diffSet A

/-- Zero is always in `D(A)` when `A` is infinite. -/
axiom zero_mem_diffSet (A : Set ℕ) (hA : Set.Infinite A) :
    (0 : ℤ) ∈ diffSet A

/-! ## Main problem -/

/-- Erdős Problem 332: What conditions on `A ⊆ ℕ` are sufficient to
ensure `D(A)` has bounded gaps?

The known sufficient condition is positive upper density. The open
question asks for the weakest possible condition. -/
def ErdosProblem332 : Prop :=
    ∀ (P : Set ℕ → Prop),
      (∀ A : Set ℕ, P A → HasBoundedGaps (diffSet A)) →
        ∀ A : Set ℕ, HasPositiveUpperDensity A → P A

/-! ## Related questions -/

/-- Does `∑_{d ∈ D(A)} 1/d = ∞` when `A` has positive upper density? -/
axiom diffSet_harmonic_diverges (A : Set ℕ) :
    HasPositiveUpperDensity A →
      ∀ B : ℚ, ∃ (S : Finset ℕ),
        (∀ n ∈ S, (n : ℤ) ∈ diffSet A) ∧
          B ≤ S.sum (fun n => (1 : ℚ) / (n : ℚ))
