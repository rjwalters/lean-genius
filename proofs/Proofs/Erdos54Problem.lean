/-!
# Erdős Problem 54: Ramsey 2-Complete Sets

A set `A ⊆ ℕ` is **Ramsey 2-complete** if for every 2-colouring of `A`,
all sufficiently large integers can be written as a monochromatic sum
of distinct elements from `A`.

**Bounds:**
- Lower: No Ramsey 2-complete `A` has `|A ∩ [1,N]| ≤ c(log N)²`
  (Burr–Erdős, 1985)
- Upper: There exists Ramsey 2-complete `A` with
  `|A ∩ [1,N]| ≪ (log N)²` (Conlon–Fox–Pham, 2021)

**Solved:** Conlon–Fox–Pham closed the gap up to constants.

*Reference:* [erdosproblems.com/54](https://www.erdosproblems.com/54)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-! ## Monochromatic subset sums -/

/-- A 2-colouring of a set `A`. -/
def Colouring2 (A : Set ℕ) := { n : ℕ // n ∈ A } → Bool

/-- The subset sums from a single colour class. -/
def monoSubsetSums (A : Set ℕ) (c : Colouring2 A) (colour : Bool) : Set ℕ :=
    { s | ∃ (S : Finset ℕ),
      (∀ n ∈ S, n ∈ A ∧ c ⟨n, ‹_›⟩ = colour) ∧
      S.sum id = s }

/-! ## Ramsey 2-completeness -/

/-- `A` is Ramsey 2-complete if for every 2-colouring, all large
integers are monochromatic subset sums. -/
def IsRamsey2Complete (A : Set ℕ) : Prop :=
    ∀ c : Colouring2 A,
      ∃ colour : Bool,
        ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
          n ∈ monoSubsetSums A c colour

/-! ## Counting function -/

/-- `|A ∩ {1,…,N}|`. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).filter (· ∈ A)).card

/-! ## Burr–Erdős lower bound -/

/-- Burr–Erdős (1985): No Ramsey 2-complete set can be too sparse.
There exists `c > 0` such that no Ramsey 2-complete `A` has
`|A ∩ [1,N]| ≤ c · (log N)²` for all large `N`. -/
axiom burr_erdos_lower :
    ∃ c : ℚ, 0 < c ∧
      ∀ A : Set ℕ, IsRamsey2Complete A →
        ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
          c * ((Nat.log 2 N : ℚ)) ^ 2 ≤ (countingFn A N : ℚ)

/-! ## Conlon–Fox–Pham upper bound -/

/-- Conlon–Fox–Pham (2021): There exists a Ramsey 2-complete set
with `|A ∩ [1,N]| ≪ (log N)²`. -/
axiom conlon_fox_pham :
    ∃ (A : Set ℕ), IsRamsey2Complete A ∧
      ∃ C : ℚ, 0 < C ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (countingFn A N : ℚ) ≤ C * ((Nat.log 2 N : ℚ)) ^ 2

/-! ## Main problem (solved) -/

/-- Erdős Problem 54 (solved): The minimum growth rate of a Ramsey
2-complete set is `Θ((log N)²)`. -/
def ErdosProblem54 : Prop :=
    (∃ c : ℚ, 0 < c ∧
      ∀ A : Set ℕ, IsRamsey2Complete A →
        ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
          c * ((Nat.log 2 N : ℚ)) ^ 2 ≤ (countingFn A N : ℚ)) ∧
    (∃ (A : Set ℕ), IsRamsey2Complete A ∧
      ∃ C : ℚ, 0 < C ∧
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (countingFn A N : ℚ) ≤ C * ((Nat.log 2 N : ℚ)) ^ 2)

/-! ## Earlier upper bound -/

/-- Burr–Erdős (1985): There exists a Ramsey 2-complete set with
`|A ∩ [1,N]| < (2 log₂ N)³`. This was improved by Conlon–Fox–Pham. -/
axiom burr_erdos_upper :
    ∃ (A : Set ℕ), IsRamsey2Complete A ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (countingFn A N : ℚ) < (2 * (Nat.log 2 N : ℚ)) ^ 3
