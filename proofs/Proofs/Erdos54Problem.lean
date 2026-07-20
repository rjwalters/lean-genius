/-
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

open scoped Classical

/- ## Monochromatic subset sums -/

/-- A 2-colouring of a set `A`. -/
def Colouring2 (A : Set ℕ) := { n : ℕ // n ∈ A } → Bool

/-- The subset sums from a single colour class. -/
def monoSubsetSums (A : Set ℕ) (c : Colouring2 A) (colour : Bool) : Set ℕ :=
    { s | ∃ (S : Finset ℕ),
      (∀ n ∈ S, ∃ hn : n ∈ A, c ⟨n, hn⟩ = colour) ∧
      S.sum id = s }

/- ## Ramsey 2-completeness -/

/-- `A` is Ramsey 2-complete if for every 2-colouring, all large
integers are monochromatic subset sums. -/
def IsRamsey2Complete (A : Set ℕ) : Prop :=
    ∀ c : Colouring2 A,
      ∃ colour : Bool,
        ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
          n ∈ monoSubsetSums A c colour

/- ## Counting function -/

/-- `|A ∩ {1,…,N}|`. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).filter (· ∈ A)).card

/- ## Burr–Erdős lower bound -/

/-  Burr–Erdős (1985): No Ramsey 2-complete set can be too sparse.
There exists `c > 0` such that no Ramsey 2-complete `A` has
`|A ∩ [1,N]| ≤ c · (log N)²` for all large `N`. -/
/- ## Conlon–Fox–Pham upper bound -/

/-  Conlon–Fox–Pham (2021): There exists a Ramsey 2-complete set
with `|A ∩ [1,N]| ≪ (log N)²`. -/
/- ## Main problem (solved) -/

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

/- ## Earlier upper bound -/

/- Burr–Erdős (1985): There exists a Ramsey 2-complete set with
`|A ∩ [1,N]| < (2 log₂ N)³`. This was improved by Conlon–Fox–Pham. -/

/- ## Foundational lemmas (axiom-free)

The two deep quantitative bounds above (Burr–Erdős lower bound, Conlon–Fox–Pham
optimal construction) are documented in the header prose only — they are not
formalised. What follows are the machine-checkable structural facts about the
definitions, proved with no axioms and no `sorry`. -/

/-- `0` is always a monochromatic subset sum: the empty subset is (vacuously)
    monochromatic and sums to `0`. -/
theorem zero_mem_monoSubsetSums (A : Set ℕ) (c : Colouring2 A) (colour : Bool) :
    0 ∈ monoSubsetSums A c colour :=
  ⟨∅, by simp, by simp⟩

/-- A single element of `A` carrying the given colour is itself a monochromatic
    subset sum (via the singleton subset `{n}`). -/
theorem mem_monoSubsetSums_of_mem (A : Set ℕ) (c : Colouring2 A) (colour : Bool)
    {n : ℕ} (hn : n ∈ A) (hc : c ⟨n, hn⟩ = colour) :
    n ∈ monoSubsetSums A c colour := by
  refine ⟨{n}, ?_, by simp⟩
  intro m hm
  rw [Finset.mem_singleton] at hm
  subst hm
  exact ⟨hn, hc⟩

/-- The counting function never exceeds the length of the window: at most `N`
    elements of `A` lie in `{1, …, N}`. -/
theorem countingFn_le (A : Set ℕ) (N : ℕ) : countingFn A N ≤ N := by
  unfold countingFn
  calc ((Finset.Icc 1 N).filter (· ∈ A)).card
      ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
    _ = N := by rw [Nat.card_Icc]; omega

/-- The counting function is monotone in the window size. -/
theorem countingFn_mono (A : Set ℕ) {M N : ℕ} (h : M ≤ N) :
    countingFn A M ≤ countingFn A N := by
  unfold countingFn
  exact Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right h))
