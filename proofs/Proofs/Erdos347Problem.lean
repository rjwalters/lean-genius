/-!
# Erdős Problem 347: Complete Sequences with Ratio Tending to 2

Is there a sequence `A = {a₁ ≤ a₂ ≤ ⋯}` of positive integers with
`lim a_{n+1}/a_n = 2` such that for every cofinite subsequence `A'`,
the set of subset sums `P(A')` has density 1?

**Solved** affirmatively (ebarschkis, based on ideas by Tao and
van Doorn). A formal Lean proof exists.

*Reference:* [erdosproblems.com/347](https://www.erdosproblems.com/347)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

/-! ## Subset sums -/

/-- The set of finite subset sums of a set `A ⊆ ℕ`. -/
def subsetSums (A : Set ℕ) : Set ℕ :=
    { s | ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧ S.sum id = s }

/-! ## Asymptotic density -/

/-- The counting function `|S ∩ {1,…,N}|`. -/
noncomputable def countIn (S : Set ℕ) (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).filter (· ∈ S)).card

/-- A set `S ⊆ ℕ` has density `δ` if `|S ∩ {1,…,N}| / N → δ`. -/
def HasDensity (S : Set ℕ) (δ : ℚ) : Prop :=
    ∀ ε : ℚ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        |((countIn S N : ℚ) / (N : ℚ)) - δ| < ε

/-! ## Monotone sequences with ratio limit -/

/-- A sequence `a : ℕ → ℕ` is monotone nondecreasing. -/
def IsMonotone (a : ℕ → ℕ) : Prop :=
    ∀ m n : ℕ, m ≤ n → a m ≤ a n

/-- The ratio `a(n+1)/a(n)` tends to `r`. -/
def HasRatioLimit (a : ℕ → ℕ) (r : ℚ) : Prop :=
    ∀ ε : ℚ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        0 < a n →
          |((a (n + 1) : ℚ) / (a n : ℚ)) - r| < ε

/-! ## Cofinite subsequences -/

/-- A cofinite subsequence: the range of `a ∘ ι` where `ι` omits only
finitely many indices. -/
def IsCofiniteSubseq (a ι : ℕ → ℕ) : Prop :=
    StrictMono ι ∧ (Set.range ι)ᶜ.Finite

/-- The image of a cofinite subsequence. -/
def cofiniteImage (a ι : ℕ → ℕ) : Set ℕ :=
    Set.range (a ∘ ι)

/-! ## Main conjecture (solved) -/

/-- Erdős Problem 347 (solved): There exists a monotone sequence with
ratio limit 2 such that every cofinite subsequence has subset sums
of density 1. -/
def ErdosProblem347 : Prop :=
    ∃ (a : ℕ → ℕ),
      IsMonotone a ∧
      HasRatioLimit a 2 ∧
      ∀ (ι : ℕ → ℕ), IsCofiniteSubseq a ι →
        HasDensity (subsetSums (cofiniteImage a ι)) 1

/-- The answer to Erdős Problem 347 is affirmative. -/
axiom erdos347_affirmative : ErdosProblem347

/-! ## Basic properties -/

/-- The empty subset sum is 0: `0 ∈ P(A)` for any `A`. -/
axiom zero_mem_subsetSums (A : Set ℕ) :
    0 ∈ subsetSums A

/-- Subset sums are closed under adding elements of `A`. -/
axiom subsetSums_add (A : Set ℕ) (s : ℕ) (a : ℕ) :
    s ∈ subsetSums A → a ∈ A →
      s + a ∈ subsetSums A

/-- If `A ⊆ B`, then `P(A) ⊆ P(B)`. -/
axiom subsetSums_mono (A B : Set ℕ) (h : A ⊆ B) :
    subsetSums A ⊆ subsetSums B
