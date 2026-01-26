/-!
# Erdős Problem 488: Divisibility Density in Multiples of Finite Sets

Let `A` be a finite set of positive integers and
`B = {n ≥ 1 : a | n for some a ∈ A}` (the set of multiples of
elements of `A`).

Is it true that for every `m > n ≥ max(A)`,
`|B ∩ [1,m]| / m < 2 · |B ∩ [1,n]| / n`?

The constant 2 is optimal: `A = {a}`, `n = 2a-1`, `m = 2a`.

Originally posed in Erdős (1961). The 1961 version had `a ∤ n`
(likely a typo), corrected to `a | n` in 1966.

*Reference:* [erdosproblems.com/488](https://www.erdosproblems.com/488)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Multiples set -/

/-- `B(A)`: the set of positive integers divisible by some element
of `A`. -/
def multiplesSet (A : Finset ℕ) : Set ℕ :=
    { n : ℕ | 1 ≤ n ∧ ∃ a ∈ A, a ∣ n }

/-! ## Counting function -/

/-- Count of elements of `B(A)` in `[1, N]`. -/
noncomputable def multiplesCount (A : Finset ℕ) (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).filter (fun n => ∃ a ∈ A, a ∣ n)).card

/-- The density ratio `|B ∩ [1,N]| / N`. -/
noncomputable def multiplesRatio (A : Finset ℕ) (N : ℕ) : ℚ :=
    (multiplesCount A N : ℚ) / (N : ℚ)

/-! ## Main conjecture -/

/-- Erdős Problem 488: For every finite set `A` of integers ≥ 2, and
every `m > n ≥ max(A)`, we have
`|B ∩ [1,m]| / m < 2 · |B ∩ [1,n]| / n`. -/
def ErdosProblem488 : Prop :=
    ∀ (A : Finset ℕ),
      A.Nonempty →
      (∀ a ∈ A, 2 ≤ a) →
        ∀ (n m : ℕ),
          A.max' A.nonempty ≤ n →
          n < m →
            multiplesRatio A m < 2 * multiplesRatio A n

/-! ## Optimality of constant 2 -/

/-- The constant 2 is optimal: for `A = {a}`, `n = 2a-1`, `m = 2a`,
the ratio approaches 2 as `a → ∞`. Specifically,
`|B ∩ [1,2a]| / (2a) = 1/a · ⌊2a/a⌋ / 2 = 1` while
`|B ∩ [1,2a-1]| / (2a-1)` is slightly more than `1/2`. -/
axiom constant_2_optimal :
    ∀ (ε : ℚ), 0 < ε →
      ∃ a : ℕ, 2 ≤ a ∧
        let A := ({a} : Finset ℕ)
        let n := 2 * a - 1
        let m := 2 * a
        2 - ε < multiplesRatio A m / multiplesRatio A n

/-! ## Inclusion–exclusion for multiples -/

/-- For a singleton `A = {a}`, `|B ∩ [1,N]| = ⌊N/a⌋`. -/
axiom singleton_multiplesCount (a N : ℕ) (ha : 1 ≤ a) :
    multiplesCount ({a} : Finset ℕ) N = N / a

/-- Monotonicity: `|B ∩ [1,M]| ≤ |B ∩ [1,N]|` when `M ≤ N`. -/
axiom multiplesCount_mono (A : Finset ℕ) (M N : ℕ) (h : M ≤ N) :
    multiplesCount A M ≤ multiplesCount A N

/-- Adding elements to `A` can only increase the multiples count. -/
axiom multiplesCount_subset (A B : Finset ℕ) (h : A ⊆ B) (N : ℕ) :
    multiplesCount A N ≤ multiplesCount B N

/-! ## Davenport's density -/

/-- The asymptotic density of `B(A)` exists and can be computed by
inclusion–exclusion over the elements of `A`. -/
axiom multiplesSet_density_exists (A : Finset ℕ) (hA : ∀ a ∈ A, 1 ≤ a) :
    ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ ε : ℚ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          |multiplesRatio A N - δ| < ε
