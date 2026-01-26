/-!
# Erdős Problem 361: Largest Non-Representing Subsets

Let `c > 0` and `n` be a large integer. What is the size of the largest set
`A ⊆ {1, ..., ⌊cn⌋}` such that `n` is not a sum of a subset of `A`?

Does this maximum size depend on `n` in an irregular way?

*Source:* Erdős–Graham [ErGr80, p. 59]

*Reference:* [erdosproblems.com/361](https://www.erdosproblems.com/361)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

open Finset Filter Asymptotics

/-! ## Definitions -/

/-- `IsSubsetSum A n` holds when `n` can be expressed as a sum of elements from a
subset of `A`. -/
def IsSubsetSum (A : Finset ℕ) (n : ℕ) : Prop :=
    ∃ B : Finset ℕ, B ⊆ A ∧ B.sum id = n

/-- `NonRepresenting A n` means `n` is NOT a sum of any subset of `A`. -/
def NonRepresenting (A : Finset ℕ) (n : ℕ) : Prop :=
    ¬IsSubsetSum A n

/-- `maxNonReprSize c n` is the maximum cardinality of `A ⊆ {1,...,⌊cn⌋}` such
that `n` is not a sum of a subset of `A`. -/
noncomputable def maxNonReprSize (c : ℝ) (n : ℕ) : ℕ :=
    ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B => NonRepresenting B n)).sup Finset.card

/-! ## Main conjecture -/

/-- Erdős Problem 361: What is the asymptotic growth of `maxNonReprSize c n`?
Does it depend on `n` irregularly? The question asks for the growth rate
and whether the function oscillates. -/
def ErdosProblem361 : Prop :=
    ∀ c : ℝ, 0 < c →
      ¬Monotone (fun n => maxNonReprSize c n)

/-- A weaker form: `maxNonReprSize c n` is unbounded as `n → ∞`. -/
def MaxNonReprUnbounded : Prop :=
    ∀ c : ℝ, 0 < c → Tendsto (fun n => (maxNonReprSize c n : ℝ)) atTop atTop

/-! ## Asymptotic questions from formal-conjectures -/

/-- Is there an asymptotic upper bound `maxNonReprSize c n = O(f(n))` for some `f`? -/
axiom maxNonRepr_bigO_bound (c : ℝ) (hc : 0 < c) :
    ∃ f : ℕ → ℝ, IsBigO atTop (fun n => (maxNonReprSize c n : ℝ)) f

/-- The growth rate might be `Θ(√n)` — this is a plausible conjecture. -/
axiom maxNonRepr_plausible_theta (c : ℝ) (hc : 0 < c) :
    IsTheta atTop (fun n => (maxNonReprSize c n : ℝ)) (fun n => Real.sqrt n)

/-! ## Basic properties -/

/-- The empty set is always non-representing (for `n > 0`). -/
axiom nonRepresenting_empty (n : ℕ) (hn : 0 < n) : NonRepresenting ∅ n

/-- Any subset of a non-representing set is also non-representing. -/
axiom nonRepresenting_subset {A B : Finset ℕ} {n : ℕ}
    (h : A ⊆ B) (hB : NonRepresenting B n) : NonRepresenting A n

/-- If `n > ⌊cn⌋ · (⌊cn⌋ + 1) / 2`, then every subset sums to less than `n`,
so `maxNonReprSize c n` equals the full set size. -/
axiom maxNonRepr_large_n (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ n in atTop, maxNonReprSize c n = ⌊c * n⌋₊

/-- `maxNonReprSize c n ≥ 1` for `n ≥ 2` and `c ≥ 1`, since `{n-1}` doesn't sum to `n`. -/
axiom maxNonRepr_ge_one (c : ℝ) (hc : 1 ≤ c) (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ maxNonReprSize c n

/-- For the singleton `{1}`, it's non-representing for `n ≥ 2`. -/
axiom singleton_one_nonRepr (n : ℕ) (hn : 2 ≤ n) : NonRepresenting {1} n
