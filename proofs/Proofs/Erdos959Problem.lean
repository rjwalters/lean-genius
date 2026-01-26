/-!
# Erdős Problem 959: Distance Frequency Gaps in Planar Point Sets

Let `A ⊂ ℝ²` be a set of `n` points with distinct distances `d₁, ..., dₖ`.
Order by frequency: `f(d₁) ≥ f(d₂) ≥ ⋯ ≥ f(dₖ)`.

Estimate `max(f(d₁) - f(d₂))` over all `n`-point sets.

Clemen, Dumitrescu, and Liu showed:
- `max(f(d₁) - f(d₂)) ≫ n log n`
- For `1 ≤ r ≤ log n`, `max(f(dᵣ) - f(dᵣ₊₁)) ≫ n log n / r`

They conjecture `max(f(d₁) - f(d₂)) ≫ n^{1 + c / log log n}`.

*Reference:* [erdosproblems.com/959](https://www.erdosproblems.com/959)
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

/-! ## Distance frequency -/

/-- The distance multiset for a finite point set: count of pairs at each distance. -/
noncomputable def distFrequency (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
    ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card / 2

/-- The set of distinct distances realized by a point set. -/
noncomputable def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
    (A ×ˢ A).image (fun p => dist p.1 p.2) |>.filter (· > 0)

/-- The maximum distance frequency for a point set. -/
noncomputable def maxFrequency (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
    (distinctDistances A).sup (distFrequency A)

/-- The second-largest distance frequency. -/
noncomputable def secondFrequency (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
    ((distinctDistances A).image (distFrequency A) |>.erase (maxFrequency A)).sup id

/-- The frequency gap: difference between top two frequencies. -/
noncomputable def frequencyGap (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
    maxFrequency A - secondFrequency A

/-! ## Main conjecture -/

/-- Erdős Problem 959: For some constant C > 0, every sufficiently large n admits
an n-point set whose frequency gap is at least C · n · log n. -/
def ErdosProblem959 : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧ C * n * Real.log n ≤ (frequencyGap A : ℝ)

/-! ## Known lower bound -/

/-- Clemen–Dumitrescu–Liu: max(f(d₁) - f(d₂)) ≫ n log n. -/
axiom clemen_dumitrescu_liu (n : ℕ) (hn : 2 ≤ n) :
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      A.card = n ∧ ∃ C : ℝ, 0 < C ∧ C * n * Real.log n ≤ (frequencyGap A : ℝ)

/-! ## Stronger conjecture -/

/-- Conjectured: max gap grows as n^{1 + c/log log n} for some c > 0. -/
def ErdosProblem959_strong : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 3 ≤ n →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧
          (n : ℝ) ^ (1 + c / Real.log (Real.log n)) ≤ (frequencyGap A : ℝ)

/-! ## Basic properties -/

/-- The frequency gap is zero for sets with at most 2 points (at most one distance). -/
axiom frequencyGap_small (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    A.card ≤ 2 → frequencyGap A = 0

/-- The maximum frequency is at least the second frequency. -/
axiom maxFreq_ge_second (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    secondFrequency A ≤ maxFrequency A

/-- Distance frequency is symmetric. -/
axiom distFrequency_nonneg (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) :
    0 ≤ distFrequency A d
