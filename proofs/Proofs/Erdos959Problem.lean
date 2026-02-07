import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-
Erdős Problem 959: Distance Frequency Gaps in Planar Point Sets

Let A ⊂ ℝ² be a set of n points with distinct distances d₁, ..., dₖ.
Order by frequency: f(d₁) ≥ f(d₂) ≥ ⋯ ≥ f(dₖ).

Estimate max(f(d₁) - f(d₂)) over all n-point sets.

Clemen, Dumitrescu, and Liu (2025) showed:
- max(f(d₁) - f(d₂)) ≫ n log n
- For 1 ≤ r ≤ log n, max(f(dᵣ) - f(dᵣ₊₁)) ≫ n log n / r

They conjecture max(f(d₁) - f(d₂)) ≫ n^{1 + c / log log n}.

Reference: erdosproblems.com/959
-/

open Finset

-- ## Distance frequency

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

-- ## Main conjecture

/-- Erdős Problem 959: For some constant C > 0, every sufficiently large n admits
an n-point set whose frequency gap is at least C · n · log n. -/
def ErdosProblem959 : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧ C * n * Real.log n ≤ (frequencyGap A : ℝ)

-- ## Known lower bound

/-- Clemen-Dumitrescu-Liu (2025): max(f(d₁) - f(d₂)) ≫ n log n. -/
axiom clemen_dumitrescu_liu (n : ℕ) (hn : 2 ≤ n) :
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      A.card = n ∧ ∃ C : ℝ, 0 < C ∧ C * n * Real.log n ≤ (frequencyGap A : ℝ)

-- ## Stronger conjecture

/-- Conjectured: max gap grows as n^{1 + c/log log n} for some c > 0. -/
def ErdosProblem959_strong : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 3 ≤ n →
      ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        A.card = n ∧
          (n : ℝ) ^ (1 + c / Real.log (Real.log n)) ≤ (frequencyGap A : ℝ)

-- ## Structural properties

/-- Distance frequency is always non-negative (trivially true for ℕ). -/
theorem distFrequency_nonneg (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) :
    0 ≤ distFrequency A d :=
  Nat.zero_le _

/-- The maximum frequency is at least the second frequency. -/
theorem maxFreq_ge_second (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    secondFrequency A ≤ maxFrequency A := by
  sorry

/-- The frequency gap for the empty set is zero. -/
theorem frequencyGap_empty : frequencyGap ∅ = 0 := by
  unfold frequencyGap maxFrequency secondFrequency distinctDistances
  simp [Finset.product_empty]

-- ## Generalized frequency gap

/-- The r-th frequency gap: difference between the r-th and (r+1)-th most
    frequent distances. -/
noncomputable def frequencyGapR (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (r : ℕ) : ℕ :=
  let freqs := ((distinctDistances A).image (distFrequency A)).sort (· ≥ ·)
  if hr : r < freqs.length ∧ r + 1 < freqs.length then
    freqs.get ⟨r, hr.1⟩ - freqs.get ⟨r + 1, hr.2⟩
  else 0

/-- CDL generalized: for 1 ≤ r ≤ log n, there exists an n-point set with
    f(dᵣ) - f(dᵣ₊₁) ≫ n log n / r. -/
axiom clemen_dumitrescu_liu_general (n r : ℕ) (hn : 2 ≤ n)
    (hr1 : 1 ≤ r) (hr2 : r ≤ Nat.log 2 n) :
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      A.card = n ∧ ∃ C : ℝ, 0 < C ∧
        C * n * Real.log n / r ≤ (frequencyGapR A r : ℝ)

-- ## Total pair count

/-- The sum of all distance frequencies is at most n choose 2. -/
theorem total_pairs (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    (distinctDistances A).sum (distFrequency A) ≤ A.card.choose 2 := by
  sorry

/-- If there are k distinct distances, the average frequency is at most n(n-1)/(2k). -/
theorem avg_frequency_bound (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (_hk : (distinctDistances A).card ≠ 0) :
    (distinctDistances A).sum (distFrequency A) / (distinctDistances A).card ≤
      A.card.choose 2 / (distinctDistances A).card := by
  exact Nat.div_le_div_right (total_pairs A)
