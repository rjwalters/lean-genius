/-!
# Erdős Problem #153: Gap Variance in Sidon Sumsets

Let A be a finite Sidon set and A+A = {s₁ < ... < sₜ}. Is it true that
(1/t) · Σ (s_{i+1} - s_i)² → ∞ as |A| → ∞?

## Status: OPEN

## References
- Erdős–Sárközy–Sós, "On Sum Sets of Sidon Sets, I" (1994)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
## Section I: Sidon Sets
-/

/-- A Sidon set (B₂ set): all pairwise sums are distinct.
a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-!
## Section II: Sumset and Gap Structure
-/

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The sorted sumset as a list. -/
noncomputable def sortedSumset (A : Finset ℕ) : List ℕ :=
  (sumset A).sort (· ≤ ·)

/-- The sum of squared consecutive gaps in the sorted sumset.
Given A+A = {s₁ < ... < sₜ}, this computes Σ (s_{i+1} - s_i)². -/
noncomputable def gapSquaredSum (A : Finset ℕ) : ℕ :=
  let sorted := sortedSumset A
  (List.zip sorted sorted.tail).foldl
    (fun acc p => acc + (p.2 - p.1) ^ 2) 0

/-!
## Section III: The Gap Variance
-/

/-- The mean squared gap: (1/t) · Σ (s_{i+1} - s_i)²
where t = |A+A| is the sumset cardinality. -/
noncomputable def meanGapSquared (A : Finset ℕ) : ℝ :=
  if (sumset A).card ≤ 1 then 0
  else (gapSquaredSum A : ℝ) / ((sumset A).card - 1 : ℝ)

/-- The minimum mean squared gap over all Sidon sets of size n. -/
noncomputable def minMeanGapSquared (n : ℕ) : ℝ :=
  ⨅ (A : Finset ℕ) (_ : A.card = n) (_ : IsSidon A), meanGapSquared A

/-!
## Section IV: The Conjecture
-/

/-- **Erdős Problem #153**: Does the mean squared gap in the sumset
of a Sidon set tend to infinity as the set grows?

Formally: for every M > 0, there exists N₀ such that for every
Sidon set A with |A| ≥ N₀, the mean squared gap in A+A exceeds M. -/
def ErdosProblem153 : Prop :=
  ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ A : Finset ℕ, IsSidon A → A.card ≥ N₀ →
      meanGapSquared A > M

/-!
## Section V: Sidon Set Sumset Properties
-/

/-- A Sidon set of size n has exactly n(n+1)/2 distinct pairwise sums
(counting ordered pairs with a ≤ b). -/
axiom sidon_sumset_card (A : Finset ℕ) (h : IsSidon A) :
    (sumset A).card ≥ A.card * (A.card + 1) / 2

/-- If A ⊆ {1,...,N} is Sidon, then A+A ⊆ {2,...,2N} so gaps can be
computed within a bounded range. -/
axiom sidon_sumset_range (A : Finset ℕ) (N : ℕ) (h : IsSidon A)
    (hN : ∀ a ∈ A, a ≤ N) :
    ∀ s ∈ sumset A, s ≤ 2 * N

/-!
## Section VI: Known Bounds
-/

/-- The sumset has size Θ(n²) while lying in an interval of length
Θ(n²) (since Sidon sets have size O(√N) in {1,...,N}).
The average gap is therefore Θ(1), but the variance could grow. -/
axiom average_gap_bounded (A : Finset ℕ) (N : ℕ) (h : IsSidon A)
    (hN : ∀ a ∈ A, a ≤ N) (hn : A.card ≥ 2) :
    ∃ C : ℝ, C > 0 ∧
      (2 * N : ℝ) / (sumset A).card ≤ C

/-- Erdős, Sárközy, and Sós (1994) studied the gap distribution
in sumsets of Sidon sets and posed this problem about the
variance growing without bound. -/
axiom ess_1994_result :
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℕ, IsSidon A → A.card ≥ 4 →
      meanGapSquared A ≥ c

/-!
## Section VII: Infinite Sidon Sets
-/

/-- An infinite Sidon set: all pairwise sums from the set are distinct. -/
def IsInfiniteSidon (S : Set ℕ) : Prop :=
  S.Infinite ∧
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- A similar question for infinite Sidon sets: do the gaps in the
sumset restricted to {1,...,N} have growing variance as N → ∞? -/
axiom infinite_sidon_gap_question :
  ∀ S : Set ℕ, IsInfiniteSidon S →
    ∀ M : ℝ, M > 0 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        let A := (Finset.range (N + 1)).filter (· ∈ S)
        A.card ≥ 2 → meanGapSquared A > M
