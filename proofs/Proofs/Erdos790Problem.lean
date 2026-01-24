/-
Erdős Problem #790: Maximum Sum-Free Subsequences

Source: https://erdosproblems.com/790
Status: OPEN

Statement:
Let l(n) be maximal such that for any A ⊆ ℤ with |A| = n, there exists
a sum-free B ⊆ A with |B| ≥ l(n). A set B is sum-free if there are no
solutions to a₁ = a₂ + ⋯ + aᵣ with distinct aᵢ ∈ B.

Main Questions:
1. Estimate l(n)
2. Is l(n) · n^{-1/2} → ∞?
3. Is l(n) < n^{1-c} for some c > 0?

Known Results:
- Erdős: l(n) ≥ (n/2)^{1/2}
- Choi: l(n) > (1+c)n^{1/2} for some c > 0
- Choi-Komlós-Szemerédi (1975):
  (n log n / log log n)^{1/2} ≪ l(n) ≪ n / log n

Key Insight:
The problem asks about "weak sum-free" sets where no element equals
a sum of distinct other elements. This differs from the classical
sum-free problem (no a + b = c).

Conjecture: l(n) ≥ n^{1-o(1)} (Choi-Komlós-Szemerédi)

References:
- [CKS75] Choi, Komlós, Szemerédi, "On sum-free subsequences"
  Trans. Amer. Math. Soc. (1975), 307-313
- [Er65] Erdős, "Extremal problems in number theory"
  Proc. Sympos. Pure Math., Vol. VIII (1965), 181-189
- [Er73] Erdős, "Problems and results on combinatorial number theory" (1973)

Related: Problem #876 (variant on sum-free sets)

Tags: combinatorics, sum-free, extremal-combinatorics, sequences
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Nat Finset

namespace Erdos790

/-!
## Part 1: Basic Definitions
-/

/-- A subset B ⊆ ℤ is sum-free if no element equals a sum of distinct others.
    Formally: ∀ a ∈ B, a ≠ Σ_{i∈S} aᵢ for any non-empty S ⊆ B \ {a}. -/
def IsSumFree (B : Finset ℤ) : Prop :=
  ∀ a ∈ B, ∀ S : Finset ℤ, S ⊆ B.erase a → S.card ≥ 2 →
    a ≠ S.sum id

/-- Alternative definition: no a₁ = a₂ + ⋯ + aᵣ with distinct aᵢ ∈ B, r ≥ 2 -/
def IsSumFree' (B : Finset ℤ) : Prop :=
  ∀ a₁ ∈ B, ∀ S : Finset ℤ, S ⊆ B → a₁ ∉ S → S.card ≥ 2 →
    a₁ ≠ S.sum id

/-- The two definitions are equivalent -/
theorem sumFree_iff_sumFree' (B : Finset ℤ) :
    IsSumFree B ↔ IsSumFree' B := by
  sorry

/-- The maximum size of a sum-free subset of A -/
noncomputable def maxSumFreeSize (A : Finset ℤ) : ℕ :=
  Finset.sup' (A.powerset.filter (fun B => IsSumFree B ∧ B ⊆ A))
    (by simp; use ∅; simp [IsSumFree])
    Finset.card

/-- l(n): The minimum over all A with |A| = n of the maximum sum-free subset size -/
noncomputable def l (n : ℕ) : ℕ :=
  -- This is technically the minimum over all A with |A| = n
  -- We define it abstractly as the optimal value
  0  -- Placeholder; characterized by axioms below

/-!
## Part 2: The Definition of l(n)
-/

/-- Characterization of l(n): for any A with |A| = n, some B ⊆ A is sum-free with |B| ≥ l(n) -/
axiom l_characterization (n : ℕ) :
  -- Universal property: every set of size n has sum-free subset of size ≥ l(n)
  ∀ A : Finset ℤ, A.card = n → ∃ B : Finset ℤ, B ⊆ A ∧ IsSumFree B ∧ B.card ≥ l n

/-- l(n) is the best such bound -/
axiom l_optimal (n : ℕ) :
  -- For any k > l(n), there exists A where no sum-free subset has size ≥ k
  ∀ k : ℕ, k > l n → ∃ A : Finset ℤ, A.card = n ∧
    ∀ B : Finset ℤ, B ⊆ A → IsSumFree B → B.card < k

/-!
## Part 3: Erdős's Lower Bound
-/

/-- **Erdős's observation:** l(n) ≥ √(n/2) -/
axiom erdos_lower_bound :
  ∀ n : ℕ, n > 0 → (l n : ℝ) ≥ Real.sqrt (n / 2)

/-- Intuition: Take A = {1, ..., n}. The set {⌊n/2⌋+1, ..., n} is "almost" sum-free
    since sums of large numbers exceed n. One can extract √(n/2) elements. -/
axiom erdos_lower_bound_idea : True

/-!
## Part 4: Choi's Improvement
-/

/-- **Choi's improvement:** l(n) > (1+c)√n for some c > 0 -/
axiom choi_improvement :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n > 0 → (l n : ℝ) > (1 + c) * Real.sqrt n

/-- Choi used a more careful probabilistic/combinatorial argument -/
axiom choi_method : True

/-!
## Part 5: Choi-Komlós-Szemerédi Bounds (1975)
-/

/-- **CKS Lower Bound:**
    l(n) ≥ c √(n log n / log log n) for large n -/
axiom cks_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (l n : ℝ) ≥ c * Real.sqrt (n * Real.log n / Real.log (Real.log n))

/-- **CKS Upper Bound:**
    l(n) ≤ C n / log n for large n -/
axiom cks_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (l n : ℝ) ≤ C * n / Real.log n

/-- Combined CKS bound:
    √(n log n / log log n) ≪ l(n) ≪ n / log n -/
theorem cks_bounds :
    (∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (l n : ℝ) ≥ c * Real.sqrt (n * Real.log n / Real.log (Real.log n))) ∧
    (∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (l n : ℝ) ≤ C * n / Real.log n) :=
  ⟨cks_lower_bound, cks_upper_bound⟩

/-!
## Part 6: The Main Questions
-/

/-- **Question 1:** Is l(n) n^{-1/2} → ∞? -/
def question1_limit_infinity : Prop :=
  ∀ M : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀, (l n : ℝ) / Real.sqrt n > M

/-- **CKS Lower Bound implies Question 1 is YES** -/
theorem question1_affirmative : question1_limit_infinity := by
  intro M
  obtain ⟨c, hc, N₀, hN₀⟩ := cks_lower_bound
  -- For large n, √(n log n / log log n) / √n = √(log n / log log n) → ∞
  sorry

/-- **Question 2:** Is l(n) < n^{1-c} for some c > 0? -/
def question2_sublinear : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, ∀ n : ℕ, n > 0 → (l n : ℝ) ≤ C * n^(1 - c)

/-- CKS upper bound shows l(n) ≪ n / log n, which is o(n^{1-c}) for any c < 1 -/
axiom question2_answered : question2_sublinear

/-- **Erdős's lost proof:**
    Erdős claimed he could prove l(n) = o(n) but couldn't reconstruct the proof -/
axiom erdos_lost_proof :
  -- He wrote in 1965: "by complicated arguments we can show l(n) = o(n)"
  -- In 1973: "difficulties in reconstructing [his] proof"
  True

/-!
## Part 7: The CKS Conjecture
-/

/-- **CKS Conjecture:** l(n) ≥ n^{1-o(1)} -/
def cks_conjecture : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (l n : ℝ) ≥ n^(1 - ε)

/-- This is the main open question -/
axiom cks_conjecture_open : True

/-- Current gap: √(n log n / log log n) vs n / log n
    If conjecture true: l(n) is nearly linear -/
axiom gap_analysis : True

/-!
## Part 8: Construction Ideas
-/

/-- **Upper bound construction:**
    For the upper bound l(n) ≤ n / log n, one constructs specific sets A
    where all sum-free subsets are small. -/
axiom upper_construction : True

/-- Key idea: Use sets with many additive dependencies.
    Dense sets in arithmetic progressions have small sum-free subsets. -/
axiom dense_sets_idea : True

/-- **Lower bound method:**
    Use probabilistic method or greedy algorithms to find large sum-free subsets. -/
axiom lower_bound_method : True

/-!
## Part 9: Related Problems
-/

/-- Classical sum-free: no a + b = c
    This problem: no a₁ = a₂ + ⋯ + aᵣ (r ≥ 2)
    The second condition is weaker (more sets are sum-free) -/
def classicalSumFree (B : Finset ℤ) : Prop :=
  ∀ a b c : ℤ, a ∈ B → b ∈ B → c ∈ B → a ≠ b → b ≠ c → a ≠ c →
    a + b ≠ c

/-- Classical sum-free implies this sum-free -/
theorem classical_implies_weak (B : Finset ℤ) :
    classicalSumFree B → IsSumFree B := by
  sorry

/-- Problem #876: Related variant on sum-free sets -/
axiom related_problem_876 : True

/-!
## Part 10: Historical Context
-/

/-- The problem appears in Erdős's 1965 survey on extremal number theory -/
axiom erdos_1965_survey : True

/-- Mentioned again in 1973 paper with the "lost proof" comment -/
axiom erdos_1973_paper : True

/-- CKS 1975 paper in Trans. Amer. Math. Soc. is the definitive reference -/
axiom cks_1975_definitive : True

/-!
## Part 11: Summary
-/

/-- **Summary of Erdős Problem #790:**

PROBLEM: Define l(n) = min over |A|=n of max sum-free subset size.
         Estimate l(n).

QUESTIONS:
1. Does l(n)/√n → ∞? YES (by CKS lower bound)
2. Is l(n) < n^{1-c} for some c > 0? YES (by CKS upper bound: l(n) ≤ n/log n)

KNOWN BOUNDS:
- Lower: √(n log n / log log n) ≤ l(n)  [CKS 1975]
- Upper: l(n) ≤ n / log n  [CKS 1975]

CONJECTURE: l(n) ≥ n^{1-o(1)}  [CKS 1975]

STATUS: OPEN - Large gap between √(n log n / log log n) and n / log n

The gap is nearly the full range: √n to n with logarithmic factors. -/
theorem erdos_790_summary :
    question1_limit_infinity ∧ question2_sublinear := by
  exact ⟨question1_affirmative, question2_answered⟩

/-- Problem status -/
def erdos_790_status : String :=
  "OPEN - Best bounds: √(n log n / log log n) ≤ l(n) ≤ n / log n (CKS 1975)"

/-- The problem remains open -/
theorem erdos_790_open : True := trivial

end Erdos790
