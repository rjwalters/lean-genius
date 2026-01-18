/-
Erdős Problem #359: MacMahon's Prime Numbers of Measurement

Source: https://erdosproblems.com/359
Status: OPEN

Statement:
Let a₁ < a₂ < ... be an infinite sequence where a₁ = n and a_{i+1} is the
smallest integer not expressible as a sum of consecutive earlier terms.
What can be said about the density of this sequence?

Specific questions (n = 1):
1. Prove a_k / k → ∞
2. Prove a_k / k^{1+c} → 0 for any c > 0

Known Results:
- MacMahon's problem, studied by Andrews [An75]
- For n = 1: sequence is 1, 2, 4, 5, 8, 10, 14, 15, ... (OEIS A002048)
- Andrews conjectured: a_k ~ (k log k) / (log log k)
- Porubský [Po77] proved partial results on density

References:
- [An75] Andrews, G.E., "MacMahon's Prime Numbers of Measurement" (1975)
- [Po77] Porubský, Š., "On MacMahon's segmented numbers" (1977)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Finset Set Filter

namespace Erdos359

/-!
## Part I: Core Definitions

We define the sequence recursively: a₀ = n and a_{j+1} is the smallest
natural number greater than a_j that cannot be expressed as a sum of
consecutive terms from a₀, ..., a_j.
-/

/-- A sum of consecutive terms a_i + a_{i+1} + ... + a_j from the sequence A.
    We use Finset.Icc for the interval [a, b]. -/
def ConsecutiveSum (A : ℕ → ℕ) (a b : ℕ) : ℕ :=
  ∑ i ∈ Finset.Icc a b, A i

/-- The set of all consecutive sums achievable from the first k+1 terms.
    A number m is achievable if m = A(a) + A(a+1) + ... + A(b) for some a ≤ b ≤ k. -/
def AchievableSums (A : ℕ → ℕ) (k : ℕ) : Set ℕ :=
  { m | ∃ a b, a ≤ b ∧ b ≤ k ∧ m = ConsecutiveSum A a b }

/-- A sequence A is "good for n" if:
    1. A(0) = n
    2. A is strictly increasing
    3. For each j, A(j+1) is the least integer greater than A(j) not in
       AchievableSums from the first j+1 terms. -/
def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop :=
  A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    { m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ConsecutiveSum A a b }
    (A (j + 1))

/-- The MacMahon sequence is the unique sequence "good for 1". -/
def IsMacMahonSeq (A : ℕ → ℕ) : Prop := IsGoodFor A 1

/-!
## Part II: Basic Properties
-/

/-- The first term of a MacMahon sequence is 1. -/
theorem macmahon_first_term (A : ℕ → ℕ) (h : IsMacMahonSeq A) : A 0 = 1 :=
  h.1

/-- A MacMahon sequence is strictly increasing. -/
theorem macmahon_strictMono (A : ℕ → ℕ) (h : IsMacMahonSeq A) : StrictMono A :=
  h.2.1

/-- Every term A(i) is achievable as a sum (the singleton sum). -/
theorem term_is_achievable (A : ℕ → ℕ) (i k : ℕ) (hik : i ≤ k) :
    A i ∈ AchievableSums A k := by
  use i, i
  constructor
  · exact le_refl i
  constructor
  · exact hik
  · simp [ConsecutiveSum]

/-!
## Part III: Known Values

The MacMahon sequence (OEIS A002048) begins: 1, 2, 4, 5, 8, 10, 14, 15, ...
-/

/-- The first 8 values of the MacMahon sequence. -/
def macmahonValues : Fin 8 → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 5
  | 4 => 8
  | 5 => 10
  | 6 => 14
  | 7 => 15

/-- The known values match the sequence definition (axiom pending full proof). -/
axiom macmahon_initial_values :
  ∀ A : ℕ → ℕ, IsMacMahonSeq A →
    ∀ i : Fin 8, A i.val = macmahonValues i

/-- Why 3 is skipped: 3 = 1 + 2 = A(0) + A(1) is achievable. -/
theorem three_is_achievable (A : ℕ → ℕ)
    (h_vals : A 0 = 1 ∧ A 1 = 2) :
    3 ∈ AchievableSums A 1 := by
  use 0, 1
  refine ⟨Nat.zero_le 1, le_refl 1, ?_⟩
  unfold ConsecutiveSum
  rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ 1)]
  simp only [Finset.Icc_self, Finset.sum_singleton, h_vals.1, h_vals.2]

/-- Why 6 is skipped: 6 = 2 + 4 = A(1) + A(2) is achievable. -/
theorem six_is_achievable (A : ℕ → ℕ)
    (h_vals : A 1 = 2 ∧ A 2 = 4) :
    6 ∈ AchievableSums A 2 := by
  use 1, 2
  refine ⟨by omega, le_refl 2, ?_⟩
  unfold ConsecutiveSum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ 2)]
  simp only [Finset.Icc_self, Finset.sum_singleton, h_vals.1, h_vals.2]

/-!
## Part IV: Growth Rate Conjectures (OPEN)

The main questions about growth rate remain open.
-/

/-- **Open Conjecture I**: a_k / k → ∞ as k → ∞.
    This means the sequence grows faster than linear. -/
axiom growth_faster_than_linear :
  ∀ A : ℕ → ℕ, IsMacMahonSeq A →
    Tendsto (fun k => (A k : ℝ) / k) atTop atTop

/-- **Open Conjecture II**: a_k / k^{1+c} → 0 for any c > 0.
    This means the sequence grows slower than any polynomial > 1. -/
axiom growth_slower_than_polynomial :
  ∀ A : ℕ → ℕ, IsMacMahonSeq A →
    ∀ c : ℝ, c > 0 →
      Tendsto (fun k => (A k : ℝ) / (k : ℝ) ^ (1 + c)) atTop (nhds 0)

/-- **Andrews' Conjecture**: a_k ~ (k log k) / (log log k).
    The asymptotic growth rate is superlinear but subpolynomial. -/
axiom andrews_conjecture :
  ∀ A : ℕ → ℕ, IsMacMahonSeq A →
    ∃ f : ℕ → ℝ, (∀ k, k > 1 → f k = (k : ℝ) * Real.log k / Real.log (Real.log k)) ∧
      Tendsto (fun k => (A k : ℝ) / f k) atTop (nhds 1)

/-!
## Part V: Porubský's Partial Results

Porubský proved some bounds on the growth rate.
-/

/-- **Porubský's Upper Bound** (1977): For any ε > 0, infinitely many k satisfy
    a_k < (log k)^ε · (k log k) / (log log k). -/
axiom porubsky_upper :
  ∀ A : ℕ → ℕ, IsMacMahonSeq A →
    ∀ ε : ℝ, ε > 0 →
      ∀ N : ℕ, ∃ k > N,
        (A k : ℝ) < Real.log k ^ ε * (k * Real.log k / Real.log (Real.log k))

/-- Counting function: A(x) = number of terms ≤ x. -/
noncomputable def countingFunction (A : ℕ → ℕ) (x : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun i => A i ≤ x) (Finset.range (x + 1)))

/-- Prime counting function π(x) = number of primes ≤ x. -/
noncomputable def primeCounting (x : ℕ) : ℕ :=
  Finset.card (Finset.filter Nat.Prime (Finset.range (x + 1)))

/-- **Porubský's Density Bound**: limsup A(x)/π(x) ≥ 1/log(2).
    The MacMahon sequence is denser than primes by a factor of at least 1/log(2). -/
axiom porubsky_density_bound :
  ∀ A : ℕ → ℕ, IsMacMahonSeq A →
    ∀ c : ℝ, c < 1 / Real.log 2 →
      ∀ N : ℕ, ∃ x > N,
        c < (countingFunction A x : ℝ) / primeCounting x

/-!
## Part VI: General Starting Value n

The problem also considers sequences starting with n ≠ 1.
-/

/-- For general n, the sequence still grows superlinearly (conjectured). -/
axiom general_n_superlinear :
  ∀ n : ℕ, n > 0 →
    ∀ A : ℕ → ℕ, IsGoodFor A n →
      Tendsto (fun k => (A k : ℝ) / k) atTop atTop

/-!
## Summary

**Erdős Problem #359** (OPEN) concerns MacMahon's sequence where each term
is the smallest integer not expressible as a consecutive sum of earlier terms.

**Main Open Questions**:
1. Prove a_k / k → ∞
2. Prove a_k / k^{1+c} → 0 for c > 0
3. Verify Andrews' conjecture: a_k ~ (k log k) / (log log k)

**Known**:
- First terms: 1, 2, 4, 5, 8, 10, 14, 15, ... (OEIS A002048)
- Porubský's partial bounds on density
- Comparison with prime counting function
-/

/-- Summary theorem packaging the main structure. -/
theorem erdos_359_summary :
    (∀ A, IsMacMahonSeq A → A 0 = 1) ∧
    (∀ A, IsMacMahonSeq A → StrictMono A) ∧
    macmahonValues 0 = 1 ∧
    macmahonValues 7 = 15 := by
  constructor
  · exact macmahon_first_term
  constructor
  · exact macmahon_strictMono
  constructor
  · rfl
  · rfl

end Erdos359
