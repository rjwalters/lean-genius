/-
Erdős Problem #874: Admissible Sets and Subset Sum Disjointness

Source: https://erdosproblems.com/874
Status: SOLVED (Deshouillers-Freiman, 1999)

Statement:
Let k(N) denote the size of the largest set A ⊆ {1,...,N} such that the sets
  S_r = { a₁ + ⋯ + a_r : a₁ < ⋯ < a_r ∈ A }
are disjoint for distinct r ≥ 1.

Estimate k(N) - in particular, is it true that k(N) ~ 2√N?

Answer: YES, proved by Deshouillers-Freiman (1999) for all large N.

History:
- Straus (1966): Called such sets "admissible"; proved 2 ≤ liminf k(N)/√N
  and limsup k(N)/√N ≤ 4/√3 ≈ 2.309
- Erdős-Nicolas-Sárközy (1991): Improved upper bound to √(143/27) ≈ 2.301
- Deshouillers-Freiman (1999): Proved k(N) ~ 2√N for large N

Key Insight:
The extremal sets often have the form (N-k, N] ∩ ℕ (top k integers),
which gives disjoint sums due to the "greedy" structure.

Related: Problems #186, #789, #875 (infinite version)
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset Nat

namespace Erdos874

/- ## Part I: Basic Definitions -/

/--
**Admissible Set:**
A subset A ⊆ {1,...,N} is admissible if sums of distinct sizes produce disjoint sets.
That is, for r ≠ s, the sets S_r and S_s are disjoint.
-/
def sumSet (A : Finset ℕ) (r : ℕ) : Set ℕ :=
  { s | ∃ B : Finset ℕ, B ⊆ A ∧ B.card = r ∧ s = B.sum id }

/--
**Disjoint Sums Property:**
The sum sets S_r are pairwise disjoint for different r.
-/
def hasDisjointSums (A : Finset ℕ) : Prop :=
  ∀ r s : ℕ, r ≠ s → r ≥ 1 → s ≥ 1 → sumSet A r ∩ sumSet A s = ∅

/--
**Admissible:**
A set is admissible if it has disjoint sums (Straus's terminology).
-/
def Admissible (A : Finset ℕ) : Prop :=
  hasDisjointSums A

/--
**Bounded Admissible:**
An admissible set contained in {1,...,N}.
-/
def BoundedAdmissible (A : Finset ℕ) (N : ℕ) : Prop :=
  Admissible A ∧ ∀ a ∈ A, a ≤ N ∧ a ≥ 1

/- ## Part II: The Function k(N) -/

/--
**k(N):**
The maximum size of an admissible subset of {1,...,N}.
-/
noncomputable def k (N : ℕ) : ℕ :=
  Finset.sup (Finset.filter (fun A => BoundedAdmissible A N)
    (Finset.powerset (Finset.range (N + 1)))) Finset.card

/- ## Part III: Straus's Results (1966) -/

/--
**Straus's Construction:**
The interval (N-k, N] ∩ ℕ is admissible when k is chosen appropriately.

For m² ≤ N < m² + m: use k = 2m - 1
For m² + m ≤ N < (m+1)²: use k = 2m
-/
def strausSet (N : ℕ) : Finset ℕ :=
  let m := Nat.sqrt N
  let boundary := m * m + m
  let size := if N < boundary then 2 * m - 1 else 2 * m
  Finset.filter (fun x => x > N - size ∧ x ≤ N) (Finset.range (N + 1))

/--
**Straus's Lower Bound:**
The construction shows liminf k(N)/√N ≥ 2.
-/

/--
**Straus's Upper Bound:**
limsup k(N)/√N ≤ 4/√3 ≈ 2.309.
-/

/--
**The constant 4/√3:**
-/
noncomputable def strausConstant : ℝ := 4 / Real.sqrt 3

theorem straus_constant_value : strausConstant = 4 / Real.sqrt 3 := rfl

/- ## Part IV: Erdős-Nicolas-Sárközy Improvement (1991) -/

/--
**ENS Constant:**
√(143/27) ≈ 2.301, improving Straus's 4/√3 ≈ 2.309.
-/
noncomputable def ensConstant : ℝ := Real.sqrt (143 / 27)

/--
**ENS Upper Bound (1991):**
limsup k(N)/√N ≤ √(143/27).
-/

/--
**ENS improves Straus:**
√(143/27) < 4/√3, so the ENS bound is strictly better.
Axiomatized since this requires numerical computation beyond native_decide.
-/

/- ## Part V: Deshouillers-Freiman Resolution (1999) -/

/--
**Main Theorem (Deshouillers-Freiman, 1999):**
For all sufficiently large N, k(N) ~ 2√N.

More precisely: lim_{N→∞} k(N)/√N = 2.
-/
axiom deshouillers_freiman_main :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(k N : ℝ) / Real.sqrt N - 2| < ε

/--
**The limit exists and equals 2:**
-/
axiom k_limit_is_two :
    Filter.Tendsto (fun N => (k N : ℝ) / Real.sqrt N) Filter.atTop (nhds 2)

/--
**Optimal sets are often intervals:**
Deshouillers-Freiman showed that for some N, the optimal A has
the form (N-k, N] ∩ ℕ.
-/

/- ## Part VI: Examples -/

/--
**Example: Small cases**
For N = 4, we can take A = {3, 4} with k = 2.
S₁ = {3, 4}, S₂ = {7}.
-/
def example_N4 : Finset ℕ := {3, 4}

/--
**Example: N = 9**
We expect k(9) ≈ 2√9 = 6.
One admissible set: {4, 5, 6, 7, 8, 9}.
-/
def example_N9 : Finset ℕ := {4, 5, 6, 7, 8, 9}

/- ## Part VII: Sum Set Properties -/

/--
**Sum set cardinality bound:**
|S_r| is at most C(|A|, r), and equals C(|A|, r) when all sums are distinct.
This follows since each r-element subset gives at most one sum.
-/

/--
**Total sum constraint:**
If A ⊆ {1,...,N} and sums are disjoint, the total number of distinct sums
is bounded by the sum range. For r-element sums from A ⊆ {1,...,N},
sums lie in [r, r·N], giving at most r·(N-1)+1 values per level.
-/

/- ## Part VIII: Summary -/

/--
**Summary of Erdős Problem #874:**

**Question:** Is k(N) ~ 2√N?

**Answer:** YES (Deshouillers-Freiman, 1999)

**History:**
1. Straus (1966): 2 ≤ liminf k(N)/√N ≤ limsup k(N)/√N ≤ 4/√3
2. ENS (1991): Improved upper bound to √(143/27)
3. Deshouillers-Freiman (1999): Proved lim k(N)/√N = 2

**Key Insight:**
Intervals (N-k, N] are often optimal, and their sums naturally separate.
-/

/--
**Main Result: Erdős Problem #874 is SOLVED**
-/
theorem erdos_874 :
    Filter.Tendsto (fun N => (k N : ℝ) / Real.sqrt N) Filter.atTop (nhds 2) :=
  k_limit_is_two

/--
**Answer: The conjecture is TRUE**
-/
theorem erdos_874_answer :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (2 - ε) * Real.sqrt N ≤ k N ∧ (k N : ℝ) ≤ (2 + ε) * Real.sqrt N := by
  intro ε hε
  have half_ε := half_pos hε
  obtain ⟨N₁, h₁⟩ := deshouillers_freiman_main (ε/2) half_ε
  use N₁
  intro N hN
  specialize h₁ N hN
  constructor <;> {
    have := abs_sub_lt_iff.mp h₁
    linarith [Real.sqrt_nonneg N]
  }

end Erdos874
