/-
Erdős Problem #489: Gaps Between B-Free Numbers

Source: https://erdosproblems.com/489
Status: OPEN

Statement:
Let A ⊆ ℕ be a set such that |A ∩ [1,x]| = o(x^{1/2}).
Let B = {n ≥ 1 : a ∤ n for all a ∈ A} (the "B-free" numbers).
If B = {b₁ < b₂ < ...} then is it true that
  lim (1/x) Σ_{bᵢ<x} (b_{i+1} - bᵢ)²
exists (and is finite)?

Example: When A = {p² : p prime}, then B is the squarefree numbers,
and the existence of this limit was proved by Erdős.

References:
- [Er61] Erdős, P., "Some unsolved problems",
  Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961), 221-254.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.NumberTheory.Squarefree

open Asymptotics Filter

namespace Erdos489

/-
## Part I: Sparse Sets and B-Free Numbers
-/

/--
**Counting Function:**
|A ∩ [1,x]| = number of elements of A up to x.
-/
def countingFunction (A : Set ℕ) (x : ℕ) : ℕ :=
  (Finset.filter (fun n => n ∈ A) (Finset.range (x + 1))).card

/--
**Sparse Set:**
A set A is sparse (for this problem) if |A ∩ [1,x]| = o(x^{1/2}).
This means the counting function grows slower than √x.
-/
def IsSparse (A : Set ℕ) : Prop :=
  (fun x : ℕ => (countingFunction A x : ℝ)) =o[atTop] (fun x => (x : ℝ) ^ (1/2 : ℝ))

/--
**B-Free Numbers:**
B = {n ∈ ℕ : a ∤ n for all a ∈ A}
These are numbers not divisible by any element of A.
-/
def BFreeSet (A : Set ℕ) : Set ℕ :=
  {n : ℕ | n ≥ 1 ∧ ∀ a ∈ A, ¬(a ∣ n)}

/--
**Alternative Definition:**
n is B-free (with respect to A) if no element of A divides n.
-/
def IsBFree (A : Set ℕ) (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ a ∈ A, ¬(a ∣ n)

/-
## Part II: Gaps and Gap Statistics
-/

/--
**Ordered Elements:**
Given an infinite set B, nthElement B n returns the n-th smallest
element. Axiomatized since it requires well-ordering machinery.
-/
axiom nthElement (B : Set ℕ) (n : ℕ) : ℕ

/--
**Gap Function:**
g_i = b_{i+1} - b_i is the gap between consecutive elements.
-/
def gap (B : Set ℕ) (i : ℕ) : ℕ :=
  nthElement B (i + 1) - nthElement B i

/--
**Gap Squared Sum:**
S(x) = Σ_{bᵢ < x} (b_{i+1} - bᵢ)²
-/
noncomputable def gapSquaredSum (B : Set ℕ) (x : ℕ) : ℝ :=
  ∑ i in Finset.range x, ((gap B i : ℕ) : ℝ) ^ 2

/--
**Normalized Gap Statistic:**
The quantity (1/x) Σ_{bᵢ<x} (b_{i+1} - bᵢ)²
-/
noncomputable def normalizedGapStatistic (B : Set ℕ) (x : ℕ) : ℝ :=
  gapSquaredSum B x / x

/-
## Part III: The Erdős Question
-/

/--
**The Main Question:**
Does the limit of (1/x) Σ_{bᵢ<x} (b_{i+1} - bᵢ)² exist and is finite?
-/
def LimitExists (A : Set ℕ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto
    (fun x : ℕ => normalizedGapStatistic (BFreeSet A) x)
    Filter.atTop
    (nhds L)

/--
**The Erdős Conjecture:**
If A is sparse (|A ∩ [1,x]| = o(√x)), then the limit exists.
-/
def ErdosConjecture : Prop :=
  ∀ A : Set ℕ, IsSparse A → LimitExists A

/-
## Part IV: The Squarefree Case
-/

/--
**Prime Squares:**
A = {p² : p prime}
-/
def PrimeSquares : Set ℕ :=
  {n : ℕ | ∃ p : ℕ, p.Prime ∧ n = p ^ 2}

/--
**Squarefree Numbers:**
When A = prime squares, B = squarefree numbers.
-/
/--
**Erdős's Theorem (for squarefrees):**
When A = {p² : p prime}, the limit exists.
-/
axiom erdos_squarefree_limit :
  LimitExists PrimeSquares

/--
**Density of Squarefree Numbers:**
The density of squarefree numbers is 6/π² ≈ 0.6079.
-/
/-
## Part V: K-Free Numbers
-/

/--
**K-Free Numbers:**
More generally, k-free numbers are those not divisible by any k-th power > 1.
-/
def IsKFree (k : ℕ) (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p ^ k ∣ n)

/--
**Cubefree Numbers:**
3-free numbers (not divisible by any cube).
-/
def IsCubefree (n : ℕ) : Prop := IsKFree 3 n

/-
## Part VI: Summary
-/

/--
**Erdős Problem #489 Summary:**

PROBLEM: For sparse A (|A ∩ [1,x]| = o(√x)), let B be the A-free numbers.
Does lim (1/x) Σ_{bᵢ<x} (b_{i+1} - bᵢ)² exist?

STATUS: OPEN (in general)

KNOWN CASE:
- A = {p² : p prime} (B = squarefree numbers): YES, limit exists (Erdős)

KEY INSIGHT: The sparseness condition o(√x) ensures B has positive density.
-/
theorem erdos_489_summary :
    -- Squarefree case is solved
    LimitExists PrimeSquares :=
  erdos_squarefree_limit

/--
**Erdős Problem #489: Known Special Case**
Squarefree numbers (A = prime squares).
-/
theorem erdos_489 : LimitExists PrimeSquares :=
  erdos_squarefree_limit

end Erdos489
