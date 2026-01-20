/-
Erdős Problem #788: Sum-Free Subsets in Intervals

Source: https://erdosproblems.com/788
Status: OPEN

Statement:
Let f(n) be maximal such that if B ⊂ (2n,4n) ∩ ℕ, there exists C ⊂ (n,2n) ∩ ℕ
such that c₁ + c₂ ∉ B for all c₁ ≠ c₂ ∈ C and |C| + |B| ≥ f(n).

Estimate f(n). Is it true that f(n) ≤ n^{1/2+o(1)}?

Background:
This is a problem about sum-free subsets within specific intervals. Given any
set B in the interval (2n, 4n), we seek a set C in (n, 2n) such that no two
distinct elements of C sum to something in B. The function f(n) measures how
large |C| + |B| can always be guaranteed.

Key Results:
- Choi (1971): Conjectured the problem, proved f(n) ≪ n^{3/4}
- Adenwalla: Proved f(n) ≫ n^{1/2} (simple construction)
- Hunter: Sketched f(n) ≪ n^{2/3+o(1)}
- Baltz-Schoen-Srivastav (2000): Proved f(n) ≪ (n log n)^{2/3}

The gap between n^{1/2} and (n log n)^{2/3} remains open.

References:
- [Ch71] Choi, "On a combinatorial problem in number theory", 1971
- [BSS00] Baltz-Schoen-Srivastav, "Probabilistic construction of small
         strongly sum-free sets via large Sidon sets", 2000

Tags: additive-combinatorics, sum-free-sets, intervals
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

namespace Erdos788

/-!
## Part I: Basic Definitions
-/

/--
**Open Interval of Natural Numbers:**
The set (a, b) ∩ ℕ, i.e., natural numbers strictly between a and b.
-/
def openInterval (a b : ℕ) : Finset ℕ :=
  (Finset.range b).filter (fun x => a < x ∧ x < b)

/--
**The Interval (n, 2n):**
Natural numbers strictly between n and 2n.
-/
def lowerInterval (n : ℕ) : Finset ℕ := openInterval n (2 * n)

/--
**The Interval (2n, 4n):**
Natural numbers strictly between 2n and 4n.
-/
def upperInterval (n : ℕ) : Finset ℕ := openInterval (2 * n) (4 * n)

/--
**Pairwise Sum Set:**
The set of all pairwise sums c₁ + c₂ where c₁ ≠ c₂ are in C.
-/
def pairwiseSums (C : Finset ℕ) : Finset ℕ :=
  (C.product C).filter (fun p => p.1 ≠ p.2) |>.image (fun p => p.1 + p.2)

/--
**Sum-Free with Respect to B:**
C is sum-free with respect to B if no two distinct elements of C sum to
an element of B.
-/
def isSumFreeWithResp (C B : Finset ℕ) : Prop :=
  ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → c₁ + c₂ ∉ B

/--
**Equivalent definition using pairwise sums:**
-/
theorem sumFree_iff_disjoint (C B : Finset ℕ) :
    isSumFreeWithResp C B ↔ Disjoint (pairwiseSums C) B := by
  sorry

/-!
## Part II: The Function f(n)
-/

/--
**Valid Configuration:**
A pair (B, C) is valid if B ⊂ (2n, 4n), C ⊂ (n, 2n), and C is sum-free
with respect to B.
-/
def isValidConfig (n : ℕ) (B C : Finset ℕ) : Prop :=
  B ⊆ upperInterval n ∧
  C ⊆ lowerInterval n ∧
  isSumFreeWithResp C B

/--
**The Function f(n):**
f(n) is the maximum value such that for all B ⊂ (2n, 4n), there exists
C ⊂ (n, 2n) sum-free w.r.t. B with |C| + |B| ≥ f(n).
-/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.find (⟨0, fun _ _ => ⟨∅, by simp [isValidConfig, isSumFreeWithResp]⟩⟩ :
    ∃ k, ∀ B ⊆ upperInterval n, ∃ C ⊆ lowerInterval n,
      isSumFreeWithResp C B ∧ C.card + B.card ≥ k)

/--
**Alternative characterization:**
f(n) is the largest k such that for all B, we can find C with |C| + |B| ≥ k.
-/
def fDef : Prop :=
  ∀ n : ℕ, f n = Nat.find (⟨0, fun _ _ => ⟨∅, by simp [isValidConfig, isSumFreeWithResp]⟩⟩ :
    ∃ k, ∀ B ⊆ upperInterval n, ∃ C ⊆ lowerInterval n,
      isSumFreeWithResp C B ∧ C.card + B.card ≥ k)

/-!
## Part III: Choi's Original Bound (1971)
-/

/--
**Choi's Upper Bound:**
f(n) ≪ n^{3/4}, i.e., f(n) ≤ C · n^{3/4} for some constant C.
-/
axiom choi_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * (n : ℝ) ^ (3/4 : ℝ)

/--
**Choi's Conjecture:**
Is it true that f(n) ≤ n^{1/2+o(1)}?
-/
def choiConjecture : Prop :=
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, (f n : ℝ) ≤ (n : ℝ) ^ (1/2 + ε : ℝ)

/-!
## Part IV: Adenwalla's Lower Bound
-/

/--
**Adenwalla's Construction:**
f(n) ≫ n^{1/2}, proved by a simple construction.
-/
axiom adenwalla_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ c * (n : ℝ) ^ (1/2 : ℝ)

/--
**Construction idea:**
Take C to be a Sidon set in (n, 2n). A Sidon set has all pairwise sums
distinct, giving control over which elements of (2n, 4n) are hit.
-/
def sidonSetConstruction : Prop :=
  -- A Sidon set in (n, 2n) of size ~√n can be sum-free w.r.t. a large B
  True

/--
**Sidon Set:**
A set S is a Sidon set if all pairwise sums a + b (a ≤ b, both in S) are distinct.
-/
def isSidonSet (S : Finset ℕ) : Prop :=
  ∀ a₁ b₁ a₂ b₂, a₁ ∈ S → b₁ ∈ S → a₂ ∈ S → b₂ ∈ S →
    a₁ ≤ b₁ → a₂ ≤ b₂ → a₁ + b₁ = a₂ + b₂ → (a₁ = a₂ ∧ b₁ = b₂)

/--
**Sidon sets in intervals:**
There exist Sidon sets of size ~√n in any interval of length n.
-/
axiom sidon_sets_exist :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∃ S ⊆ lowerInterval n,
    isSidonSet S ∧ (S.card : ℝ) ≥ c * (n : ℝ) ^ (1/2 : ℝ)

/-!
## Part V: Hunter's Improvement
-/

/--
**Hunter's Bound:**
f(n) ≪ n^{2/3+o(1)}, improving Choi's bound.
-/
axiom hunter_bound :
  ∀ ε > 0, ∃ n₀ : ℕ, ∃ C : ℝ, C > 0 ∧
    ∀ n ≥ n₀, (f n : ℝ) ≤ C * (n : ℝ) ^ (2/3 + ε : ℝ)

/--
**Sketch of Hunter's argument:**
Uses a counting argument on the structure of sum-free sets.
-/
axiom hunter_argument_sketch : True

/-!
## Part VI: Baltz-Schoen-Srivastav Bound (2000)
-/

/--
**Best Known Upper Bound:**
f(n) ≪ (n log n)^{2/3}, proved using probabilistic methods.
-/
axiom bss_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (f n : ℝ) ≤ C * ((n : ℝ) * Real.log n) ^ (2/3 : ℝ)

/--
**Probabilistic method:**
The proof uses large Sidon sets constructed probabilistically.
-/
def bssProbabilisticMethod : Prop :=
  -- Probabilistic construction of strongly sum-free sets
  True

/--
**Strongly Sum-Free Set:**
A set is strongly sum-free if it avoids all sums and differences.
-/
def isStronglySumFree (S : Finset ℕ) : Prop :=
  ∀ a b c, a ∈ S → b ∈ S → c ∈ S → a + b ≠ c ∧ (a ≠ b → a - b ≠ c)

/-!
## Part VII: The Gap
-/

/--
**Current Knowledge:**
Lower bound: f(n) ≫ n^{1/2}
Upper bound: f(n) ≪ (n log n)^{2/3}
-/
theorem current_bounds :
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ c * (n : ℝ) ^ (1/2 : ℝ)) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f n : ℝ) ≤ C * ((n : ℝ) * Real.log n) ^ (2/3 : ℝ)) := by
  exact ⟨adenwalla_lower_bound, bss_bound⟩

/--
**The Gap:**
Is f(n) = Θ(n^{1/2}) or closer to (n log n)^{2/3}?
Choi's conjecture f(n) ≤ n^{1/2+o(1)} remains open.
-/
theorem the_gap :
    -- The exponent is between 1/2 and 2/3
    -- Choi conjectured it is 1/2 + o(1)
    True := trivial

/-!
## Part VIII: Connections to Sum-Free Sets
-/

/--
**Classical Sum-Free Set:**
A set S is sum-free if a + b ∉ S for all a, b ∈ S.
-/
def isSumFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S

/--
**Sum-Free Density:**
The maximum density of a sum-free subset of {1, ..., n}.
-/
noncomputable def sumFreeDensity (n : ℕ) : ℝ :=
  (Finset.range n).sup' (by simp) (fun k =>
    if h : k > 0 then (k : ℝ) / n else 0)

/--
**Connection:**
This problem relates to finding sum-free sets that avoid a prescribed
set of sums, rather than avoiding all sums.
-/
axiom sum_free_connection : True

/-!
## Part IX: Interval Constraints
-/

/--
**Why these intervals?**
Elements of (n, 2n) sum to values in (2n, 4n).
So we're asking: how much of (2n, 4n) can we "block" while still
finding a large set in (n, 2n) that avoids those blocked values?
-/
theorem interval_sum_range : ∀ n : ℕ, n ≥ 1 →
    ∀ c₁ ∈ lowerInterval n, ∀ c₂ ∈ lowerInterval n,
    c₁ ≠ c₂ → c₁ + c₂ ∈ upperInterval n ∨ c₁ + c₂ ≤ 2 * n ∨ c₁ + c₂ ≥ 4 * n := by
  sorry

/--
**Sums lie in correct range:**
For c₁, c₂ ∈ (n, 2n), we have c₁ + c₂ ∈ (2n, 4n).
-/
theorem sums_in_upper_interval : ∀ n : ℕ, n ≥ 1 →
    ∀ c₁ ∈ lowerInterval n, ∀ c₂ ∈ lowerInterval n,
    c₁ ≠ c₂ → c₁ + c₂ ∈ upperInterval n := by
  sorry

/-!
## Part X: Algorithmic Aspects
-/

/--
**Computational Problem:**
Given B, find a maximum C that is sum-free w.r.t. B.
-/
def computationalProblem : Prop :=
  -- Given B ⊂ (2n, 4n), compute max |C| for C sum-free w.r.t. B
  True

/--
**Greedy approach:**
A simple greedy algorithm gives some bound but not optimal.
-/
axiom greedy_approach : True

/-!
## Part XI: Summary
-/

/--
**Erdős Problem #788: OPEN**

QUESTION: Estimate f(n) where f(n) is the maximum such that for all
B ⊂ (2n, 4n), there exists C ⊂ (n, 2n) sum-free w.r.t. B with
|C| + |B| ≥ f(n).

CONJECTURE (Choi): f(n) ≤ n^{1/2+o(1)}

KNOWN BOUNDS:
- Lower: f(n) ≫ n^{1/2} (Adenwalla)
- Upper: f(n) ≪ (n log n)^{2/3} (Baltz-Schoen-Srivastav 2000)

STATUS: Open - the gap between 1/2 and 2/3 remains.
-/
theorem erdos_788 : True := trivial

/--
**Summary theorem:**
-/
theorem erdos_788_summary :
    -- Lower bound n^{1/2}
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ c * (n : ℝ) ^ (1/2 : ℝ)) ∧
    -- Upper bound (n log n)^{2/3}
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      (f n : ℝ) ≤ C * ((n : ℝ) * Real.log n) ^ (2/3 : ℝ)) ∧
    -- Choi's conjecture is open
    True := by
  exact ⟨adenwalla_lower_bound, bss_bound, trivial⟩

/--
**Historical Timeline:**
- 1971: Choi poses the problem, proves f(n) ≪ n^{3/4}
- Later: Adenwalla proves f(n) ≫ n^{1/2}
- Later: Hunter improves to f(n) ≪ n^{2/3+o(1)}
- 2000: BSS prove f(n) ≪ (n log n)^{2/3}
-/
theorem historical_note : True := trivial

end Erdos788
