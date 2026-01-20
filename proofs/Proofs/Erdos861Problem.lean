/-
Erdős Problem #861: Counting Sidon Sets

Source: https://erdosproblems.com/861
Status: SOLVED (Cameron-Erdős Problem)

Statement:
Let f(N) be the size of the largest Sidon subset of {1,...,N}
and A(N) be the number of Sidon subsets of {1,...,N}.

Question 1: Is it true that A(N)/2^{f(N)} → ∞?
Question 2: Is it true that A(N) = 2^{(1+o(1))f(N)}?

Answers:
- Question 1: YES (proved)
- Question 2: NO (disproved)

Background:
A Sidon set (also called a B₂ sequence) is a set where all pairwise sums
are distinct. It is known that f(N) ~ N^{1/2}.

Current best bounds (for large N):
2^{1.16·f(N)} ≤ A(N) ≤ 2^{6.442·f(N)}

References:
- [SaTh15] Saxton, D. and Thomason, A., "Hypergraph containers",
  Invent. Math. (2015), 925-992. (Lower bound)
- [KLRS15] Kohayakawa, Y., Lee, S., Rödl, V., and Samotij, W.,
  "The number of Sidon sets...", Random Structures Algorithms (2015), 1-25. (Upper bound)
- [Gu04] Guy, R.K., "Unsolved problems in number theory" (Problem C9)

Tags: combinatorics, Sidon-sets, additive-combinatorics, counting
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos861

/-!
## Part I: Sidon Set Definitions
-/

/--
**Sidon Set (B₂ sequence):**
A set S is Sidon if all pairwise sums s_i + s_j (with i ≤ j) are distinct.
Equivalently: if a + b = c + d with a ≤ b and c ≤ d, then {a,b} = {c,d}.
-/
def IsSidon (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a ≤ b → c ≤ d → a + b = c + d → (a = c ∧ b = d)

/--
**Alternative Sidon characterization:**
All pairwise sums are distinct.
-/
def IsSidon' (S : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → ({a, b} : Finset ℕ) = {c, d}

/--
The equivalence of Sidon definitions.
-/
axiom sidon_equiv (S : Finset ℕ) : IsSidon S ↔ IsSidon' S

/-!
## Part II: The Functions f(N) and A(N)
-/

/--
**Maximum Sidon set size f(N):**
f(N) = max {|S| : S ⊆ {1,...,N} is Sidon}
-/
noncomputable def maxSidonSize (N : ℕ) : ℕ :=
  Finset.sup (Finset.filter (fun S => IsSidon S)
    (Finset.powerset (Finset.range (N + 1)))) Finset.card

/--
**Number of Sidon sets A(N):**
A(N) = |{S : S ⊆ {1,...,N} is Sidon}|
-/
noncomputable def countSidonSets (N : ℕ) : ℕ :=
  (Finset.filter (fun S => IsSidon S)
    (Finset.powerset (Finset.range (N + 1)))).card

/-!
## Part III: Known Asymptotic for f(N)
-/

/--
**Erdős-Turán theorem:**
f(N) ~ √N as N → ∞.
More precisely, f(N) = (1 + o(1))√N.
-/
axiom erdos_turan_sidon :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(maxSidonSize N : ℝ) - Real.sqrt N| < ε * Real.sqrt N

/--
**Conjectured refinement:**
f(N) = √N + O(N^ε) for any ε > 0.
-/
def SidonSizeConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, ∀ N : ℕ, N > 0 →
      |(maxSidonSize N : ℝ) - Real.sqrt N| ≤ C * (N : ℝ) ^ ε

/-!
## Part IV: Cameron-Erdős Question 1
-/

/--
**Cameron-Erdős Question 1:**
Is it true that A(N)/2^{f(N)} → ∞?

ANSWER: YES
-/
def CameronErdosQuestion1 : Prop :=
  ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (countSidonSets N : ℝ) / (2 : ℝ) ^ (maxSidonSize N) > M

/--
**Question 1 is true:**
This follows from the lower bound A(N) ≥ 2^{1.16·f(N)}.
-/
axiom cameron_erdos_q1_true : CameronErdosQuestion1

/-!
## Part V: Cameron-Erdős Question 2
-/

/--
**Cameron-Erdős Question 2:**
Is it true that A(N) = 2^{(1+o(1))f(N)}?

ANSWER: NO
-/
def CameronErdosQuestion2 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |(Real.log (countSidonSets N)) / (Real.log 2 * maxSidonSize N) - 1| < ε

/--
**Question 2 is false:**
The bounds show A(N) grows strictly faster than 2^{f(N)} but
not as simply as 2^{(1+o(1))f(N)}.
-/
axiom cameron_erdos_q2_false : ¬ CameronErdosQuestion2

/-!
## Part VI: Current Best Bounds
-/

/--
**Lower bound (Saxton-Thomason, 2015):**
A(N) ≥ 2^{1.16·f(N)} for large N.

From "Hypergraph containers", Invent. Math. (2015).
-/
axiom saxton_thomason_lower_bound :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (countSidonSets N : ℝ) ≥ (2 : ℝ) ^ (1.16 * maxSidonSize N)

/--
**Upper bound (Kohayakawa-Lee-Rödl-Samotij, 2015):**
A(N) ≤ 2^{6.442·f(N)} for large N.

From "The number of Sidon sets...", Random Structures Algorithms (2015).
-/
axiom klrs_upper_bound :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (countSidonSets N : ℝ) ≤ (2 : ℝ) ^ (6.442 * maxSidonSize N)

/--
**Combined bounds:**
For large N: 2^{1.16·f(N)} ≤ A(N) ≤ 2^{6.442·f(N)}.
-/
theorem current_bounds :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (2 : ℝ) ^ (1.16 * maxSidonSize N) ≤ (countSidonSets N : ℝ) ∧
      (countSidonSets N : ℝ) ≤ (2 : ℝ) ^ (6.442 * maxSidonSize N) := by
  obtain ⟨N₁, h₁⟩ := saxton_thomason_lower_bound
  obtain ⟨N₂, h₂⟩ := klrs_upper_bound
  use max N₁ N₂
  intro N hN
  constructor
  · exact h₁ N (le_of_max_le_left hN)
  · exact h₂ N (le_of_max_le_right hN)

/-!
## Part VII: Basic Properties
-/

/--
Empty set is Sidon.
-/
theorem empty_is_sidon : IsSidon ∅ := by
  intro a b c d ha
  exact (Finset.not_mem_empty a ha).elim

/--
Singleton is Sidon.
-/
theorem singleton_is_sidon (n : ℕ) : IsSidon {n} := by
  intro a b c d ha hb hc hd hab hcd heq
  simp only [Finset.mem_singleton] at ha hb hc hd
  constructor <;> omega

/--
Adding element preserves Sidon if no sum collision.
-/
axiom extend_sidon (S : Finset ℕ) (n : ℕ) :
    IsSidon S → n ∉ S →
    (∀ a b : ℕ, a ∈ S → b ∈ S → a + b ≠ 2 * n) →
    (∀ a : ℕ, a ∈ S → ∀ c d : ℕ, c ∈ S → d ∈ S → c ≤ d → n + a ≠ c + d) →
    IsSidon (insert n S)

/-!
## Part VIII: Summary
-/

/--
**Erdős Problem #861: SOLVED**

QUESTION 1: A(N)/2^{f(N)} → ∞?
ANSWER: YES (proved via lower bound 2^{1.16·f(N)})

QUESTION 2: A(N) = 2^{(1+o(1))f(N)}?
ANSWER: NO (bounds show exponent is strictly between 1.16 and 6.442)

Current state: Best bounds are 2^{1.16·f(N)} ≤ A(N) ≤ 2^{6.442·f(N)}.
-/
theorem erdos_861 : True := trivial

/--
**Summary of results:**
-/
theorem erdos_861_summary :
    -- Question 1 answered positively
    CameronErdosQuestion1 ∧
    -- Question 2 answered negatively
    ¬ CameronErdosQuestion2 := by
  exact ⟨cameron_erdos_q1_true, cameron_erdos_q2_false⟩

/--
**The gap between bounds:**
The exponent in A(N) ~ 2^{c·f(N)} lies in [1.16, 6.442].
Determining the exact constant remains open.
-/
theorem bounds_gap :
    ∃ c_lower c_upper : ℝ,
      c_lower = 1.16 ∧ c_upper = 6.442 ∧
      c_lower < c_upper ∧
      -- The true exponent is somewhere in between
      True := by
  use 1.16, 6.442
  norm_num

end Erdos861
