/-
Erdős Problem #441: LCM-Bounded Subsets

Source: https://erdosproblems.com/441
Status: SOLVED (Chen-Dai, 2006-2007)

Statement:
Let N ≥ 1. What is the size of the largest A ⊆ {1,...,N} such that
[a,b] ≤ N for all a,b ∈ A, where [a,b] is the least common multiple?

Is the maximum attained by choosing all integers in [1, (N/2)^{1/2}]
together with all even integers in [(N/2)^{1/2}, (2N)^{1/2}]?

Answer: NO - Erdős' construction is not always optimal.

Let g(N) denote the maximum size. Known results:
- Lower: g(N) ≥ (9N/8)^{1/2} + O(1) (Erdős' construction)
- Upper: g(N) ≤ (9N/8)^{1/2} + O((N/log N)^{1/2} · log log N) (Chen-Dai)
- Asymptotic: g(N) ~ (9N/8)^{1/2} (Chen 1998)
- Erdős' construction is NOT optimal for infinitely many N (Chen-Dai 2006)

References:
- [Er51b] Erdős (1951) - Original problem
- [Ch72b] Choi (1972) - Early results
- [Ch98] Chen (1998) - Asymptotic formula
- [DaCh06] Dai-Chen (2006) - Showed construction is not optimal
- [ChDa07] Chen-Dai (2007) - Refined upper bound

Tags: number-theory, lcm, extremal-combinatorics, solved
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Nat Real Finset

namespace Erdos441

/-!
## Part 1: Basic Definitions
-/

/-- A subset of {1,...,N} -/
def IsSubsetOfInterval (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- All pairwise LCMs are at most N -/
def HasBoundedLCM (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → Nat.lcm a b ≤ N

/-- An LCM-bounded subset: A ⊆ {1,...,N} with [a,b] ≤ N for all a,b ∈ A -/
def IsLCMBounded (A : Finset ℕ) (N : ℕ) : Prop :=
  IsSubsetOfInterval A N ∧ HasBoundedLCM A N

/-- g(N): Maximum size of an LCM-bounded subset of {1,...,N} -/
noncomputable def g (N : ℕ) : ℕ :=
  sSup {A.card | A : Finset ℕ, IsLCMBounded A N}

/-!
## Part 2: Erdős' Proposed Construction
-/

/-- The first part of Erdős' construction: all integers in [1, (N/2)^{1/2}] -/
def ErdosFirstPart (N : ℕ) : Finset ℕ :=
  (Finset.range (Nat.sqrt (N / 2) + 1)).filter (· ≥ 1)

/-- The second part: even integers in [(N/2)^{1/2}, (2N)^{1/2}] -/
def ErdosSecondPart (N : ℕ) : Finset ℕ :=
  ((Finset.range (Nat.sqrt (2 * N) + 1)).filter (· ≥ Nat.sqrt (N / 2))).filter (fun x => x % 2 = 0)

/-- Erdős' full construction -/
def ErdosConstruction (N : ℕ) : Finset ℕ :=
  ErdosFirstPart N ∪ ErdosSecondPart N

/-- Erdős' construction gives an LCM-bounded set -/
axiom erdos_construction_valid :
  ∀ N : ℕ, N ≥ 1 → IsLCMBounded (ErdosConstruction N) N

/-- Size of Erdős' construction: approximately (9N/8)^{1/2} -/
axiom erdos_construction_size :
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
    |(ErdosConstruction N).card - Real.sqrt ((9 : ℝ) * N / 8)| ≤ C

/-!
## Part 3: The Main Question
-/

/-- Erdős' original question: Is his construction optimal? -/
def ErdosQuestion : Prop :=
  ∀ N : ℕ, N ≥ 1 → g N = (ErdosConstruction N).card

/-- The answer is NO: the construction is not always optimal -/
theorem erdos_question_answer : ¬ErdosQuestion := by
  -- Chen and Dai (2006) showed the construction is not optimal
  -- for infinitely many N
  sorry

/-!
## Part 4: Lower Bounds
-/

/-- Lower bound: g(N) ≥ (9N/8)^{1/2} - O(1) -/
def LowerBound : Prop :=
  ∃ C : ℝ, ∀ N : ℕ, N ≥ 1 →
    (g N : ℝ) ≥ Real.sqrt ((9 : ℝ) * N / 8) - C

/-- Erdős' construction establishes the lower bound -/
axiom lower_bound_holds : LowerBound

/-- The construction gives g(N) ≥ (9N/8)^{1/2} + O(1) -/
theorem construction_gives_lower_bound (N : ℕ) (hN : N ≥ 1) :
    (g N : ℝ) ≥ (ErdosConstruction N).card := by
  -- The construction is valid, so g(N) ≥ its size
  sorry

/-!
## Part 5: Upper Bounds
-/

/-- Chen's asymptotic (1998): g(N) ~ (9N/8)^{1/2} -/
def ChenAsymptotic : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |(g N : ℝ) / Real.sqrt ((9 : ℝ) * N / 8) - 1| < ε

/-- Chen's theorem (1998): Established the asymptotic formula -/
axiom chen_1998 : ChenAsymptotic

/-- Chen-Dai upper bound (2007): g(N) ≤ (9N/8)^{1/2} + O((N/log N)^{1/2} · log log N) -/
def ChenDaiUpperBound : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 3 →
    (g N : ℝ) ≤ Real.sqrt ((9 : ℝ) * N / 8) +
      C * Real.sqrt (N / Real.log N) * Real.log (Real.log N)

/-- Chen and Dai's theorem (2007): Refined upper bound -/
axiom chen_dai_2007 : ChenDaiUpperBound

/-!
## Part 6: The Construction is Not Optimal
-/

/-- There exist infinitely many N where Erdős' construction is not optimal -/
def ConstructionNotOptimal : Prop :=
  ∀ M : ℕ, ∃ N > M, g N > (ErdosConstruction N).card

/-- Chen-Dai (2006): Proved the construction is not optimal for infinitely many N -/
axiom chen_dai_2006 : ConstructionNotOptimal

/-- Corollary: Erdős' original question has a negative answer -/
theorem erdos_question_disproved :
    ConstructionNotOptimal → ¬ErdosQuestion := by
  intro hNotOpt hOpt
  -- If construction is always optimal, it can't fail for any N
  obtain ⟨N, hN_pos, hN_strict⟩ := hNotOpt 0
  have hN_ge : N ≥ 1 := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN_pos)
  have := hOpt N hN_ge
  omega

/-!
## Part 7: Why the Construction Fails
-/

/-- The structure of optimal sets can differ from Erdős' pattern -/
axiom optimal_sets_structure :
  -- For some N, the optimal set has different structure
  -- May include different combinations of integers
  True

/-- The error term in Chen-Dai bound shows room for improvement -/
axiom error_term_significance :
  -- The O((N/log N)^{1/2} · log log N) term is not O(1)
  -- This leaves room for the construction to be suboptimal
  True

/-!
## Part 8: Special Cases
-/

/-- For small N, exact values of g(N) can be computed -/
axiom small_cases :
  -- g(1) = 1: only {1} works
  -- g(2) = 2: {1, 2} works
  -- g(6) = 3: {1, 2, 3} works (since lcm(2,3) = 6)
  True

/-- The set {1, 2, ..., k} is LCM-bounded for N = lcm(1,...,k) -/
axiom consecutive_integers :
  -- For N = lcm(1, 2, ..., k), the set {1, 2, ..., k} works
  True

/-!
## Part 9: Related Results
-/

/-- Connection to primitive sequences -/
axiom primitive_sequence_connection :
  -- A is primitive if no element divides another
  -- LCM-bounded sets have connections to primitive sequences
  True

/-- Connection to density questions -/
axiom density_connection :
  -- The asymptotic g(N) ~ (9N/8)^{1/2} implies
  -- LCM-bounded sets have density ~N^{-1/2}
  True

/-- Choi's earlier work (1972) -/
axiom choi_1972 :
  -- Choi studied related questions about LCM constraints
  True

/-!
## Part 10: The Constant 9/8
-/

/-- Why 9/8 appears in the asymptotic -/
axiom why_nine_eighths :
  -- From Erdős' construction:
  -- First part: integers in [1, (N/2)^{1/2}] ≈ (N/2)^{1/2}
  -- Second part: even integers in [(N/2)^{1/2}, (2N)^{1/2}] ≈ (1/2)((2N)^{1/2} - (N/2)^{1/2})
  -- Total ≈ (N/2)^{1/2} + (1/2)((2N)^{1/2} - (N/2)^{1/2})
  --      = (1/2)(N/2)^{1/2} + (1/2)(2N)^{1/2}
  --      = (1/2)N^{1/2}(1/√2 + √2)
  --      = (1/2)N^{1/2} · (3/√2)
  --      = (3/(2√2))N^{1/2}
  --      = (9/8)^{1/2} · N^{1/2}
  True

/-- The constant (9/8)^{1/2} = 3/(2√2) ≈ 1.061 -/
theorem constant_value :
    Real.sqrt ((9 : ℝ) / 8) = 3 / (2 * Real.sqrt 2) := by
  rw [Real.sqrt_div_self', Real.sqrt_eq_iff_sq_eq]
  · ring_nf
    norm_num
  · norm_num
  · norm_num

/-!
## Part 11: Summary
-/

/-- Erdős Problem #441 is SOLVED -/
theorem erdos_441_solved :
    ChenAsymptotic ∧ ChenDaiUpperBound ∧ ConstructionNotOptimal := by
  exact ⟨chen_1998, chen_dai_2007, chen_dai_2006⟩

/-- **Erdős Problem #441: SOLVED**

QUESTION: Find the maximum size g(N) of A ⊆ {1,...,N} with [a,b] ≤ N for all a,b ∈ A.
Is Erdős' construction (integers up to (N/2)^{1/2} plus even integers in
[(N/2)^{1/2}, (2N)^{1/2}]) optimal?

ANSWER: NO - The construction is not always optimal.

ASYMPTOTIC: g(N) ~ (9N/8)^{1/2}

BOUNDS:
- Lower: g(N) ≥ (9N/8)^{1/2} - O(1) (Erdős' construction)
- Upper: g(N) ≤ (9N/8)^{1/2} + O((N/log N)^{1/2} · log log N) (Chen-Dai)

KEY RESULT: For infinitely many N, g(N) > |Erdős' construction| (Chen-Dai 2006)
-/
theorem erdos_441_summary :
    -- Asymptotic is known
    ChenAsymptotic →
    -- Construction is not always optimal
    ConstructionNotOptimal →
    -- So the answer to Erdős' specific question is NO
    ¬ErdosQuestion := by
  intro _ hNotOpt
  exact erdos_question_disproved hNotOpt

/-- Problem status -/
def erdos_441_status : String :=
  "SOLVED - g(N) ~ (9N/8)^{1/2}, but Erdős' construction is not always optimal"

end Erdos441
