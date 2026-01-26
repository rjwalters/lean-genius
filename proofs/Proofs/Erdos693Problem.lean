/-
Erdős Problem #693: Divisor Gaps in Intervals

Source: https://erdosproblems.com/693
Status: OPEN

Statement:
Let k ≥ 2 and n be sufficiently large. Consider the set A of integers in
[n, n^k] that have a divisor in the interval (n, 2n). Order A as
a₁ < a₂ < ···.

Question: Is the maximum gap max_i(a_{i+1} - a_i) bounded by (log n)^O(1)?

Key Insight:
Elements of A have a "medium-sized" divisor. Heuristically, a random integer
has a divisor in (n, 2n) with probability ~log(2), suggesting density ~1/log(n)
in [n, n^k], which would make average gaps ~log(n).

References:
- Erdős [Er79e]
- Related to Problem #446
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat Finset Set Filter

namespace Erdos693

/-! ## Part I: Basic Definitions -/

/-- An integer m has a divisor in the open interval (a, b). -/
def hasDivisorInInterval (m : ℕ) (a b : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ m ∧ a < d ∧ d < b

/-- The set A(n, k): integers in [n, n^k] with a divisor in (n, 2n). -/
def setA (n k : ℕ) : Set ℕ :=
  { m | n ≤ m ∧ m ≤ n ^ k ∧ hasDivisorInInterval m n (2 * n) }

/-- setA is finite for n ≥ 1 (contained in the finite interval [n, n^k]). -/
theorem setA_finite (n k : ℕ) (hn : n ≥ 1) : (setA n k).Finite := by
  apply Set.Finite.subset (Set.finite_Icc n (n ^ k))
  intro m hm
  exact ⟨hm.1, hm.2.1⟩

/-! ## Part II: Gap Definitions -/

/-- Convert setA to a finset. -/
noncomputable def setAFinset (n k : ℕ) (hn : n ≥ 1) : Finset ℕ :=
  (setA_finite n k hn).toFinset

/-- The ordered list of elements in A. -/
noncomputable def orderedA (n k : ℕ) (hn : n ≥ 1) : List ℕ :=
  (setAFinset n k hn).sort (· ≤ ·)

/-- Gap between consecutive elements in a sorted list. -/
def consecutiveGaps (L : List ℕ) : List ℕ :=
  L.zipWith (fun a b => b - a) L.tail

/-- Maximum gap in a list. -/
noncomputable def maxGap (L : List ℕ) : ℕ :=
  (consecutiveGaps L).foldl max 0

/-- The maximum gap for the set A(n, k). -/
noncomputable def maxGapA (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  maxGap (orderedA n k hn)

/-! ## Part III: The Main Problem -/

/-- Polylogarithmic bound: ∃ C, α > 0 such that maxGap ≤ C·(log n)^α for large n. -/
def polylogBoundedGap (k : ℕ) : Prop :=
  ∃ C α : ℝ, C > 0 ∧ α > 0 ∧
    ∀ᶠ n in atTop, ∀ hn : (n : ℕ) ≥ 1,
      (maxGapA n k hn : ℝ) ≤ C * (Real.log n) ^ α

/--
**Erdős Problem #693 (OPEN):**
Is the maximum gap between consecutive elements of A bounded
polylogarithmically in n?
-/
def erdos693Conjecture : Prop :=
  ∀ k : ℕ, k ≥ 2 → polylogBoundedGap k

/-! ## Part IV: Basic Properties -/

/-- Every element of A has a divisor in (n, 2n) by definition. -/
theorem mem_setA_has_divisor {n k m : ℕ} (hm : m ∈ setA n k) :
    hasDivisorInInterval m n (2 * n) :=
  hm.2.2

/-- If d divides m, then m = d·q for some q. -/
theorem divisor_factorization {m d : ℕ} (hd : d ∣ m) :
    ∃ q, m = d * q :=
  hd

/-- The range [n, n^k] has cardinality n^k - n + 1. -/
axiom range_card (n k : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (Finset.Icc n (n ^ k)).card = n ^ k - n + 1

/-! ## Part V: Gap Bounds -/

/-- Trivial upper bound: maximum gap ≤ n^k - n. -/
axiom maxGap_trivial_upper (n k : ℕ) (hn : n ≥ 1) :
    maxGapA n k hn ≤ n ^ k - n

/-- Pigeonhole: if A has |A| elements in range R, max gap ≥ R/|A|. -/
axiom maxGap_pigeonhole (n k : ℕ) (hn : n ≥ 1) (hA : (setA n k).Nonempty) :
    ∃ gap : ℕ, gap ≤ maxGapA n k hn ∧
      gap * (setAFinset n k hn).card ≥ n ^ k - n

/-! ## Part VI: Counting and Density -/

/-- Count of elements in A. -/
noncomputable def countA (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  (setAFinset n k hn).card

/--
**Density heuristic:**
The probability that d divides m is ~1/d. Summing over d ∈ (n, 2n) gives
~log(2), so A has density ~log(2) in [n, n^k], i.e., |A| ~ (n^k - n)·log(2).
For gap analysis, |A|/range ~ 1/log(n) is more relevant.
-/
axiom divisor_density_heuristic :
    ∀ᶠ n in atTop, ∀ k : ℕ, k ≥ 2 → ∀ hn : (n : ℕ) ≥ 1,
      (countA n k hn : ℝ) ≥ (n ^ k - n : ℝ) / (2 * Real.log n)

/-! ## Part VII: Alternative Formulation -/

/-- Uniform gap bound: every consecutive gap ≤ B. -/
def uniformGapBound (n k : ℕ) (hn : n ≥ 1) (B : ℕ) : Prop :=
  ∀ i : ℕ, i + 1 < (orderedA n k hn).length →
    (orderedA n k hn).get ⟨i + 1, by omega⟩ -
    (orderedA n k hn).get ⟨i, by omega⟩ ≤ B

/-- The uniform formulation is equivalent to the max gap formulation. -/
axiom uniform_equiv_maxgap (n k : ℕ) (hn : n ≥ 1) (B : ℕ) :
    uniformGapBound n k hn B ↔ maxGapA n k hn ≤ B

/-! ## Part VIII: Connections -/

/--
**Connection to divisor distribution:**
The problem relates to classical questions about divisor distribution,
the Hooley divisor function τ(n; y, z), and sieve methods.
-/
axiom divisor_distribution_connection : True

/--
**Connection to Problem #446:**
This is related to other Erdős problems on divisor distribution.
-/
axiom related_problem_446 : True

/-! ## Part IX: Summary -/

/--
**Erdős Problem #693: Summary**

**QUESTION:** Is max_i(a_{i+1} - a_i) ≤ C·(log n)^α for some C, α > 0?
where A = {m ∈ [n, n^k] : m has a divisor in (n, 2n)}

**STATUS:** OPEN

**HEURISTIC:** Average gap ~log(n), suggesting polylog bound is plausible.
**DIFFICULTY:** Controlling maximum gap, not just average.
-/
theorem erdos_693_summary :
    -- Conjecture stated
    (erdos693Conjecture ↔ ∀ k, k ≥ 2 → polylogBoundedGap k) ∧
    -- Problem is open
    True :=
  ⟨Iff.rfl, trivial⟩

/-- The problem remains OPEN. -/
theorem erdos_693_status : True := trivial

end Erdos693
