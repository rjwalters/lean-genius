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
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Nat Finset Set Filter

namespace Erdos693

/- ## Part I: Basic Definitions -/

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

/-- setA is a subset of Set.Icc n (n^k). -/
theorem setA_subset_Icc (n k : ℕ) : setA n k ⊆ Set.Icc n (n ^ k) :=
  fun m hm => ⟨hm.1, hm.2.1⟩

/-- Every element of A is at least n. -/
theorem setA_lower_bound {n k m : ℕ} (hm : m ∈ setA n k) : n ≤ m :=
  hm.1

/-- Every element of A is at most n^k. -/
theorem setA_upper_bound {n k m : ℕ} (hm : m ∈ setA n k) : m ≤ n ^ k :=
  hm.2.1

/- ## Part II: Gap Definitions -/

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

/- ## Part III: The Main Problem -/

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

/- ## Part IV: Basic Properties -/

/-- Every element of A has a divisor in (n, 2n) by definition. -/
theorem mem_setA_has_divisor {n k m : ℕ} (hm : m ∈ setA n k) :
    hasDivisorInInterval m n (2 * n) :=
  hm.2.2

/-- If d divides m, then m = d·q for some q. -/
theorem divisor_factorization {m d : ℕ} (hd : d ∣ m) :
    ∃ q, m = d * q :=
  hd

/-- The range [n, n^k] has cardinality n^k - n + 1. -/
theorem range_card (n k : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (Finset.Icc n (n ^ k)).card = n ^ k - n + 1 := by
  rw [Finset.card_Icc]
  omega

/-- For k ≥ 1 and n ≥ 1, we have n ≤ n^k. -/
theorem le_pow_of_ge_one {n k : ℕ} (hn : n ≥ 1) (hk : k ≥ 1) : n ≤ n ^ k := by
  calc n = n ^ 1 := (pow_one n).symm
    _ ≤ n ^ k := Nat.pow_le_pow_right hn hk

/-- setA is contained in the Finset.Icc. -/
theorem setAFinset_subset_Icc (n k : ℕ) (hn : n ≥ 1) :
    setAFinset n k hn ⊆ Finset.Icc n (n ^ k) := by
  intro m hm
  rw [Finset.mem_Icc]
  have hm' := (setA_finite n k hn).mem_toFinset.mp hm
  exact ⟨hm'.1, hm'.2.1⟩

/-- setA has at most n^k - n + 1 elements. -/
theorem setA_card_le (n k : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (setAFinset n k hn).card ≤ n ^ k - n + 1 := by
  calc (setAFinset n k hn).card
      ≤ (Finset.Icc n (n ^ k)).card := Finset.card_le_card (setAFinset_subset_Icc n k hn)
    _ = n ^ k - n + 1 := range_card n k hn hk

/- ## Part V: Membership Witnesses -/

/-- n·(n+1) is in setA when k ≥ 2 and n ≥ 2, since n+1 divides it and n < n+1 < 2n. -/
theorem mem_setA_of_n_mul_succ {n k : ℕ} (hn : n ≥ 2) (hk : k ≥ 2) :
    n * (n + 1) ∈ setA n k := by
  refine ⟨?_, ?_, ?_⟩
  · calc n = n * 1 := (mul_one n).symm
      _ ≤ n * (n + 1) := Nat.mul_le_mul_left n (by omega)
  · calc n * (n + 1) ≤ n * (n * n) := by nlinarith
      _ = n ^ 3 := by ring
      _ ≤ n ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  · exact ⟨n + 1, ⟨n, rfl⟩, by omega, by omega⟩

/-- For n ≥ 2, k ≥ 2, setA is nonempty. -/
theorem setA_nonempty {n k : ℕ} (hn : n ≥ 2) (hk : k ≥ 2) : (setA n k).Nonempty :=
  ⟨n * (n + 1), mem_setA_of_n_mul_succ hn hk⟩

/- ## Part VI: Gap Bounds -/

/-- Trivial upper bound: maximum gap ≤ n^k - n. -/
theorem maxGap_trivial_upper (n k : ℕ) (hn : n ≥ 1) :
    maxGapA n k hn ≤ n ^ k - n := by sorry

/-- Pigeonhole: if A has |A| elements in range R, max gap ≥ R/|A|. -/
theorem maxGap_pigeonhole (n k : ℕ) (hn : n ≥ 1) (hA : (setA n k).Nonempty) :
    ∃ gap : ℕ, gap ≤ maxGapA n k hn ∧
      gap * (setAFinset n k hn).card ≥ n ^ k - n := by sorry

/- ## Part VII: Counting and Density -/

/-- Count of elements in A. -/
noncomputable def countA (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  (setAFinset n k hn).card

/--
**Density heuristic:**
The probability that d divides m is ~1/d. Summing over d ∈ (n, 2n) gives
~log(2), so A has density ~log(2) in [n, n^k], i.e., |A| ~ (n^k - n)·log(2).
For gap analysis, |A|/range ~ 1/log(n) is more relevant.
-/
theorem divisor_density_heuristic :
    ∀ᶠ n in atTop, ∀ k : ℕ, k ≥ 2 → ∀ hn : (n : ℕ) ≥ 1,
      (countA n k hn : ℝ) ≥ (n ^ k - n : ℝ) / (2 * Real.log n) := by sorry

/- ## Part VIII: Alternative Formulation -/

/-- Maximum gap as supremum over consecutive differences. -/
def maxConsecDiff (n k : ℕ) (hn : n ≥ 1) : ℕ :=
  let L := orderedA n k hn
  maxGap L

/-- The polylog conjecture restated: for each k ≥ 2, the max gap grows at most polylogarithmically. -/
theorem polylog_restatement :
    erdos693Conjecture ↔
      ∀ k : ℕ, k ≥ 2 →
        ∃ C α : ℝ, C > 0 ∧ α > 0 ∧
          ∀ᶠ n in atTop, ∀ hn : (n : ℕ) ≥ 1,
            (maxGapA n k hn : ℝ) ≤ C * (Real.log n) ^ α :=
  Iff.rfl

/- ## Part IX: Connections -/

/-
**Connection to divisor distribution:**
The problem relates to classical questions about divisor distribution,
the Hooley divisor function τ(n; y, z), and sieve methods.
It is also related to Erdős Problem #446 on divisor distribution.
-/

/- ## Part X: Summary -/

/--
**Erdős Problem #693: Summary**

**QUESTION:** Is max_i(a_{i+1} - a_i) ≤ C·(log n)^α for some C, α > 0?
where A = {m ∈ [n, n^k] : m has a divisor in (n, 2n)}

**STATUS:** OPEN

**HEURISTIC:** Average gap ~log(n), suggesting polylog bound is plausible.
**DIFFICULTY:** Controlling maximum gap, not just average.
-/
theorem erdos_693_summary :
    erdos693Conjecture ↔ ∀ k, k ≥ 2 → polylogBoundedGap k :=
  Iff.rfl

end Erdos693
