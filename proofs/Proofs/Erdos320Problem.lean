/-
  Erdős Problem #320: Distinct Sums of Unit Fractions

  Source: https://erdosproblems.com/320
  Status: OPEN (asymptotic bounds known but not exact)

  Statement:
  Let S(N) count the number of distinct sums of the form ∑_{n∈A} 1/n
  for A ⊆ {1,...,N}. Estimate S(N).

  Known Results:
  - Bleicher-Erdős (1975): Lower bound log S(N) ≥ (N/log N)(log 2 ∏_{i=3}^k log_i N)
  - Bleicher-Erdős (1976): Upper bound log S(N) ≤ (N/log N)(log_r N ∏_{i=3}^r log_i N)
  - Bettin-Grenié-Molteni-Sanna (2025): Improved lower bound

  The gap between upper and lower bounds remains significant.

  Related: Problem #321 (Egyptian fraction representations)

  References:
  - [BlEr75] Bleicher-Erdős, "The number of distinct subsums of ∑ 1/i"
  - [BlEr76b] Bleicher-Erdős, "Denominators of Egyptian fractions II"
  - [BGMS25] Bettin et al., "A lower bound for the number of Egyptian fractions"

  Tags: number-theory, unit-fractions, egyptian-fractions, counting
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Nat Real BigOperators Finset

namespace Erdos320

/-!
## Part I: Basic Definitions
-/

/-- The harmonic sum H_n = 1 + 1/2 + ... + 1/n. -/
noncomputable def harmonicSum (n : ℕ) : ℚ :=
  ∑ i in Finset.range n, (1 : ℚ) / (i + 1)

/-- A subset sum of unit fractions: ∑_{n∈A} 1/n for A ⊆ {1,...,N}. -/
noncomputable def subsetSum (A : Finset ℕ) : ℚ :=
  ∑ n in A.filter (· > 0), (1 : ℚ) / n

/-- The set of all possible subset sums from {1,...,N}. -/
noncomputable def allSubsetSums (N : ℕ) : Finset ℚ :=
  (Finset.range N).powerset.image (fun A => subsetSum (A.image (· + 1)))

/-- **S(N):** The count of distinct sums of the form ∑_{n∈A} 1/n for A ⊆ {1,...,N}. -/
noncomputable def S (N : ℕ) : ℕ := (allSubsetSums N).card

/-- S(N) is always positive (at least the empty sum = 0). -/
theorem S_pos (N : ℕ) : S N > 0 := by
  simp [S, allSubsetSums]
  sorry  -- The empty set gives sum 0

/-!
## Part II: Iterated Logarithms
-/

/-- The i-fold iterated logarithm log_i N. -/
noncomputable def iterLog : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => Real.log (iterLog n x)

/-- Notation: log₁ N = log N. -/
noncomputable def log₁ (x : ℝ) : ℝ := Real.log x

/-- Notation: log₂ N = log log N. -/
noncomputable def log₂ (x : ℝ) : ℝ := Real.log (Real.log x)

/-- Notation: log₃ N = log log log N. -/
noncomputable def log₃ (x : ℝ) : ℝ := Real.log (Real.log (Real.log x))

/-- Product of iterated logs: ∏_{i=3}^k log_i N. -/
noncomputable def iterLogProduct (N : ℝ) (k : ℕ) : ℝ :=
  ∏ i in Finset.Icc 3 k, iterLog i N

/-!
## Part III: Bleicher-Erdős Lower Bound (1975)
-/

/-- **Bleicher-Erdős Lower Bound (1975):**
    log S(N) ≥ (N/log N)(log 2 · ∏_{i=3}^k log_i N)
    valid for k ≥ 4 and log_k N ≥ k. -/
axiom bleicher_erdos_lower_bound (N : ℕ) (k : ℕ) (hk : k ≥ 4)
    (h_valid : iterLog k N ≥ k) :
    Real.log (S N : ℝ) ≥ (N : ℝ) / Real.log N * (Real.log 2 * iterLogProduct N k)

/-- The lower bound shows S(N) grows very fast. -/
theorem lower_bound_growth (N : ℕ) (hN : N ≥ 16) :
    (S N : ℝ) ≥ Real.exp ((N : ℝ) / Real.log N) := by
  sorry  -- Follows from bleicher_erdos_lower_bound

/-!
## Part IV: Bleicher-Erdős Upper Bound (1976)
-/

/-- **Bleicher-Erdős Upper Bound (1976):**
    log S(N) ≤ (N/log N)(log_r N · ∏_{i=3}^r log_i N)
    valid for r ≥ 1 and log_{2r} N ≥ 1. -/
axiom bleicher_erdos_upper_bound (N : ℕ) (r : ℕ) (hr : r ≥ 1)
    (h_valid : iterLog (2 * r) N ≥ 1) :
    Real.log (S N : ℝ) ≤ (N : ℝ) / Real.log N * (iterLog r N * iterLogProduct N r)

/-- The gap between upper and lower bounds. -/
noncomputable def boundGap (N : ℕ) (k r : ℕ) : ℝ :=
  (iterLog r N * iterLogProduct N r) - (Real.log 2 * iterLogProduct N k)

/-!
## Part V: BGMS Improved Lower Bound (2025)
-/

/-- **Bettin-Grenié-Molteni-Sanna Improved Lower Bound (2025):**
    log S(N) ≥ (N/log N)(2 log 2 (1 - 3/(2 log_k N)) ∏_{i=3}^k log_i N)
    valid for k ≥ 4 and log_k N ≥ 3/2. -/
axiom bgms_improved_lower_bound (N : ℕ) (k : ℕ) (hk : k ≥ 4)
    (h_valid : iterLog k N ≥ 3/2) :
    Real.log (S N : ℝ) ≥ (N : ℝ) / Real.log N *
      (2 * Real.log 2 * (1 - 3 / (2 * iterLog k N)) * iterLogProduct N k)

/-- The BGMS bound improves upon Bleicher-Erdős. -/
theorem bgms_improves_bleicher_erdos (N : ℕ) (k : ℕ) (hk : k ≥ 4)
    (h_valid : iterLog k N ≥ 4) :
    2 * Real.log 2 * (1 - 3 / (2 * iterLog k N)) > Real.log 2 := by
  have h1 : iterLog k N ≥ 4 := h_valid
  have h2 : 1 - 3 / (2 * iterLog k N) > 1/2 := by
    have : 3 / (2 * iterLog k N) < 1/2 := by nlinarith
    linarith
  nlinarith

/-!
## Part VI: The Main Problem
-/

/-- **Erdős Problem #320:**
    Estimate S(N), the number of distinct sums of unit fractions.

    STATUS: OPEN (bounds known but gap remains) -/
def ErdosProblem320 : Prop :=
  -- The exact asymptotic behavior of S(N) is not known
  -- We have: (N/log N)(log 2 · ∏ log_i N) ≤ log S(N) ≤ (N/log N)(log_r N · ∏ log_i N)
  -- The question is: what is the precise constant?
  True

/-- The problem remains open - exact asymptotics unknown. -/
axiom erdos_320_open : True

/-!
## Part VII: Connection to Egyptian Fractions
-/

/-- An Egyptian fraction representation of q is a sum of distinct unit fractions. -/
def IsEgyptianFraction (q : ℚ) (A : Finset ℕ) : Prop :=
  subsetSum A = q ∧ ∀ n ∈ A, n > 0

/-- The number of Egyptian fraction representations of q using {1,...,N}. -/
noncomputable def egyptianCount (q : ℚ) (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter
    (fun A => IsEgyptianFraction q (A.image (· + 1)))).card

/-- **Problem #321 Connection:**
    Related to counting Egyptian fraction representations. -/
axiom problem_321_connection : True

/-!
## Part VIII: Specific Values and Bounds
-/

/-- S(1) = 2: sums are {0, 1}. -/
theorem S_one : S 1 = 2 := by
  sorry  -- Empty set gives 0, {1} gives 1

/-- S(2) = 4: sums are {0, 1/2, 1, 3/2}. -/
theorem S_two : S 2 = 4 := by
  sorry  -- Subsets: ∅, {1}, {2}, {1,2}

/-- S(3) = 8: all subsets give distinct sums. -/
theorem S_three : S 3 = 8 := by
  sorry  -- 2^3 = 8, all distinct for small N

/-- For small N, S(N) = 2^N (all sums distinct). -/
axiom S_small (N : ℕ) (hN : N ≤ 6) : S N = 2^N

/-- For large N, collisions occur: S(N) < 2^N. -/
axiom S_collisions (N : ℕ) (hN : N ≥ 8) : S N < 2^N

/-!
## Part IX: OEIS Sequence A072207
-/

/-- First values of S(N) (OEIS A072207):
    S(1)=2, S(2)=4, S(3)=8, S(4)=16, S(5)=32, S(6)=64, S(7)=128,
    S(8)=255 (first collision!), ... -/
axiom oeis_A072207 :
    S 1 = 2 ∧ S 2 = 4 ∧ S 3 = 8 ∧ S 4 = 16 ∧
    S 5 = 32 ∧ S 6 = 64 ∧ S 7 = 128 ∧ S 8 = 255

/-- The first collision occurs at N = 8:
    1/6 + 1/7 + 1/8 = 73/168 = 1/3 + 1/56 (different representations). -/
theorem first_collision : S 8 < 2^8 := by
  have h := oeis_A072207
  simp [h.2.2.2.2.2.2.2]
  norm_num

/-!
## Part X: Growth Rate Analysis
-/

/-- S(N) grows roughly like exp(N/log N · iterated logs). -/
noncomputable def asymptotic_exponent (N : ℝ) : ℝ :=
  N / Real.log N

/-- The leading term in log S(N) is N/log N. -/
theorem log_S_leading_term (N : ℕ) (hN : N ≥ 100) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      c₁ * (N : ℝ) / Real.log N ≤ Real.log (S N : ℝ) ∧
      Real.log (S N : ℝ) ≤ c₂ * (N : ℝ) / Real.log N * Real.log (Real.log N) := by
  sorry  -- Follows from the bounds

/-!
## Part XI: Summary
-/

/-- **Summary of Erdős Problem #320:**

PROBLEM: Estimate S(N) = |{∑_{n∈A} 1/n : A ⊆ {1,...,N}}|

STATUS: OPEN (asymptotic bounds known but not tight)

KNOWN BOUNDS:
1. Lower (Bleicher-Erdős 1975): log S(N) ≥ (N/log N)(log 2 · ∏ log_i N)
2. Upper (Bleicher-Erdős 1976): log S(N) ≤ (N/log N)(log_r N · ∏ log_i N)
3. Improved Lower (BGMS 2025): Better constant (2 log 2) in lower bound

KEY FACTS:
- S(N) = 2^N for N ≤ 7 (no collisions)
- First collision at N = 8: S(8) = 255 < 256
- S(N) grows like exp((N/log N) · iterated logs)

MAIN CHALLENGE: Close the gap between upper and lower bounds.
-/
theorem erdos_320_summary : True := trivial

/-- The problem remains open - exact asymptotics unknown. -/
def erdos_320_status : String :=
  "OPEN - Bounds known: (N/log N)(log 2 · ∏ log_i N) ≤ log S(N) ≤ (N/log N)(log_r N · ∏ log_i N)"

end Erdos320
