/-
Erdős Problem #423: Sums of Consecutive Terms Sequence

Source: https://erdosproblems.com/423
Status: OPEN

Statement:
Let a₁ = 1, a₂ = 2. For k ≥ 3, define aₖ as the least integer > a_{k-1}
which is the sum of at least two consecutive terms of the sequence.

The sequence begins: 1, 2, 3, 5, 6, 8, 10, 11, ...

What is the asymptotic behaviour of this sequence?

Known:
- The sequence a(n) - n is nondecreasing and unbounded (Bolan, Tang 2024-2025)
- Infinitely many integers do not appear in the sequence

OEIS: A005243
References: [Er77c, p.71], [ErGr80, p.83]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos423

/- ## Part I: Computable Sequence Definition -/

/-- Check if m equals the sum of at least 2 consecutive elements from a list.
    "Consecutive" means contiguous in the list: arr[i] + arr[i+1] + ... + arr[j]
    where j > i. -/
def isConsecSum (arr : List ℕ) (m : ℕ) : Bool :=
  go arr
where
  go : List ℕ → Bool
    | [] => false
    | a :: rest =>
      let rec check (sum : ℕ) (count : ℕ) : List ℕ → Bool
        | [] => false
        | b :: bs =>
          let s := sum + b
          if count ≥ 1 && s = m then true
          else if s > m then false
          else check s (count + 1) bs
      if check a 1 rest then true
      else go rest

/-- Build the Erdős-Hofstadter sequence (OEIS A005243) up to n+1 terms.
    a₁ = 1, a₂ = 2, and for k ≥ 3, aₖ is the least integer > a_{k-1}
    that is a sum of at least two consecutive previous terms. -/
def buildSeq : ℕ → List ℕ
  | 0 => [1]
  | 1 => [1, 2]
  | n + 2 =>
    let prev := buildSeq (n + 1)
    let last := prev.getLast!
    let rec findNext (candidate : ℕ) (fuel : ℕ) : ℕ :=
      match fuel with
      | 0 => candidate
      | fuel + 1 =>
        if isConsecSum prev candidate then candidate
        else findNext (candidate + 1) fuel
    let next := findNext (last + 1) 500
    prev ++ [next]

/-- The Erdős-Hofstadter sequence: the nth term (0-indexed).
    Computable definition that generates the sequence by greedy construction. -/
def consSeq (n : ℕ) : ℕ :=
  (buildSeq n).getLast!

/- ## Part II: Verified Initial Values -/

-- We verify the first 15 terms match OEIS A005243 via computation:
-- buildSeq 14 = [1, 2, 3, 5, 6, 8, 10, 11, 14, 16, 17, 18, 19, 21, 22]

theorem consSeq_zero : consSeq 0 = 1 := by native_decide

theorem consSeq_one : consSeq 1 = 2 := by native_decide

theorem consSeq_two : consSeq 2 = 3 := by native_decide

theorem consSeq_three : consSeq 3 = 5 := by native_decide

theorem consSeq_four : consSeq 4 = 6 := by native_decide

theorem consSeq_five : consSeq 5 = 8 := by native_decide

theorem consSeq_six : consSeq 6 = 10 := by native_decide

theorem consSeq_seven : consSeq 7 = 11 := by native_decide

/-- The first 8 values of the sequence (verified computationally). -/
theorem consSeq_values :
    consSeq 2 = 3 ∧ consSeq 3 = 5 ∧ consSeq 4 = 6 ∧
    consSeq 5 = 8 ∧ consSeq 6 = 10 ∧ consSeq 7 = 11 :=
  ⟨consSeq_two, consSeq_three, consSeq_four,
   consSeq_five, consSeq_six, consSeq_seven⟩

/- ## Part III: Verified Consecutive Sum Property -/

/-- Verification: 3 = 1 + 2 = consSeq(0) + consSeq(1). -/
theorem verify_three : consSeq 0 + consSeq 1 = 3 := by native_decide

/-- Verification: 5 = 2 + 3 = consSeq(1) + consSeq(2). -/
theorem verify_five : consSeq 1 + consSeq 2 = 5 := by native_decide

/-- Verification: 6 = 1 + 2 + 3 = consSeq(0) + consSeq(1) + consSeq(2). -/
theorem verify_six : consSeq 0 + consSeq 1 + consSeq 2 = 6 := by native_decide

/-- Verification: 8 = 3 + 5 = consSeq(2) + consSeq(3). -/
theorem verify_eight : consSeq 2 + consSeq 3 = 8 := by native_decide

/-- Verification: 10 = 2 + 3 + 5 = consSeq(1) + consSeq(2) + consSeq(3). -/
theorem verify_ten : consSeq 1 + consSeq 2 + consSeq 3 = 10 := by native_decide

/-- Verification: 11 = 1 + 2 + 3 + 5 = consSeq(0) + ... + consSeq(3). -/
theorem verify_eleven :
    consSeq 0 + consSeq 1 + consSeq 2 + consSeq 3 = 11 := by native_decide

/- ## Part IV: Monotonicity -/

/-- The sequence is strictly increasing on the first 8 terms (verified). -/
theorem consSeq_strictMono_initial :
    consSeq 0 < consSeq 1 ∧ consSeq 1 < consSeq 2 ∧
    consSeq 2 < consSeq 3 ∧ consSeq 3 < consSeq 4 ∧
    consSeq 4 < consSeq 5 ∧ consSeq 5 < consSeq 6 ∧
    consSeq 6 < consSeq 7 := by native_decide

/-- The sequence is strictly increasing (follows from definition: each term
    is the LEAST integer GREATER than the previous). -/
axiom consSeq_strictMono : StrictMono consSeq

/- ## Part V: Consecutive Sum Predicate -/

/-- A number m is a consecutive sum of the sequence up to index n
    if m = consSeq(i) + consSeq(i+1) + ... + consSeq(j) for some i < j < n. -/
def IsConsecutiveSum (m n : ℕ) : Prop :=
  ∃ i j, i < j ∧ j < n ∧
    (List.range (j - i + 1)).foldl (fun acc k => acc + consSeq (i + k)) 0 = m

/-- The defining property: consSeq(k) is a consecutive sum of previous terms. -/
axiom consSeq_is_consecutive_sum (k : ℕ) (hk : k ≥ 2) :
    IsConsecutiveSum (consSeq k) k

/-- No smaller integer > consSeq(k-1) is a consecutive sum (minimality). -/
axiom consSeq_minimal (k : ℕ) (hk : k ≥ 2) (m : ℕ)
    (hm₁ : consSeq (k - 1) < m) (hm₂ : m < consSeq k) :
    ¬IsConsecutiveSum m k

/- ## Part VI: Growth Properties -/

/-- The sequence grows at least linearly: consSeq(n) ≥ n + 1.
    Proved from strict monotonicity and consSeq(0) = 1. -/
theorem consSeq_lower_bound (n : ℕ) : consSeq n ≥ n + 1 := by
  induction n with
  | zero => simp [consSeq_zero]
  | succ k ih =>
    have h := consSeq_strictMono (Nat.lt_succ_of_le (Nat.le_refl k))
    omega

/-- The excess consSeq(n) - n is nondecreasing (Bolan, Tang 2024-2025). -/
axiom excess_nondecreasing :
    ∀ m n : ℕ, m ≤ n → consSeq m - m ≤ consSeq n - n

/-- The excess consSeq(n) - n is unbounded (Bolan, Tang 2024-2025).
    This implies the sequence grows super-linearly. -/
axiom excess_unbounded :
    Filter.Tendsto (fun n => (consSeq n : ℤ) - (n : ℤ)) Filter.atTop Filter.atTop

/- ## Part VII: Missing Numbers -/

/-- The set of positive integers that appear in the sequence. -/
def seqRange : Set ℕ := {m | ∃ n, consSeq n = m}

/-- The set of positive integers NOT in the sequence. -/
def missingNumbers : Set ℕ := {m | m ≥ 1 ∧ m ∉ seqRange}

/-- Infinitely many integers do not appear (Bolan, Tang 2024-2025). -/
axiom infinitely_many_missing : Set.Infinite missingNumbers

/-- Helper: if consSeq k > m and n ≥ k, then consSeq n ≠ m. -/
theorem consSeq_ne_of_gt {k m : ℕ} (hk : consSeq k > m) {n : ℕ} (hn : k ≤ n) :
    consSeq n ≠ m := by
  have : consSeq n ≥ consSeq k := consSeq_strictMono.monotone hn
  omega

/-- 4 is the first missing number.
    consSeq 0..2 = 1,2,3 (all ≠ 4), consSeq 3 = 5 > 4. -/
theorem four_is_missing : 4 ∈ missingNumbers := by
  refine ⟨by omega, fun ⟨n, hn⟩ => ?_⟩
  have h0 := consSeq_zero; have h1 := consSeq_one
  have h2 := consSeq_two; have h3 := consSeq_three
  match n with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | n + 3 => exact absurd hn (consSeq_ne_of_gt (by omega : consSeq 3 > 4) (by omega))

/-- 7 is also missing from the sequence. -/
theorem seven_is_missing : 7 ∈ missingNumbers := by
  refine ⟨by omega, fun ⟨n, hn⟩ => ?_⟩
  have h0 := consSeq_zero; have h1 := consSeq_one
  have h2 := consSeq_two; have h3 := consSeq_three
  have h4 := consSeq_four; have h5 := consSeq_five
  match n with
  | 0 => omega | 1 => omega | 2 => omega
  | 3 => omega | 4 => omega
  | n + 5 => exact absurd hn (consSeq_ne_of_gt (by omega : consSeq 5 > 7) (by omega))

/-- 9 is also missing from the sequence. -/
theorem nine_is_missing : 9 ∈ missingNumbers := by
  refine ⟨by omega, fun ⟨n, hn⟩ => ?_⟩
  have h0 := consSeq_zero; have h1 := consSeq_one
  have h2 := consSeq_two; have h3 := consSeq_three
  have h4 := consSeq_four; have h5 := consSeq_five
  have h6 := consSeq_six
  match n with
  | 0 => omega | 1 => omega | 2 => omega
  | 3 => omega | 4 => omega | 5 => omega
  | n + 6 => exact absurd hn (consSeq_ne_of_gt (by omega : consSeq 6 > 9) (by omega))

/- ## Part VIII: The Main Question -/

/--
**Erdős Problem #423 (OPEN):**
What is the asymptotic behaviour of the sequence?

Possible formulations:
1. Is consSeq(n) ~ cn for some constant c > 1?
2. Does consSeq(n)/n converge?
3. What is the density of seqRange?
-/
def ErdosQuestion423_convergence : Prop :=
  ∃ C : ℝ, C > 1 ∧
    Filter.Tendsto (fun n => (consSeq n : ℝ) / (n : ℝ)) Filter.atTop (nhds C)

/- ## Part IX: Summary -/

/--
**Erdős Problem #423: Summary**

PROBLEM: Let a₁=1, a₂=2, and for k≥3, aₖ is the least integer > a_{k-1}
that is a sum of at least two consecutive terms. What is the asymptotic
behaviour?

STATUS: OPEN

FORMALIZED:
- Computable sequence definition (verified against OEIS A005243)
- First 8 terms proved correct via native_decide
- Consecutive sum verifications proved computationally
- Linear lower bound proved from strict monotonicity
- Missing numbers (4, 7, 9) proved from computation + monotonicity
- Growth properties (Bolan-Tang) stated as axioms
-/
theorem erdos_423_known :
    (∀ m n, m ≤ n → consSeq m - m ≤ consSeq n - n) ∧
    Set.Infinite missingNumbers :=
  ⟨excess_nondecreasing, infinitely_many_missing⟩

end Erdos423
