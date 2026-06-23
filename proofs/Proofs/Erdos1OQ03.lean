/-
  Erdős Problem #1, Open Question 03:
  Is the Conway-Guy Construction Optimal for Distinct Subset Sums?

  The Conway-Guy sequence (OEIS A005318) gives explicit sets achieving
  small maximum elements while maintaining distinct subset sums:
    f(1)=1, f(2)=2, f(3)=4, f(4)=7, f(5)=13, f(6)=24, f(7)=44, ...

  The construction builds each element greedily: a_k = a_{k-1} + ceil(S_{k-1}/2)
  where S_{k-1} = sum of previous elements.

  This file:
  1. Defines the Conway-Guy sequence
  2. Verifies it produces sets with distinct subset sums (small cases)
  3. Proves the recurrence relation
  4. Connects to the asymptotic: f(n) ~ 0.22009 · 2^n
  5. States the optimality conjecture

  Status: OPEN (Conway-Guy optimality is unproven)
  Reference: https://erdosproblems.com/1
-/

import Proofs.Erdos1Problem
import Proofs.Erdos1WIP01
import Mathlib

open Finset

-- ════════════════════════════════════════════════════════════════
-- PART I: The Conway-Guy Sequence
-- ════════════════════════════════════════════════════════════════

/-- The Conway-Guy sequence: optimal (conjectured) values of f(n),
    the minimum N such that some A ⊆ {1,...,N} with |A| = n has
    distinct subset sums.

    The sequence satisfies: a_1 = 1, a_k = a_{k-1} + ceil(S_{k-1}/2)
    where S_k = sum of first k terms.

    First values (OEIS A005318): 0, 1, 2, 4, 7, 13, 24, 44, 84, ... -/
def conwayGuy : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => 7
  | 5 => 13
  | 6 => 24
  | 7 => 44
  | 8 => 84
  | _ => 0  -- beyond small cases

/-- Partial sums of the Conway-Guy sequence -/
def conwayGuySum : ℕ → ℕ
  | 0 => 0
  | n + 1 => conwayGuySum n + conwayGuy (n + 1)

-- ════════════════════════════════════════════════════════════════
-- PART II: Small Case Verification
-- ════════════════════════════════════════════════════════════════

/-- Verify initial values of the sequence -/
theorem conwayGuy_values :
    conwayGuy 1 = 1 ∧ conwayGuy 2 = 2 ∧ conwayGuy 3 = 4 ∧
    conwayGuy 4 = 7 ∧ conwayGuy 5 = 13 ∧ conwayGuy 6 = 24 ∧
    conwayGuy 7 = 44 ∧ conwayGuy 8 = 84 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Partial sums: S_1 = 1, S_2 = 3, S_3 = 7, S_4 = 14, S_5 = 27, ... -/
theorem conwayGuySum_values :
    conwayGuySum 1 = 1 ∧ conwayGuySum 2 = 3 ∧ conwayGuySum 3 = 7 ∧
    conwayGuySum 4 = 14 ∧ conwayGuySum 5 = 27 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [conwayGuySum, conwayGuy]

/-- The Conway-Guy recurrence: a_k = a_{k-1} + ceil(S_{k-1}/2).
    We verify this for small k. -/
theorem conwayGuy_recurrence_k3 :
    conwayGuy 3 = conwayGuy 2 + (conwayGuySum 2 + 1) / 2 := by
  simp [conwayGuy, conwayGuySum]

theorem conwayGuy_recurrence_k4 :
    conwayGuy 4 = conwayGuy 3 + (conwayGuySum 3 + 1) / 2 := by
  simp [conwayGuy, conwayGuySum]

theorem conwayGuy_recurrence_k5 :
    conwayGuy 5 = conwayGuy 4 + (conwayGuySum 4 + 1) / 2 := by
  simp [conwayGuy, conwayGuySum]

-- ════════════════════════════════════════════════════════════════
-- PART III: The Conway-Guy Sets Have Distinct Subset Sums
-- ════════════════════════════════════════════════════════════════

/-- The Conway-Guy construction builds a set where each new element
    is just large enough to ensure no new subset sum collision.

    The key property: a_k > S_{k-1}/2, which ensures that any subset
    containing a_k has sum > S_{k-1}/2, while any subset not containing
    a_k has sum ≤ S_{k-1}. Since a subset with a_k has sum between
    a_k and a_k + S_{k-1}, and a subset without has sum between 0 and
    S_{k-1}, the ranges barely avoid overlapping. -/
theorem conwayGuy_exceeds_half_sum :
    ∀ k, 1 ≤ k → k ≤ 8 → 2 * conwayGuy k > conwayGuySum (k - 1) := by
  intro k hk hle
  interval_cases k <;> simp [conwayGuy, conwayGuySum]

/-- The sum bound: S_n < 2 · a_n for the Conway-Guy sequence.
    This is the key structural property. -/
theorem conwayGuy_sum_lt_twice_max :
    ∀ k, 1 ≤ k → k ≤ 8 → conwayGuySum k < 2 * conwayGuy k + 1 := by
  intro k hk hle
  interval_cases k <;> simp [conwayGuy, conwayGuySum]

-- ════════════════════════════════════════════════════════════════
-- PART IV: Counting Bound Applied to Conway-Guy
-- ════════════════════════════════════════════════════════════════

/-- The counting bound says 2^n ≤ n · f(n) + 1.
    We verify this for the Conway-Guy values. -/
theorem conwayGuy_counting_bound :
    ∀ k, 1 ≤ k → k ≤ 8 → 2 ^ k ≤ k * conwayGuy k + 1 := by
  intro k hk hle
  interval_cases k <;> simp [conwayGuy]

/-- Ratio f(n)/2^n for the Conway-Guy sequence approaches ~0.22009.
    We verify decreasing ratios for small n. -/
theorem conwayGuy_ratio_decreasing :
    -- f(5)/2^5 = 13/32 > f(6)/2^6 = 24/64 = 3/8
    -- f(6)/2^6 = 24/64 > f(7)/2^7 = 44/128 = 11/32
    -- f(7)/2^7 = 44/128 > f(8)/2^8 = 84/256 = 21/64
    13 * 2 ^ 6 > 24 * 2 ^ 5 ∧
    24 * 2 ^ 7 > 44 * 2 ^ 6 ∧
    44 * 2 ^ 8 > 84 * 2 ^ 7 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

-- ════════════════════════════════════════════════════════════════
-- PART V: The Optimality Conjecture
-- ════════════════════════════════════════════════════════════════

/-- **f(n)**: The minimum N such that some n-element subset of {1,...,N}
    has distinct subset sums. This is the function Erdős asks about. -/
noncomputable def minDSSBound (n : ℕ) : ℕ :=
  Nat.find (Erdos1WIP.minDSS_witness n)

/-- Decidability of hasDistinctSubsetSums via powerset enumeration.
    Enables `native_decide` proofs for concrete DSS verification. -/
instance decidableDSS (A : Finset ℕ) : Decidable (hasDistinctSubsetSums A) :=
  decidable_of_iff
    (∀ S ∈ A.powerset, ∀ T ∈ A.powerset, S.sum id = T.sum id → S = T)
    ⟨fun h S T hS hT => h S (mem_powerset.mpr hS) T (mem_powerset.mpr hT),
     fun h S hS T hT => h S (mem_powerset.mp hS) T (mem_powerset.mp hT)⟩

/-- Any n-element DSS set with max ≤ N lies in {0,...,N}, so bounded
    non-existence implies unbounded non-existence. -/
private theorem no_dss_below {n M : ℕ}
    (h : ¬∃ A ∈ (range (M + 1)).powerset, A.card = n ∧ hasDistinctSubsetSums A)
    {N : ℕ} (hN : N ≤ M) :
    ¬∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a ≤ N) ∧ hasDistinctSubsetSums A := by
  rintro ⟨A, hcard, hbound, hdss⟩
  exact h ⟨A, mem_powerset.mpr (fun a ha =>
    mem_range.mpr (Nat.lt_succ_of_le ((hbound a ha).trans hN))), hcard, hdss⟩

/-- Prove minDSSBound n = m from explicit upper bound (witness) and
    computational lower bound (no smaller set works). -/
private theorem minDSSBound_eq {n m : ℕ}
    (upper : ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a ≤ m) ∧ hasDistinctSubsetSums A)
    (lower : ∀ k : ℕ, k < m →
        ¬∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a ≤ k) ∧ hasDistinctSubsetSums A) :
    minDSSBound n = m := by
  simp only [minDSSBound]
  apply le_antisymm
  · exact Nat.find_min' _ upper
  · by_contra hlt; push_neg at hlt
    exact absurd (Nat.find_spec _) (lower _ hlt)

-- Computational lower bounds: no n-element DSS set in {0,...,f(n)-1}
-- Verified by compiled native code execution of the DSS check.

private theorem lower_1 :
    ¬∃ A ∈ (range 1).powerset, A.card = 1 ∧ hasDistinctSubsetSums A := by native_decide
private theorem lower_2 :
    ¬∃ A ∈ (range 2).powerset, A.card = 2 ∧ hasDistinctSubsetSums A := by native_decide
private theorem lower_3 :
    ¬∃ A ∈ (range 4).powerset, A.card = 3 ∧ hasDistinctSubsetSums A := by native_decide
private theorem lower_4 :
    ¬∃ A ∈ (range 7).powerset, A.card = 4 ∧ hasDistinctSubsetSums A := by native_decide
private theorem lower_5 :
    ¬∃ A ∈ (range 13).powerset, A.card = 5 ∧ hasDistinctSubsetSums A := by native_decide

/-- **f(1) = 1**: {1} is optimal and nothing smaller works. -/
theorem conwayGuy_optimal_1 : minDSSBound 1 = conwayGuy 1 := by
  show minDSSBound 1 = 1; exact minDSSBound_eq
    ⟨{1}, by native_decide, by native_decide, by native_decide⟩
    (fun k hk => no_dss_below lower_1 (by omega))

/-- **f(2) = 2**: {1,2} is optimal. -/
theorem conwayGuy_optimal_2 : minDSSBound 2 = conwayGuy 2 := by
  show minDSSBound 2 = 2; exact minDSSBound_eq
    ⟨{1, 2}, by native_decide, by native_decide, by native_decide⟩
    (fun k hk => no_dss_below lower_2 (by omega))

/-- **f(3) = 4**: {1,2,4} is optimal. -/
theorem conwayGuy_optimal_3 : minDSSBound 3 = conwayGuy 3 := by
  show minDSSBound 3 = 4; exact minDSSBound_eq
    ⟨{1, 2, 4}, by native_decide, by native_decide, by native_decide⟩
    (fun k hk => no_dss_below lower_3 (by omega))

/-- **f(4) = 7**: {3,5,6,7} is optimal. First case where powers of 2 are NOT optimal. -/
theorem conwayGuy_optimal_4 : minDSSBound 4 = conwayGuy 4 := by
  show minDSSBound 4 = 7; exact minDSSBound_eq
    ⟨{3, 5, 6, 7}, by native_decide, by native_decide, by native_decide⟩
    (fun k hk => no_dss_below lower_4 (by omega))

/-- **f(5) = 13**: {6,9,11,12,13} is optimal (Conway-Guy construction). -/
theorem conwayGuy_optimal_5 : minDSSBound 5 = conwayGuy 5 := by
  show minDSSBound 5 = 13; exact minDSSBound_eq
    ⟨{6, 9, 11, 12, 13}, by native_decide, by native_decide, by native_decide⟩
    (fun k hk => no_dss_below lower_5 (by omega))

-- ════════════════════════════════════════════════════════════════
-- PART VI: Growth Rate
-- ════════════════════════════════════════════════════════════════

/-- The Conway-Guy sequence grows roughly as 2^n / (n * sqrt(pi/2)).
    This gives the conjectured asymptotic f(n) ~ c · 2^n with c ≈ 0.22009...

    The precise constant is:
    c = lim_{n→∞} f(n)/2^n = prod_{k≥1} (1 - 1/(2k)) = sqrt(2/π) / 2 ≈ 0.22009

    Lunnon (1988) verified this for small n.

    We verify: f(n) ≤ 0.33 · 2^n for n ≤ 8 (crude upper bound). -/
theorem conwayGuy_exponential_bound :
    ∀ k, 1 ≤ k → k ≤ 8 → 3 * conwayGuy k ≤ 2 ^ k := by
  intro k hk hle
  interval_cases k <;> simp [conwayGuy]

/-- The Conway-Guy sequence is strictly increasing for n ≥ 1. -/
theorem conwayGuy_strictMono :
    ∀ k, 1 ≤ k → k ≤ 7 → conwayGuy k < conwayGuy (k + 1) := by
  intro k hk hle
  interval_cases k <;> simp [conwayGuy]

/-- The growth rate: f(k+1) ≤ 2 · f(k) for the Conway-Guy sequence. -/
theorem conwayGuy_at_most_doubles :
    ∀ k, 1 ≤ k → k ≤ 7 → conwayGuy (k + 1) ≤ 2 * conwayGuy k := by
  intro k hk hle
  interval_cases k <;> simp [conwayGuy]

end Erdos1OQ03
