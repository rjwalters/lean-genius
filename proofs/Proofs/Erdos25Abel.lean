/-
Erdős Problem #25: Abel Summation Infrastructure

This file provides the Abel summation identity for logWeightedCount,
the key building block for proving naturalDensity_implies_logDensity.

The identity:
  Σ_{n=1}^{N} 1_A(n)/n = c(N)/N + Σ_{n=1}^{N-1} c(n)/(n·(n+1))
where c(n) = |A ∩ {1,...,n}| (counting function, excluding 0).

Once this identity is established, the proof of
naturalDensity_implies_logDensity reduces to:
1. c(N)/(N·log N) → 0 (since c(N)/N → d and 1/log N → 0)
2. (1/log N) · Σ c(n)/(n·(n+1)) → d (weighted Cesàro argument)

Axiom count: 0
Sorry count: 0
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset BigOperators Classical

attribute [local instance] Classical.dec Classical.decPred

namespace Erdos25Abel

/-- Counting function for a set A: counts |A ∩ {1,...,N}| (excluding 0).
    This matches the convention of Erdos25.logWeightedCount. -/
noncomputable def countExcl (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Finset.filter (fun n => n ∈ A ∧ n ≠ 0) (Finset.range (N + 1))).card : ℝ)

/-- The weighted sum Σ_{n ∈ A, 1 ≤ n ≤ N} 1/n.
    Redefined here to avoid importing Erdos25LogDensity. -/
noncomputable def weightedCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), if n ∈ A ∧ n ≠ 0 then (1 : ℝ) / n else 0

/-- weightedCount at 0 is 0 (only n=0 in range, which is excluded). -/
theorem weightedCount_zero (A : Set ℕ) : weightedCount A 0 = 0 := by
  simp [weightedCount, Finset.sum_range_one]

/-- countExcl at 0 is 0. -/
theorem countExcl_zero (A : Set ℕ) : countExcl A 0 = 0 := by
  simp [countExcl, Finset.range_one, Finset.filter_singleton]

/-- Recurrence for weightedCount. -/
theorem weightedCount_succ (A : Set ℕ) (N : ℕ) :
    weightedCount A (N + 1) = weightedCount A N +
    (if (N + 1) ∈ A then (1 : ℝ) / (↑(N + 1)) else 0) := by
  simp only [weightedCount, Finset.sum_range_succ, Nat.succ_ne_zero, ne_eq,
    not_false_eq_true, and_true]

/-- Recurrence for countExcl: adds 1 when N+1 ∈ A. -/
theorem countExcl_succ (A : Set ℕ) (N : ℕ) :
    countExcl A (N + 1) = countExcl A N + if (N + 1) ∈ A then 1 else 0 := by
  simp only [countExcl]
  rw [show N + 1 + 1 = N + 2 from by omega]
  rw [show N + 1 = N + 1 from rfl]
  rw [Finset.range_succ]
  simp only [Finset.filter_insert, Nat.succ_ne_zero, ne_eq, not_false_eq_true, and_true]
  split_ifs with h
  · rw [Finset.card_insert_of_not_mem]
    · push_cast; ring
    · simp only [Finset.mem_filter, Finset.mem_range]; omega
  · ring

/-- **Abel summation identity for weightedCount.**
    Σ_{n=1}^{N} 1_A(n)/n = c(N)/N + Σ_{n ∈ Ico 1 N} c(n)/(n·(n+1))

    Proved by induction on N. The inductive step uses the partial fraction
    identity 1/n = 1/(n+1) + 1/(n·(n+1)). -/
theorem weightedCount_abel (A : Set ℕ) : ∀ N : ℕ, 1 ≤ N →
    weightedCount A N = countExcl A N / (N : ℝ) +
    ∑ n ∈ Finset.Ico 1 N, countExcl A n / ((n : ℝ) * (↑n + 1)) := by
  intro N hN
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · -- Base case: N = 1
      subst hn0
      simp only [weightedCount_succ, weightedCount_zero, zero_add,
        Finset.Ico_self, Finset.sum_empty, add_zero]
      rw [countExcl_succ, countExcl_zero, zero_add]
      split_ifs with h
      · simp
      · simp
    · -- Inductive step: n ≥ 1
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      rw [weightedCount_succ, ih hn1]
      -- Extend the sum: Ico 1 (n+1) = Ico 1 n ∪ {n}
      have h_ico : Finset.Ico 1 (n + 1) = Finset.Ico 1 n ∪ {n} := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
      have h_disj : Disjoint (Finset.Ico 1 n) {n} := by
        simp [Finset.disjoint_left]; intro k hk1 hk2 hkn; omega
      rw [h_ico, Finset.sum_union h_disj, Finset.sum_singleton]
      -- Algebra: c(n)/n + [n+1∈A]/(n+1) = c(n+1)/(n+1) + c(n)/(n·(n+1))
      rw [countExcl_succ]
      have hn_pos : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
      have hn1_pos : (↑(n + 1) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
      split_ifs with h
      · -- N+1 ∈ A: need c(n)/n + Σ + 1/(n+1) = (c(n)+1)/(n+1) + Σ + c(n)/(n·(n+1))
        field_simp
        ring
      · -- N+1 ∉ A: need c(n)/n + Σ = c(n)/(n+1) + Σ + c(n)/(n·(n+1))
        -- i.e., c(n)/n = c(n)/(n+1) + c(n)/(n·(n+1))  [partial fractions]
        simp only [add_zero]
        ring_nf
        field_simp
        ring

end Erdos25Abel
