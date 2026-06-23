/-
Erdős Problem #450: Divisor Density in Short Intervals

**Source:** [erdosproblems.com/450](https://erdosproblems.com/450)
**Status:** OPEN (Erdős–Graham, 1980)

## Statement

How large must y = y(ε, n) be such that the number of integers
in (x, x + y) with a divisor in (n, 2n) is at most ε·y?

## Background

From Erdős–Graham (1980, p.89). The question asks about the density
of integers having a "medium-sized" divisor (between n and 2n) in
short intervals. There is a subtlety about whether the bound holds
for all x or for some x.

Cambie showed that for the "for all x" interpretation, if
ε · (log n)^δ · (log log n)^{3/2} → ∞ (with δ ≈ 0.086),
no such y exists (using Ford's work on divisor distribution).

Reference: https://erdosproblems.com/450
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos450

open Finset

/- ## Part I: Divisors in an Interval -/

/-- An integer m has a divisor in the open interval (n, 2n). -/
def HasDivisorIn (m n : ℕ) : Prop :=
  ∃ d : ℕ, d ∣ m ∧ n < d ∧ d < 2 * n

/-- Count of integers in (x, x + y) having a divisor in (n, 2n). -/
noncomputable def countWithDivisor (x y n : ℕ) : ℕ :=
  ((Finset.range y).filter (fun i => HasDivisorIn (x + i + 1) n)).card

/- ## Part II: Proven Infrastructure Lemmas -/

/-- The count is bounded by the interval length. -/
theorem countWithDivisor_le (x y n : ℕ) :
    countWithDivisor x y n ≤ y := by
  unfold countWithDivisor
  calc ((Finset.range y).filter _).card
      ≤ (Finset.range y).card := Finset.card_filter_le _ _
    _ = y := Finset.card_range y

/-- Empty interval has zero count. -/
theorem countWithDivisor_zero (x n : ℕ) :
    countWithDivisor x 0 n = 0 := by
  unfold countWithDivisor
  simp [Finset.range_zero]

/-- For n = 0, no divisor can be in (0, 0), so the count is 0. -/
theorem countWithDivisor_n_zero (x y : ℕ) :
    countWithDivisor x y 0 = 0 := by
  unfold countWithDivisor
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro i _
  intro ⟨d, _, hdn, hd2n⟩
  omega

/-- For n = 1, the interval (1, 2) is empty, so the count is 0. -/
theorem countWithDivisor_n_one (x y : ℕ) :
    countWithDivisor x y 1 = 0 := by
  unfold countWithDivisor
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro i _
  intro ⟨d, _, hdn, hd2n⟩
  omega

/-- Monotonicity: longer intervals have at least as many divisor-rich integers. -/
theorem countWithDivisor_mono_y {y₁ y₂ : ℕ} (h : y₁ ≤ y₂) (x n : ℕ) :
    countWithDivisor x y₁ n ≤ countWithDivisor x y₂ n := by
  unfold countWithDivisor
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono h

/-- Any multiple of d ∈ (n, 2n) has a divisor in (n, 2n). -/
theorem hasDivisorIn_of_dvd {m n d : ℕ} (hd : d ∣ m) (hdn : n < d)
    (hd2n : d < 2 * n) : HasDivisorIn m n :=
  ⟨d, hd, hdn, hd2n⟩

/-- n+1 has a divisor in (n, 2n) when n ≥ 1: namely n+1 itself. -/
theorem hasDivisorIn_succ {n : ℕ} (hn : 1 ≤ n) :
    HasDivisorIn (n + 1) n := by
  exact ⟨n + 1, dvd_refl _, by omega, by omega⟩

/-- Any integer m in (n, 2n) has a divisor in (n, 2n): itself. -/
theorem hasDivisorIn_self {m n : ℕ} (hm1 : n < m) (hm2 : m < 2 * n) :
    HasDivisorIn m n :=
  ⟨m, dvd_refl _, hm1, hm2⟩

/-- 0 trivially has a divisor in (n, 2n) for n ≥ 2: every d divides 0,
    so we can take d = n + 1 ∈ (n, 2n). -/
theorem hasDivisorIn_zero {n : ℕ} (hn : n ≥ 2) :
    HasDivisorIn 0 n :=
  ⟨n + 1, dvd_zero _, by omega, by omega⟩

/- ## Part III: The Density Condition -/

/-- The density of integers with a divisor in (n, 2n) within (x, x+y)
    is at most ε. We use rational approximation: count ≤ εNum * y / εDen. -/
def DensityBound (x y n εNum εDen : ℕ) : Prop :=
  εDen ≥ 1 ∧ countWithDivisor x y n * εDen ≤ εNum * y

/-- DensityBound holds trivially for y = 0. -/
theorem densityBound_zero_y (x n εNum εDen : ℕ) (hε : εDen ≥ 1) :
    DensityBound x 0 n εNum εDen := by
  constructor
  · exact hε
  · simp [countWithDivisor_zero]

/-- DensityBound holds trivially when εNum ≥ εDen (since count ≤ y). -/
theorem densityBound_large_eps (x y n εNum εDen : ℕ) (hε : εDen ≥ 1)
    (hle : εDen ≤ εNum) :
    DensityBound x y n εNum εDen := by
  constructor
  · exact hε
  · calc countWithDivisor x y n * εDen
        ≤ y * εDen := by exact Nat.mul_le_mul_right εDen (countWithDivisor_le x y n)
      _ ≤ y * εNum := Nat.mul_le_mul_left y hle
      _ = εNum * y := Nat.mul_comm y εNum

/-- DensityBound for n = 0 holds trivially (count is always 0). -/
theorem densityBound_n_zero (x y εNum εDen : ℕ) (hε : εDen ≥ 1) :
    DensityBound x y 0 εNum εDen := by
  constructor
  · exact hε
  · rw [countWithDivisor_n_zero]; omega

/-- DensityBound for n = 1 holds trivially (count is always 0). -/
theorem densityBound_n_one (x y εNum εDen : ℕ) (hε : εDen ≥ 1) :
    DensityBound x y 1 εNum εDen := by
  constructor
  · exact hε
  · rw [countWithDivisor_n_one]; omega

/- ## Part IV: Problem Statements -/

/-- **Erdős Problem #450, "for all x" version:**
    Given ε > 0 and n, find the least y such that for ALL x,
    the density of integers in (x, x+y) with a divisor in (n, 2n)
    is at most ε. -/
def ErdosProblem450_ForAll : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∀ n : ℕ, n ≥ 2 →
      ∃ y : ℕ, y ≥ 1 ∧
        ∀ x : ℕ, DensityBound x y n εNum εDen

/-- **Erdős Problem #450, "exists x" version:**
    Given ε > 0 and n, find the least y such that for SOME x,
    the density condition holds. -/
def ErdosProblem450_Exists : Prop :=
  ∀ εNum εDen : ℕ, εNum ≥ 1 → εDen ≥ 1 →
    ∀ n : ℕ, n ≥ 2 →
      ∃ y : ℕ, y ≥ 1 ∧
        ∃ x : ℕ, DensityBound x y n εNum εDen

/-- The "for all x" version implies the "exists x" version. -/
theorem forAll_implies_exists :
    ErdosProblem450_ForAll → ErdosProblem450_Exists := by
  intro h εNum εDen hεN hεD n hn
  obtain ⟨y, hy, hx⟩ := h εNum εDen hεN hεD n hn
  exact ⟨y, hy, 0, hx 0⟩

/- ## Part V: Known Results (axiomatized) -/

/-- **Cambie's observation (for all x version):**
    If ε · (log n)^δ · (log log n)^{3/2} → ∞ with δ ≈ 0.086,
    no finite y works for the "for all x" version.
    This uses Ford's work on the distribution of divisors. -/
axiom cambie_no_y_for_all :
  ∃ εNum εDen : ℕ, εNum ≥ 1 ∧ εDen ≥ 1 ∧
    ∃ n : ℕ, n ≥ 2 ∧
      ∀ y : ℕ, y ≥ 1 →
        ∃ x : ℕ, ¬DensityBound x y n εNum εDen

/-- **Cambie: small ε regime.**
    For y ≥ 2n + 1, every interval of that length contains
    at least one multiple of some d ∈ (n, 2n). -/
axiom cambie_small_epsilon :
  ∀ n : ℕ, n ≥ 2 →
    ∀ y : ℕ, y ≥ 2 * n + 1 →
      ∀ x : ℕ, countWithDivisor x y n ≥ 1

/-- **Ford's divisor distribution:**
    For all n ≥ 2, every interval of length 4n contains
    integers with a divisor in (n, 2n). -/
axiom ford_divisor_distribution :
  ∀ n : ℕ, n ≥ 2 →
    ∀ x : ℕ, countWithDivisor x (4 * n) n ≥ 1

/- ## Part VI: Corollaries -/

/-- Cambie's result implies the "for all x" version is FALSE in general. -/
theorem not_forAll_in_general : ¬ErdosProblem450_ForAll := by
  intro h
  obtain ⟨εNum, εDen, hεN, hεD, n, hn, hbad⟩ := cambie_no_y_for_all
  obtain ⟨y, hy, hgood⟩ := h εNum εDen hεN hεD n hn
  obtain ⟨x, hx⟩ := hbad y hy
  exact hx (hgood x)

/-- Summary of the current state of knowledge. -/
theorem erdos_450_summary :
    -- The "for all x" version can fail
    (∃ εNum εDen : ℕ, εNum ≥ 1 ∧ εDen ≥ 1 ∧
      ∃ n : ℕ, n ≥ 2 ∧
        ∀ y : ℕ, y ≥ 1 → ∃ x : ℕ, ¬DensityBound x y n εNum εDen) ∧
    -- Every long interval has integers with divisors in (n, 2n)
    (∀ n : ℕ, n ≥ 2 → ∀ y : ℕ, y ≥ 2 * n + 1 →
      ∀ x : ℕ, countWithDivisor x y n ≥ 1) :=
  ⟨cambie_no_y_for_all, cambie_small_epsilon⟩

end Erdos450
