/-
# Erdős Problem #323 — Sums of k-th Powers Counting Function

Let f_{k,m}(x) denote the count of integers ≤ x that are representable as
sums of m nonnegative k-th powers. Two questions:

1. Is f_{k,k}(x) ≫_ε x^{1-ε} for all ε > 0?
2. If m < k, is f_{k,m}(x) ≫ x^{m/k}?

## Known results

- **k = 2**: Landau proved f_{2,2}(x) ~ c·x/√(log x) for a constant c > 0.
  This completely resolves the case k = 2.
- **k > 2**: It is unknown whether f_{k,k}(x) = o(x).

Erdős and Graham described this as "unattackable by the methods at our
disposal."

Reference: https://erdosproblems.com/323

Axioms: 1 (landau_two_squares)
Proved: 4 theorems (isSumOfPowers_one, first_power_count, isSumOfPowers_succ, power_sum_count_mono)
Sorries: 0
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/- ## Sums of k-th powers -/

/-- An integer n is a sum of m nonnegative k-th powers. -/
def IsSumOfPowers (n k m : ℕ) : Prop :=
    ∃ (xs : Fin m → ℕ), n = (Finset.univ.sum fun i => (xs i) ^ k)

/-- f_{k,m}(x): count of integers in [0, x] that are sums of m k-th powers. -/
noncomputable def powerSumCount (k m x : ℕ) : ℕ :=
    (Finset.range (x + 1)).filter (fun n => IsSumOfPowers n k m) |>.card

/- ## Basic properties -/

/-- Every nonneg integer is a sum of m first powers (k=1): n = n + 0 + ··· + 0. -/
theorem isSumOfPowers_one (n m : ℕ) (hm : 1 ≤ m) : IsSumOfPowers n 1 m := by
  use fun i => if i = ⟨0, by omega⟩ then n else 0
  simp [pow_one, Finset.sum_ite_eq', Finset.mem_univ]

/-- f_{1,m}(x) ≥ m for x ≥ m: every integer is a sum of m 1st powers. -/
theorem first_power_count (m x : ℕ) (hm : 1 ≤ m) (hx : m ≤ x) :
    m ≤ powerSumCount 1 m x := by
  have h_full : powerSumCount 1 m x = x + 1 := by
    unfold powerSumCount
    rw [Finset.filter_true_of_mem (fun n _ => isSumOfPowers_one n m hm)]
    exact Finset.card_range (x + 1)
  omega

/-- If n is a sum of m k-th powers, it is also a sum of (m+1) k-th powers
    (append a 0^k = 0 term). -/
theorem isSumOfPowers_succ {n k m : ℕ} (h : IsSumOfPowers n k m) :
    IsSumOfPowers n k (m + 1) := by
  obtain ⟨xs, hxs⟩ := h
  use Fin.snoc xs 0
  rw [hxs]
  rw [Fin.sum_univ_snoc]
  simp [Fin.snoc_last, Fin.snoc_castSucc]

/-- Monotonicity: f_{k,m}(x) ≤ f_{k,m+1}(x). -/
theorem power_sum_count_mono (k m x : ℕ) :
    powerSumCount k m x ≤ powerSumCount k (m + 1) x := by
  unfold powerSumCount
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  intro n hn
  exact isSumOfPowers_succ hn

/- ## Landau's theorem for sums of two squares -/

/-- Landau: f_{2,2}(x) ~ c·x/√(log x). Formally: for every ε > 0,
    for large x, (1-ε)·c·x/√(log x) ≤ f_{2,2}(x) ≤ (1+ε)·c·x/√(log x). -/
axiom landau_two_squares :
    ∃ c : ℚ, 0 < c ∧
      ∀ ε : ℚ, 0 < ε → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (1 - ε) * c * (x : ℚ) ≤ (powerSumCount 2 2 x : ℚ) * (Nat.log 2 x : ℚ)

/- ## Main conjectures -/

/-- Conjecture 1: f_{k,k}(x) ≫_ε x^{1-ε} for all ε > 0.
    Formally: for every k ≥ 2 and ε > 0, there exist c > 0 and x₀ such that
    f_{k,k}(x) ≥ c · x^{1-ε} for all x ≥ x₀. -/
def ErdosProblem323_part1 : Prop :=
    ∀ (k : ℕ) (hk : 2 ≤ k) (ε : ℚ) (hε : 0 < ε),
      ∃ c : ℚ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        c * (x : ℚ) ≤ (powerSumCount k k x : ℚ) * (x : ℚ) ^ ε

/-- Conjecture 2: for m < k, f_{k,m}(x) ≫ x^{m/k}.
    Formally: for every k ≥ 2 and 1 ≤ m < k, there exist c > 0 and x₀
    such that f_{k,m}(x) ≥ c · x^{m/k} for x ≥ x₀. -/
def ErdosProblem323_part2 : Prop :=
    ∀ (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) (hmk : m < k),
      ∃ c : ℚ, 0 < c ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        c * (x : ℚ) ^ ((m : ℚ) / (k : ℚ)) ≤ (powerSumCount k m x : ℚ)

/-- Erdős Problem 323: both parts combined. -/
def ErdosProblem323 : Prop := ErdosProblem323_part1 ∧ ErdosProblem323_part2

/- ## Open sub-question -/

/-- It is unknown whether f_{k,k}(x) = o(x) for k > 2. That is, it is
    open whether the density of sums of k k-th powers is zero. -/
def DensityQuestion (k : ℕ) : Prop :=
    ∀ ε : ℚ, 0 < ε → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (powerSumCount k k x : ℚ) < ε * (x : ℚ)
