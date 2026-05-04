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

/-- Every nonneg integer is a sum of itself many 1st powers: f_{1,m} grows
    linearly for m large enough.
    Proof: every n is IsSumOfPowers n 1 m (put n on index 0, rest 0),
    so the filter keeps all of {0,...,x}, giving card = x+1 ≥ m. -/
theorem first_power_count (m x : ℕ) (hm : 1 ≤ m) (hx : m ≤ x) :
    m ≤ powerSumCount 1 m x := by
  unfold powerSumCount
  suffices h : ∀ n, IsSumOfPowers n 1 m by
    rw [Finset.filter_true_of_mem (fun n _ => h n), Finset.card_range]; omega
  intro n
  exact ⟨fun i => if i = ⟨0, by omega⟩ then n else 0, by
    simp [pow_one, Finset.sum_ite_eq', Finset.mem_univ]⟩

/-- Monotonicity: f_{k,m}(x) ≤ f_{k,m+1}(x) for k ≥ 1.
    Proof: extend witness by appending 0 (0^k = 0 when k ≥ 1).
    Note: requires k ≥ 1 since for k = 0, IsSumOfPowers n 0 m ↔ n = m
    (each term is 0^0 = 1), so f_{0,m}(x) counts only {m} while
    f_{0,m+1}(x) counts only {m+1}, violating monotonicity at m = x. -/
theorem power_sum_count_mono (k m x : ℕ) (hk : 1 ≤ k) :
    powerSumCount k m x ≤ powerSumCount k (m + 1) x := by
  unfold powerSumCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, by
    obtain ⟨xs, hxs⟩ := hn.2
    exact ⟨Fin.snoc xs 0, by
      rw [hxs, Fin.sum_univ_castSucc]
      simp [Fin.snoc_castSucc, Fin.snoc_last, zero_pow (show k ≠ 0 by omega)]⟩⟩

/- ## Special case: sums of exactly 1 k-th power -/

/-- IsSumOfPowers n k 1 iff n is a perfect k-th power. -/
theorem IsSumOfPowers_one_iff (n k : ℕ) :
    IsSumOfPowers n k 1 ↔ ∃ a : ℕ, n = a ^ k := by
  simp only [IsSumOfPowers, Fin.sum_univ_one]
  constructor
  · rintro ⟨xs, h⟩; exact ⟨xs 0, h⟩
  · rintro ⟨a, h⟩; exact ⟨fun _ => a, h⟩

/-- Every perfect k-th power is a sum of 1 k-th power. -/
lemma isSumOfPowers_pow_self (a k : ℕ) : IsSumOfPowers (a ^ k) k 1 :=
  IsSumOfPowers_one_iff.mpr ⟨a, rfl⟩

/-- Lower bound for 1-sum count: f_{k,1}(n^k) ≥ n+1, since the n+1 values
    {0^k, 1^k, ..., n^k} are distinct elements of [0, n^k].
    This is the m=1 case of Conjecture 2 (up to integrality). -/
theorem powerSumCount_one_lb (k n : ℕ) (hk : 1 ≤ k) :
    n + 1 ≤ powerSumCount k 1 (n ^ k) := by
  unfold powerSumCount
  have hMono : StrictMono (fun a : ℕ => a ^ k) := fun a b hab =>
    Nat.pow_lt_pow_left hab (by omega)
  have hcard : ((Finset.range (n + 1)).image (· ^ k)).card = n + 1 := by
    rw [Finset.card_image_of_injective _ hMono.injective, Finset.card_range]
  have hsubset : (Finset.range (n + 1)).image (· ^ k) ⊆
      (Finset.range (n ^ k + 1)).filter (fun m => IsSumOfPowers m k 1) := by
    intro m hm
    simp only [Finset.mem_image, Finset.mem_range] at hm
    obtain ⟨a, ha, rfl⟩ := hm
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.pow_le_pow_left (by omega) k),
           isSumOfPowers_pow_self a k⟩
  linarith [Finset.card_le_card hsubset, hcard.symm.le]

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
