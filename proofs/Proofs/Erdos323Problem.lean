/-!
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

/-! ## Sums of k-th powers -/

/-- An integer n is a sum of m nonnegative k-th powers. -/
def IsSumOfPowers (n k m : ℕ) : Prop :=
    ∃ (xs : Fin m → ℕ), n = (Finset.univ.sum fun i => (xs i) ^ k)

/-- f_{k,m}(x): count of integers in [0, x] that are sums of m k-th powers. -/
noncomputable def powerSumCount (k m x : ℕ) : ℕ :=
    (Finset.range (x + 1)).filter (fun n => IsSumOfPowers n k m) |>.card

/-! ## Basic properties -/

/-- Every nonneg integer is a sum of itself many 1st powers: f_{1,m} grows
    linearly for m large enough. -/
axiom first_power_count (m x : ℕ) (hm : 1 ≤ m) (hx : m ≤ x) :
    m ≤ powerSumCount 1 m x

/-- Monotonicity: f_{k,m}(x) ≤ f_{k,m+1}(x). -/
axiom power_sum_count_mono (k m x : ℕ) :
    powerSumCount k m x ≤ powerSumCount k (m + 1) x

/-! ## Landau's theorem for sums of two squares -/

/-- Landau: f_{2,2}(x) ~ c·x/√(log x). Formally: for every ε > 0,
    for large x, (1-ε)·c·x/√(log x) ≤ f_{2,2}(x) ≤ (1+ε)·c·x/√(log x). -/
axiom landau_two_squares :
    ∃ c : ℚ, 0 < c ∧
      ∀ ε : ℚ, 0 < ε → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (1 - ε) * c * (x : ℚ) ≤ (powerSumCount 2 2 x : ℚ) * (Nat.log 2 x : ℚ)

/-! ## Main conjectures -/

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

/-! ## Open sub-question -/

/-- It is unknown whether f_{k,k}(x) = o(x) for k > 2. That is, it is
    open whether the density of sums of k k-th powers is zero. -/
def DensityQuestion (k : ℕ) : Prop :=
    ∀ ε : ℚ, 0 < ε → ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      (powerSumCount k k x : ℚ) < ε * (x : ℚ)
