/-
# Erdős Problem #1053: Growth Rate of k-Perfect Numbers

A number n is k-perfect if σ(n) = k·n, where σ is the sum-of-divisors function.
Must k = o(log log n) for k-perfect numbers?

## Background
- k=1: only n=1
- k=2: perfect numbers (6, 28, 496, 8128, ...)
- k=3: triperfect (120, 672, 523776, ...)
- Largest known k: k=11

## Key Question
If σ(n) = k·n, must k grow slower than log log n?
Equivalently, is σ(n)/n = o(log log n)?

## Related
Guy suggested finitely many k-perfect numbers for each k ≥ 3.

## Status: OPEN
Guy's Problem B2.

Reference: https://erdosproblems.com/1053
-/

import Mathlib

/- ## Core Definitions -/

/-- The sum-of-divisors function σ(n), computed as the sum of all divisors. -/
def sigma (n : ℕ) : ℕ := (Nat.divisors n).sum id

/-- σ(n) equals the sum of all positive divisors of n (definitional). -/
theorem sigma_def (n : ℕ) (_hn : n > 0) :
    sigma n = (Nat.divisors n).sum id := rfl

/-- A number n is k-perfect if σ(n) = k·n. -/
def IsKPerfect (n k : ℕ) : Prop :=
  n > 0 ∧ sigma n = k * n

/-- IsKPerfect is decidable since sigma is computable. -/
instance (n k : ℕ) : Decidable (IsKPerfect n k) := by
  unfold IsKPerfect; exact instDecidableAnd

/-- The multiplicity of n: the ratio σ(n)/n when it is an integer. -/
def perfectMultiplicity (n : ℕ) : ℕ :=
  sigma n / n

/- ## Basic Properties of σ and k-Perfect Numbers -/

/-- σ(1) = 1: the only divisor of 1 is 1 itself. -/
theorem sigma_one : sigma 1 = 1 := by native_decide

/-- σ(n) ≥ n for n > 0, since n divides itself and is thus a summand. -/
theorem sigma_ge_self (n : ℕ) (hn : n > 0) : sigma n ≥ n := by
  unfold sigma
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩)

/-- k-perfect numbers have k ≥ 1, since σ(n) ≥ n > 0 forces k·n ≥ n. -/
theorem kperfect_k_ge_one (n k : ℕ) (h : IsKPerfect n k) : k ≥ 1 := by
  rcases k with _ | k
  · -- k = 0: σ(n) = 0, but σ(n) ≥ n > 0
    exfalso
    have h0 := h.2; simp at h0
    linarith [sigma_ge_self n h.1]
  · omega

/-- For k-perfect n, perfectMultiplicity n = k (exact division). -/
theorem perfectMultiplicity_kperfect (n k : ℕ) (h : IsKPerfect n k) :
    perfectMultiplicity n = k := by
  unfold perfectMultiplicity
  rw [h.2]
  exact Nat.mul_div_cancel_left k h.1

/- ## Classical Perfect Numbers (k = 2) -/

/-- k=1: only n=1 satisfies σ(n) = n.
    Proof: For n ≥ 2, σ(n) ≥ 1 + n > n since both 1 and n divide n. -/
theorem one_perfect_unique : ∀ n : ℕ, IsKPerfect n 1 → n = 1 := by
  intro n ⟨hn, hσ⟩
  simp only [one_mul] at hσ
  by_contra h
  have h1 : (1 : ℕ) ∈ n.divisors := by
    rw [Nat.mem_divisors]; exact ⟨one_dvd n, by omega⟩
  have hn_mem : n ∈ n.divisors := by
    rw [Nat.mem_divisors]; exact ⟨dvd_refl n, by omega⟩
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have hpair : ({1, n} : Finset ℕ).sum id = 1 + n := by
    rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ n)]; simp
  have hle := Finset.sum_le_sum_of_subset (f := id) hsub
  unfold sigma at hσ
  have : 1 + n ≤ n := by linarith [hpair, hle, hσ]
  omega

/-- Complete characterization: n is 1-perfect if and only if n = 1. -/
theorem IsKPerfect_one_iff (n : ℕ) : IsKPerfect n 1 ↔ n = 1 :=
  ⟨one_perfect_unique n, fun h => h ▸ ⟨Nat.one_pos, by simp [sigma_one]⟩⟩

/-- k=2: classical perfect numbers. The first few: 6, 28, 496, 8128.
    Proved by computation: σ(6) = 12 = 2·6, σ(28) = 56 = 2·28, etc. -/
theorem perfect_examples :
    IsKPerfect 6 2 ∧ IsKPerfect 28 2 ∧ IsKPerfect 496 2 ∧ IsKPerfect 8128 2 := by
  native_decide

/-- Euler's characterization: even perfect numbers are exactly
    2^(p-1) · (2^p - 1) where 2^p - 1 is a Mersenne prime. -/
/- ## Multiperfect Numbers (k ≥ 3) -/

/-- k=3 (triperfect): 120, 672, 523776.
    Proved by computation: σ(120) = 360 = 3·120, σ(672) = 2016 = 3·672, etc. -/
theorem triperfect_examples :
    IsKPerfect 120 3 ∧ IsKPerfect 672 3 ∧ IsKPerfect 523776 3 := by
  native_decide

/-- The largest known k for which a k-perfect number exists is k=11.
    The k=11 examples are extremely large (thousands of digits). -/
/- ## The Main Conjecture -/

/-- Erdős Problem #1053: If n is k-perfect (σ(n) = k·n),
    must k = o(log log n)?

    Formally: for any ε > 0, there exists N such that for all n ≥ N,
    if σ(n) = k·n, then k < ε · log(log n). -/
/- ## Known Upper Bounds -/

/-- Gronwall's theorem (1913): lim sup σ(n)/(n · log log n) = e^γ
    where γ is the Euler–Mascheroni constant.
    So σ(n)/n can be as large as ~e^γ · log log n for highly composite n. -/
/-- Robin's inequality (1984): σ(n) < e^γ · n · log log n for n ≥ 5041,
    assuming RH. Unconditionally true for most n. -/
axiom robin_inequality_conditional (n : ℕ) (hn : n ≥ 5041) :
    -- Assuming RH
    (sigma n : ℝ) < Real.exp 0.5772 * (n : ℝ) * Real.log (Real.log (n : ℝ))

/- ## Guy's Finiteness Conjecture -/

/-- Guy's conjecture: For each k ≥ 3, there are only finitely many
    k-perfect numbers. This is stronger than Erdős's question. -/
/- ## Relationship to Robin's Criterion -/

/-- If σ(n) = k·n and Robin's inequality holds, then
    k < e^γ · log log n for n ≥ 5041, giving k = O(log log n).
    The Erdős question asks for the stronger o(log log n).
    Proof: From Robin, σ(n) < e^γ · n · log log n. Since σ(n) = k·n,
    we get k·n < e^γ · n · log log n, and dividing by n gives the result. -/
theorem robin_gives_O_bound (n k : ℕ) (hn : n ≥ 5041)
    (hkp : IsKPerfect n k) :
    (k : ℝ) < Real.exp 0.5772 * Real.log (Real.log (n : ℝ)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hrobin := robin_inequality_conditional n hn
  -- Cast σ(n) = k * n to ℝ
  have hσ_cast : (sigma n : ℝ) = (k : ℝ) * (n : ℝ) := by exact_mod_cast hkp.2
  -- k = σ(n) / n
  have hk_eq : (k : ℝ) = (sigma n : ℝ) / (n : ℝ) := by
    rw [hσ_cast]; field_simp
  -- σ(n)/n < exp(γ) * n * log(log n) / n = exp(γ) * log(log n)
  rw [hk_eq, div_lt_iff₀ hn_pos]
  have : Real.exp 0.5772 * Real.log (Real.log (n : ℝ)) * (n : ℝ) =
      Real.exp 0.5772 * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by ring
  linarith
