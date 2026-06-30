import Mathlib
import Proofs.SylvesterSequenceOQ01

/-!
# Sylvester's sequence: doubly-exponential growth and the rate of convergence

Sylvester's sequence is `a₀ = 2`, `a_{n+1} = aₙ² - aₙ + 1`, giving `2, 3, 7, 43, 1807, …`.

The parent files establish the *exact* finite identity
`∑_{k≤n} 1/aₖ = 1 - 1/(a_{n+1} - 1)` (`SylvesterSequenceOQ01.syl_partial_sum`)
and the *qualitative* limit `∑' 1/aₙ = 1` (`SylvesterSequenceOQ02`). Neither file
quantifies **how fast** the partial sums approach `1`.

This file supplies that missing quantitative layer, fully machine-checked:

* **Exact gap recurrence** (`syl_sub_one_succ`): `a_{n+1} − 1 = aₙ · (aₙ − 1)`, so the
  gaps `bₙ := aₙ − 1` satisfy `b_{n+1} = bₙ² + bₙ`.

* **Doubly-exponential lower bound** (`two_pow_two_pow_le_syl_sub_one`):
  `2^(2ⁿ) ≤ a_{n+1} − 1`. The squaring `b_{n+1} = bₙ(bₙ+1) ≥ bₙ²` lifts the
  base case `b₁ = 2` to a tower.

* **Doubly-exponential upper bound** (`syl_le_two_pow_two_pow`): `aₙ ≤ 2^(2ⁿ)`,
  from `a_{n+1} = aₙ² − aₙ + 1 ≤ aₙ²`.

* **Quantitative convergence rate** (`syl_error_le`): the truncation error obeys
  `1 − ∑_{k≤n} 1/aₖ ≤ 1 / 2^(2ⁿ)` — a doubly-exponential decay, the sharp
  qualitative shape of Sylvester's constant `E ≈ 1.2640…` with `aₙ ≈ E^(2^{n+1})`.

* **Strict positivity** (`syl_error_pos`): the error is always `> 0`, so no finite
  partial sum ever reaches `1` (the series only converges to `1` in the limit).

No axioms, no sorries, no `native_decide`.
-/

namespace SylvesterSequenceOQ03

open SylvesterSequenceOQ01

/-- Exact recurrence for the gap to `1`: `a_{n+1} − 1 = aₙ · (aₙ − 1)` over `ℤ`.
Equivalently `b_{n+1} = bₙ² + bₙ` for the gaps `bₙ := aₙ − 1`. -/
theorem syl_sub_one_succ (n : ℕ) :
    (syl (n + 1) : ℤ) - 1 = (syl n : ℤ) * ((syl n : ℤ) - 1) := by
  rw [syl_cast_succ]; ring

/-- **Doubly-exponential lower bound.** `2^(2ⁿ) ≤ a_{n+1} − 1` over `ℤ`.

The base case is `b₁ = a₁ − 1 = 2`; the squaring `b_{n+1} = bₙ(bₙ+1) ≥ bₙ²`
turns it into the tower `2, 4, 16, 256, …`. -/
theorem two_pow_two_pow_le_syl_sub_one (n : ℕ) :
    (2 : ℤ) ^ (2 ^ n) ≤ (syl (n + 1) : ℤ) - 1 := by
  induction n with
  | zero =>
    -- `2^(2^0) = 2 ≤ a₁ − 1 = 2`
    norm_num [show syl 1 = 3 from rfl]
  | succ m ih =>
    -- abbreviate the gap `a_{m+1} − 1`
    set t : ℤ := (2 : ℤ) ^ (2 ^ m) with ht
    have ht2 : (2 : ℤ) ≤ t := by
      have : (2 : ℤ) ^ 1 ≤ (2 : ℤ) ^ (2 ^ m) :=
        pow_le_pow_right₀ (by norm_num) (Nat.one_le_two_pow)
      simpa using this
    -- `a_{m+1} ≥ t + 1`, so both factors of `a_{m+1}·(a_{m+1}−1)` dominate `t`
    have hge : t + 1 ≤ (syl (m + 1) : ℤ) := by linarith [ih]
    have hgap : (syl (m + 2) : ℤ) - 1 = (syl (m + 1) : ℤ) * ((syl (m + 1) : ℤ) - 1) :=
      syl_sub_one_succ (m + 1)
    -- exponent bookkeeping: `2^(2^{m+1}) = (2^(2^m))²`
    have hpow : (2 : ℤ) ^ (2 ^ (m + 1)) = t ^ 2 := by
      rw [ht, ← pow_mul, pow_succ]
    rw [hpow, hgap]
    nlinarith [ih, ht2, hge]

/-- **Doubly-exponential upper bound.** `aₙ ≤ 2^(2ⁿ)`.

From `a_{n+1} = aₙ² − aₙ + 1 ≤ aₙ² ≤ (2^(2ⁿ))² = 2^(2^{n+1})`. -/
theorem syl_le_two_pow_two_pow (n : ℕ) : (syl n : ℤ) ≤ (2 : ℤ) ^ (2 ^ n) := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    have hrec : (syl (m + 1) : ℤ) = (syl m : ℤ) ^ 2 - (syl m : ℤ) + 1 := syl_cast_succ m
    have hpos : (1 : ℤ) ≤ (syl m : ℤ) := by exact_mod_cast Nat.one_le_of_lt (two_le_syl m)
    have hpow : (2 : ℤ) ^ (2 ^ (m + 1)) = ((2 : ℤ) ^ (2 ^ m)) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [hpow, hrec]
    nlinarith [ih, hpos]

/-- The gap `a_{n+1} − 1` is a positive rational at least `2^(2ⁿ)`; the casting
bridge used by the convergence estimate. -/
theorem syl_sub_one_pos_rat (n : ℕ) : (0 : ℚ) < (syl (n + 1) : ℚ) - 1 := by
  have h : (2 : ℚ) ≤ (syl (n + 1) : ℚ) := by exact_mod_cast two_le_syl (n + 1)
  linarith

/-- **Quantitative convergence rate.** The truncation error after `n+1` terms is
bounded by a doubly-exponentially small quantity:
`1 − ∑_{k≤n} 1/aₖ ≤ 1 / 2^(2ⁿ)`. -/
theorem syl_error_le (n : ℕ) :
    1 - ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (syl k : ℚ)
      ≤ 1 / (2 : ℚ) ^ (2 ^ n) := by
  -- the parent identity turns the error into the exact gap reciprocal
  have hsum : 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (syl k : ℚ)
      = 1 / ((syl (n + 1) : ℚ) - 1) := by
    rw [syl_partial_sum]; ring
  rw [hsum]
  -- `2^(2ⁿ) ≤ a_{n+1} − 1` as rationals, both positive
  have hle : (2 : ℚ) ^ (2 ^ n) ≤ (syl (n + 1) : ℚ) - 1 := by
    have := two_pow_two_pow_le_syl_sub_one n
    have hcast : ((2 : ℤ) ^ (2 ^ n) : ℚ) ≤ (((syl (n + 1) : ℤ) - 1 : ℤ) : ℚ) := by
      exact_mod_cast this
    push_cast at hcast
    linarith
  have hpos : (0 : ℚ) < (2 : ℚ) ^ (2 ^ n) := by positivity
  exact one_div_le_one_div_of_le hpos hle

/-- **Strict positivity of the error.** Every finite partial sum is strictly below
`1`: the reciprocal series reaches `1` only in the limit, never at a finite stage. -/
theorem syl_error_pos (n : ℕ) :
    0 < 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (syl k : ℚ) := by
  have hsum : 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (syl k : ℚ)
      = 1 / ((syl (n + 1) : ℚ) - 1) := by
    rw [syl_partial_sum]; ring
  rw [hsum]
  exact one_div_pos.mpr (syl_sub_one_pos_rat n)

/-- **Capstone.** Both sides of the doubly-exponential sandwich together with the
matching convergence rate: for every `n`,
`2^(2ⁿ) ≤ a_{n+1} − 1` and `aₙ ≤ 2^(2ⁿ)`, and the error satisfies
`0 < 1 − Sₙ ≤ 2^(−2ⁿ)`. -/
theorem sylvester_doubly_exponential (n : ℕ) :
    (2 : ℤ) ^ (2 ^ n) ≤ (syl (n + 1) : ℤ) - 1
      ∧ (syl n : ℤ) ≤ (2 : ℤ) ^ (2 ^ n)
      ∧ 0 < 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (syl k : ℚ)
      ∧ 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (syl k : ℚ)
          ≤ 1 / (2 : ℚ) ^ (2 ^ n) :=
  ⟨two_pow_two_pow_le_syl_sub_one n, syl_le_two_pow_two_pow n,
   syl_error_pos n, syl_error_le n⟩

end SylvesterSequenceOQ03
