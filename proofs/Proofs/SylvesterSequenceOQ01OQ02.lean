import Mathlib
import Proofs.SylvesterSequenceOQ01

/-!
# Sylvester's sequence, oq-01-oq-02: a doubly-exponential lower bound

The parent entry `sylvester-sequence-oq-01` studied Sylvester's sequence
`a₀ = 2`, `a_{n+1} = aₙ² - aₙ + 1`  (`2, 3, 7, 43, 1807, …`) and proved the
closed-form partial reciprocal sums `∑_{k≤n} 1/aₖ = 1 - 1/(a_{n+1} - 1)`.
It established only the *linear* growth fact `2 ≤ aₙ` needed for coprimality; it
never quantified how fast the sequence actually grows.

Sylvester's sequence roughly **squares** at each step, so it grows
doubly-exponentially.  This entry makes that precise:

  `syl_doubly_exponential` :  `2 ^ (2 ^ (n - 1)) ≤ aₙ`   for `n ≥ 1`.

Numerically the bound is `a₁ ≥ 2, a₂ ≥ 4, a₃ ≥ 16, a₄ ≥ 256, …` against the true
values `3, 7, 43, 1807, …`.

## Method

The obvious induction "`aₙ ≥ 2^{2^{n-1}}`" **fails**: writing `bₙ = 2^{2^{n-1}}`
so that `b_{n+1} = bₙ²`, one needs `a_{n+1} = aₙ² - aₙ + 1 ≥ bₙ²`, but at the
tight point `aₙ = bₙ` the `-aₙ` term breaks it (`bₙ² - bₙ + 1 < bₙ²`).

The remedy is to **strengthen the hypothesis** to absorb the linear term:

  `syl_ge_double_exp_succ` :  `2 ^ (2 ^ n) + 1 ≤ a_{n+1}`.

This invariant is self-sustaining.  With `B = 2^{2ⁿ}` and `a = a_{n+1} ≥ B + 1`,

  `a_{n+2} = a² - a + 1 ≥ (B+1)² - (B+1) + 1 = B² + B + 1 ≥ B² + 1 = 2^{2^{n+1}} + 1`,

using `2^{2^{n+1}} = (2^{2ⁿ})²`.  The base case is the sharp equality `a₁ = 3 = 2 + 1`.

As an application we quantify the convergence rate of the Egyptian-fraction
expansion `∑ 1/aₖ = 1`: the truncation error is itself doubly-exponentially small,

  `syl_reciprocal_error_bound` :
      `1 - ∑_{k≤n} 1/aₖ  ≤  1 / 2 ^ (2 ^ n)`,

because the parent's exact error term `1/(a_{n+1} - 1)` is at most `1/2^{2ⁿ}`.

No axioms, no sorries.
-/

namespace SylvesterSequenceOQ01OQ02

open SylvesterSequenceOQ01

/-- **Strengthened invariant.**  For every `n`, `2^{2ⁿ} + 1 ≤ a_{n+1}`.

The extra `+ 1` over the naive bound `2^{2ⁿ} ≤ a_{n+1}` is exactly what makes the
induction close: it compensates for the `-aₙ` term in the recurrence. -/
theorem syl_ge_double_exp_succ (n : ℕ) : 2 ^ (2 ^ n) + 1 ≤ syl (n + 1) := by
  induction n with
  | zero =>
    -- `a₁ = 3` and `2^{2⁰} + 1 = 3`.
    show 2 ^ (2 ^ 0) + 1 ≤ syl 1
    norm_num [show syl 1 = 3 from rfl]
  | succ k ih =>
    -- Abbreviate `B = 2^{2^k}` and `a = a_{k+1}`; work in `ℤ` to dodge `ℕ` subtraction.
    set B : ℤ := 2 ^ (2 ^ k) with hB
    have hBpos : (1 : ℤ) ≤ B := by
      have h0 : (0 : ℤ) < B := by rw [hB]; positivity
      omega
    have ihZ : B + 1 ≤ (syl (k + 1) : ℤ) := by
      rw [hB]; exact_mod_cast ih
    -- The recurrence lifted to `ℤ`.
    have hrec : (syl (k + 2) : ℤ) = (syl (k + 1) : ℤ) ^ 2 - (syl (k + 1) : ℤ) + 1 :=
      syl_cast_succ (k + 1)
    -- `2^{2^{k+1}} = (2^{2^k})²`.
    have hpow : (2 : ℤ) ^ (2 ^ (k + 1)) = B ^ 2 := by
      rw [hB, ← pow_mul, pow_succ]
    -- Prove the target in `ℤ`, then cast back.
    have goalZ : (2 : ℤ) ^ (2 ^ (k + 1)) + 1 ≤ (syl (k + 2) : ℤ) := by
      rw [hrec, hpow]
      nlinarith [ihZ, hBpos, sq_nonneg ((syl (k + 1) : ℤ) - B - 1)]
    exact_mod_cast goalZ

/-- **Doubly-exponential lower bound.**  For `n ≥ 1`,  `2^{2^{n-1}} ≤ aₙ`. -/
theorem syl_doubly_exponential {n : ℕ} (hn : 1 ≤ n) :
    2 ^ (2 ^ (n - 1)) ≤ syl n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using le_trans (Nat.le_succ _) (syl_ge_double_exp_succ m)

/-- **Doubly-exponential convergence of the reciprocal sum.**

The Egyptian-fraction partial sums `∑_{k≤n} 1/aₖ` converge to `1`, and the
truncation error is at most `1/2^{2ⁿ}` — doubly-exponentially small.  This
sharpens the parent's `Tendsto`-level statement with an explicit rate. -/
theorem syl_reciprocal_error_bound (n : ℕ) :
    (1 : ℚ) - ∑ k ∈ Finset.range (n + 1), 1 / (syl k : ℚ) ≤ 1 / 2 ^ (2 ^ n) := by
  rw [syl_partial_sum]
  -- After rewriting, the left side is exactly the error term `1/(a_{n+1} - 1)`.
  have hden : (2 : ℚ) ^ (2 ^ n) ≤ (syl (n + 1) : ℚ) - 1 := by
    have h : (2 : ℚ) ^ (2 ^ n) + 1 ≤ (syl (n + 1) : ℚ) := by
      exact_mod_cast syl_ge_double_exp_succ n
    linarith
  have hpos : (0 : ℚ) < 2 ^ (2 ^ n) := by positivity
  have : (1 : ℚ) - (1 - 1 / ((syl (n + 1) : ℚ) - 1)) = 1 / ((syl (n + 1) : ℚ) - 1) := by
    ring
  rw [this]
  exact one_div_le_one_div_of_le hpos hden

end SylvesterSequenceOQ01OQ02
