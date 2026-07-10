import Mathlib

/-
# Erdős #1093 OQ-02 — Factorial growth meta-theorem

Erdős #1093 OQ-02 asks whether the deficiency `d(284, 28) = 9` is the maximal
deficiency of any binomial coefficient `C(n, k)` with `n ≥ 2k`.

A natural proof strategy tries to bound the deficiency using the *sharp* factorial
inequality that governs the size of the relevant products.  This file records a
**negative** structural fact about that strategy: the inequality `(k + D)! ≤ (k!)²`
holds for **every** fixed shift `D` once `k` is large enough (concretely, once
`k ≥ 3·D`).  The shift `D` upper-bounds the width of the deficiency window, so it can
be taken arbitrarily large while the sharp factorial bound `(k + D)! ≤ (k!)²` is
still satisfied.  Hence the sharp bound *alone* cannot pin the maximal deficiency to
any finite value such as `9`: it is compatible with unboundedly large windows, and
some genuinely arithmetic (not merely size-based) input is required.

The proof is entirely elementary — no analytic input.  It combines Mathlib's
`Nat.factorial_mul_ascFactorial` (to split `(k + D)!` as `k! · (k+1).ascFactorial D`)
with `Nat.factorial_mul_pow_le_factorial` (a subtraction-free lower bound on `k!`)
and a clean `2 ^ n ≤ (n + 1)!` helper.

Main results:
* `two_pow_le_succ_factorial`     : `2 ^ n ≤ (n + 1)!`
* `ascFactorial_le_pow`           : `(N+1).ascFactorial D ≤ (N + D) ^ D`
* `ascFactorial_le_factorial`     : for `2 * D ≤ b`, `(b + D + 1).ascFactorial D ≤ (b + D)!`
* `factorial_add_le_sq_factorial` : for `2 * D ≤ b`, `(b + D + D)! ≤ ((b + D)!) ^ 2`
* `exists_factorial_add_le_sq`    : `∀ D, ∃ k₀, ∀ k ≥ k₀, (k + D)! ≤ (k !) ^ 2`
-/

open Nat Finset

namespace Erdos1093OQ02

/-- `2 ^ n ≤ (n + 1)!`: a clean, subtraction-free factorial-dominates-geometric bound,
proved by induction using `(m + 2)! = (m + 2) · (m + 1)!`. -/
theorem two_pow_le_succ_factorial (n : ℕ) : 2 ^ n ≤ (n + 1)! := by
  induction n with
  | zero => simp
  | succ m ih =>
      calc 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
        _ ≤ 2 * (m + 1)! := Nat.mul_le_mul (le_refl 2) ih
        _ ≤ (m + 2) * (m + 1)! := Nat.mul_le_mul (by omega) (le_refl _)
        _ = (m + 1 + 1)! := by rw [Nat.factorial_succ (m + 1)]

/-- The ascending factorial `(N+1)(N+2)⋯(N+D)` is bounded by `(N + D) ^ D`, since each
of its `D` factors is at most `N + D`. -/
theorem ascFactorial_le_pow (N D : ℕ) : (N + 1).ascFactorial D ≤ (N + D) ^ D := by
  rw [Nat.ascFactorial_eq_prod_range]
  calc ∏ i ∈ Finset.range D, (N + 1 + i)
      ≤ ∏ _i ∈ Finset.range D, (N + D) := by
          apply Finset.prod_le_prod
          · intro i _; exact Nat.zero_le _
          · intro i hi; rw [Finset.mem_range] at hi; omega
    _ = (N + D) ^ D := by rw [Finset.prod_const, Finset.card_range]

/-- Key inequality: for `2 * D ≤ b`, the ascending factorial `(b+D+1).ascFactorial D`
is bounded by `(b + D)!`.  The chain is
`(b+D+1).ascFactorial D ≤ (b+2D)^D ≤ (2(b+1))^D = 2^D·(b+1)^D ≤ b!·(b+1)^D ≤ (b+D)!`,
where the middle step uses `b + 2D ≤ 2(b + 1)` (from `2D ≤ b`), the `2^D ≤ b!` step
uses `two_pow_le_succ_factorial`, and the last step is
`Nat.factorial_mul_pow_le_factorial`. -/
theorem ascFactorial_le_factorial (D b : ℕ) (hb : 2 * D ≤ b) :
    (b + D + 1).ascFactorial D ≤ (b + D)! := by
  have h2 : 2 ^ D ≤ b ! := by
    rcases Nat.eq_zero_or_pos D with hD | hD
    · subst hD; simpa using b.factorial_pos
    · calc 2 ^ D ≤ (D + 1)! := two_pow_le_succ_factorial D
        _ ≤ b ! := Nat.factorial_le (by omega)
  calc (b + D + 1).ascFactorial D
      ≤ (b + D + D) ^ D := ascFactorial_le_pow (b + D) D
    _ = (b + 2 * D) ^ D := by rw [show b + D + D = b + 2 * D by ring]
    _ ≤ (2 * (b + 1)) ^ D := Nat.pow_le_pow_left (by omega) D
    _ = 2 ^ D * (b + 1) ^ D := by rw [Nat.mul_pow]
    _ ≤ b ! * (b + 1) ^ D := Nat.mul_le_mul h2 (le_refl _)
    _ ≤ (b + D)! := Nat.factorial_mul_pow_le_factorial

/-- Sharp factorial bound in split form: for `2 * D ≤ b`, `(b + D + D)! ≤ ((b + D)!) ^ 2`.
This is the honest statement `(k + D)! ≤ (k!)²` with `k = b + D`. -/
theorem factorial_add_le_sq_factorial (D b : ℕ) (hb : 2 * D ≤ b) :
    (b + D + D)! ≤ ((b + D)!) ^ 2 := by
  have hsplit : (b + D + D)! = (b + D)! * (b + D + 1).ascFactorial D := by
    rw [← Nat.factorial_mul_ascFactorial (b + D) D]
  rw [hsplit, pow_two]
  exact Nat.mul_le_mul (le_refl _) (ascFactorial_le_factorial D b hb)

/-- **Factorial growth meta-theorem.** For every fixed shift `D`, the sharp factorial
inequality `(k + D)! ≤ (k !) ^ 2` holds for all sufficiently large `k` (any `k ≥ 3·D`).
Since `D` is arbitrary, the sharp bound is compatible with unboundedly large windows and
cannot, by itself, establish any finite maximal deficiency for Erdős #1093 OQ-02. -/
theorem exists_factorial_add_le_sq (D : ℕ) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → (k + D)! ≤ (k !) ^ 2 := by
  refine ⟨3 * D, fun k hk => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + D := ⟨k - D, by omega⟩
  exact factorial_add_le_sq_factorial D b (by omega)

end Erdos1093OQ02
