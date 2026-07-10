import Mathlib

/-
# Jacobi four-square RHS: the elementary lower bound  (OQ-01 → OQ-03, continued)

`LagrangeFourSquaresOQ01OQ03.lean` defines the right-hand side of Jacobi's
four-square formula, `jacobiCount n = 8·Σ_{d|n, 4∤d} d`, and the companion
`LagrangeFourSquaresOQ01OQ03Even.lean` pins its closed form on every `n`. Both
leave the general `r4 = jacobiCount` equality Mathlib-blocked (≫1000 LOC of new
quaternion-order or weight-2 modular-form theory).

This file adds the elementary, 0-axiom **lower bound**: the Jacobi RHS is at least
`8` for every `n ≥ 1`, hence strictly positive. The divisor `1` is never divisible
by `4`, so it always survives the Jacobi filter and contributes `8·1 = 8`. This is
the RHS reflection of Lagrange's four-square theorem: every positive integer admits
at least `8` ordered signed four-square representations (the sign/permutation orbit
of any single representation of a positive square already has size ≥ 8), so a
faithful count formula must stay `≥ 8`. `jacobiCount` is restated verbatim to keep
the file self-contained.

Tags: number-theory, jacobi, four-squares, divisor-sum, lower-bound
-/

namespace LagrangeFourSquaresOQ01OQ03Bound

open Finset

/-- The right-hand side of Jacobi's four-square formula:
`jacobiCount n = 8 · Σ_{d ∣ n, 4 ∤ d} d` (restated from the base file). -/
def jacobiCount (n : ℕ) : ℕ :=
  8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d

/-- `1` is always a divisor of a positive `n` and is never divisible by `4`, so it
survives the Jacobi filter `4 ∤ d`. -/
theorem one_mem_filter {n : ℕ} (hn : n ≠ 0) :
    (1 : ℕ) ∈ n.divisors.filter (fun d => ¬ 4 ∣ d) := by
  rw [mem_filter, Nat.mem_divisors]
  exact ⟨⟨one_dvd n, hn⟩, by decide⟩

/-- **Elementary lower bound.**  For every `n ≥ 1` the Jacobi RHS satisfies
`8 ≤ jacobiCount n`: the unfiltered divisor `1` alone contributes `8`.  This is the
right-hand-side witness that Jacobi's formula is consistent with Lagrange's theorem
(every positive `n` has at least `8` signed four-square representations). -/
theorem eight_le_jacobiCount {n : ℕ} (hn : n ≠ 0) : 8 ≤ jacobiCount n := by
  have hle : 1 ≤ ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d :=
    Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) (one_mem_filter hn)
  unfold jacobiCount
  omega

/-- **Positivity.**  The Jacobi RHS is strictly positive on every positive `n`. -/
theorem jacobiCount_pos {n : ℕ} (hn : n ≠ 0) : 0 < jacobiCount n :=
  lt_of_lt_of_le (by norm_num) (eight_le_jacobiCount hn)

/-- **Every Jacobi count is a multiple of `8`.**  Immediate from the shape
`jacobiCount n = 8·Σ…`.  Arithmetically this is the reason the lower bound is exactly
`8` rather than `1`: signed four-square representations come in sign/permutation orbits,
and the count is an integer number of size-`8` orbits.  (Combined with
`eight_le_jacobiCount`, on every `n ≥ 1` the count is a *positive* multiple of `8`.) -/
theorem eight_dvd_jacobiCount (n : ℕ) : 8 ∣ jacobiCount n := by
  unfold jacobiCount
  exact dvd_mul_right 8 _

/-- **Elementary upper bound.**  The Jacobi RHS never exceeds `8·σ₁(n)`, i.e.
`jacobiCount n ≤ 8·Σ_{d ∣ n} d`: the filter `4 ∤ d` can only *drop* divisor terms from
the full divisor sum, never add them.  Together with `eight_le_jacobiCount` this sandwiches
the count, `8 ≤ jacobiCount n ≤ 8·σ₁(n)` for `n ≥ 1`, with equality at the top exactly when
no divisor of `n` is a multiple of `4` (e.g. every odd `n`). -/
theorem jacobiCount_le_eight_mul_sigma (n : ℕ) :
    jacobiCount n ≤ 8 * ∑ d ∈ n.divisors, d := by
  have h : (∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d) ≤ ∑ d ∈ n.divisors, d :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  unfold jacobiCount
  omega

/-- Sanity check: `jacobiCount 1 = 8`, so the lower bound is attained at `n = 1`. -/
example : jacobiCount 1 = 8 := by decide

end LagrangeFourSquaresOQ01OQ03Bound
