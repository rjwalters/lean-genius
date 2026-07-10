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

/-- Sanity check: `jacobiCount 1 = 8`, so the lower bound is attained at `n = 1`. -/
example : jacobiCount 1 = 8 := by decide

end LagrangeFourSquaresOQ01OQ03Bound
