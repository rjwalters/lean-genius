/-
  Connecting the exponential prime bound to the Chebyshev functions θ and ψ
  =========================================================================

  Open question (prime-gap-bounds, OQ #3):
    "Connect the exponential bound p_n ≤ 2^(n+1) to the Chebyshev functions
     θ(x) and ψ(x)."

  The parent entry `PrimeGapBounds` proves, by elementary induction from
  Bertrand's postulate, the exponential bound on the n-th prime

      PrimeGapBounds.nth_prime_le_two_pow_succ : nth Prime n ≤ 2 ^ (n + 1).

  Mathlib v4.26.0's `Mathlib.NumberTheory.Chebyshev` develops the two Chebyshev
  prime-power summatory functions

      ψ(x) = ∑_{p^k ≤ x} log p,        θ(x) = ∑_{p ≤ x} log p

  together with the elementary upper bounds θ(x) ≤ x·log 4 and
  ψ(x) ≤ (log 4 + 4)·x, and the identity θ(x) = log (primorial ⌊x⌋₊).

  This file plugs the parent's exponential prime bound into that machinery to
  obtain *two-sided* control of θ, ψ, and the primorial **evaluated at the
  n-th prime**:

    • θ(p_n) ≤ (log 4)·2^(n+1)                          [Chebyshev upper bound]
    • (n+1)·log 2 ≤ θ(p_n)                              [counting lower bound]
    • ψ(p_n) ≤ (log 4 + 4)·2^(n+1)                       [Chebyshev upper bound]
    • θ(p_n) ≤ ψ(p_n)                                    [θ ≤ ψ]
    • 2^(n+1) ≤ primorial p_n ≤ 4^(2^(n+1))             [doubly-exponential]

  The lower bounds rest on the exact prime count
      #{ p ≤ p_n : p prime } = n + 1,
  which we read off from `Nat.primeCounting'_nth_eq` and `Nat.count_succ`.

  Everything is fully verified: 0 sorries, 0 `axiom` declarations, no
  `native_decide`.  `#print axioms` reports only the foundational
  [propext, Classical.choice, Quot.sound].
-/
import Mathlib
import Proofs.PrimeGapBounds

open Nat Chebyshev Finset

namespace PrimeGapBoundsOQ03

/-- The exponential bound on the n-th prime, cast to the reals. -/
theorem nth_prime_le_two_pow_succ_real (n : ℕ) :
    (Nat.nth Nat.Prime n : ℝ) ≤ 2 ^ (n + 1) := by
  exact_mod_cast PrimeGapBounds.nth_prime_le_two_pow_succ n

/-! ### θ at the n-th prime -/

/-- **Chebyshev upper bound at the n-th prime.**  Combining θ-monotonicity with
the exponential prime bound `p_n ≤ 2^(n+1)` and Mathlib's `θ(x) ≤ x·log 4`. -/
theorem theta_nth_prime_le (n : ℕ) :
    θ (Nat.nth Nat.Prime n) ≤ Real.log 4 * 2 ^ (n + 1) := by
  calc θ (Nat.nth Nat.Prime n)
      ≤ θ ((2 : ℝ) ^ (n + 1)) := theta_mono (nth_prime_le_two_pow_succ_real n)
    _ ≤ Real.log 4 * 2 ^ (n + 1) := theta_le_log4_mul_x (by positivity)

/-! ### The exact prime count below `p_n` and the primorial sandwich -/

/-- There are exactly `n + 1` primes `≤ p_n` (the primes `p_0, …, p_n`).  This is
the combinatorial input for both the primorial lower bound and the θ lower bound. -/
theorem prime_count_nth_prime (n : ℕ) :
    ((Finset.range (Nat.nth Nat.Prime n + 1)).filter (fun p => Nat.Prime p)).card
      = n + 1 := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_succ,
      if_pos (Nat.prime_nth_prime n)]
  have hc : Nat.count Nat.Prime (Nat.nth Nat.Prime n) = n :=
    Nat.primeCounting'_nth_eq n
  omega

/-- **Lower bound on the primorial.**  The product of the `n + 1` primes `≤ p_n`
is at least `2^(n+1)`, since each prime is `≥ 2`. -/
theorem two_pow_le_primorial (n : ℕ) :
    2 ^ (n + 1) ≤ primorial (Nat.nth Nat.Prime n) := by
  have hge := Finset.pow_card_le_prod
      ((Finset.range (Nat.nth Nat.Prime n + 1)).filter (fun p => Nat.Prime p))
      (fun p => p) 2
      (fun p hp => (Finset.mem_filter.mp hp).2.two_le)
  calc 2 ^ (n + 1)
      = 2 ^ ((Finset.range (Nat.nth Nat.Prime n + 1)).filter
              (fun p => Nat.Prime p)).card := by rw [prime_count_nth_prime]
    _ ≤ primorial (Nat.nth Nat.Prime n) := by unfold primorial; exact hge

/-- **Upper bound on the primorial.**  Mathlib's `primorial_le_4_pow` together
with the exponential prime bound gives the doubly-exponential bound
`primorial p_n ≤ 4^(2^(n+1))`. -/
theorem primorial_nth_prime_le (n : ℕ) :
    primorial (Nat.nth Nat.Prime n) ≤ 4 ^ (2 ^ (n + 1)) := by
  calc primorial (Nat.nth Nat.Prime n)
      ≤ 4 ^ (Nat.nth Nat.Prime n) := primorial_le_4_pow _
    _ ≤ 4 ^ (2 ^ (n + 1)) :=
        Nat.pow_le_pow_right (by norm_num)
          (PrimeGapBounds.nth_prime_le_two_pow_succ n)

/-- The two-sided doubly-exponential bound on the primorial of the n-th prime. -/
theorem primorial_nth_prime_bounds (n : ℕ) :
    2 ^ (n + 1) ≤ primorial (Nat.nth Nat.Prime n) ∧
      primorial (Nat.nth Nat.Prime n) ≤ 4 ^ (2 ^ (n + 1)) :=
  ⟨two_pow_le_primorial n, primorial_nth_prime_le n⟩

/-- **Lower bound on θ at the n-th prime.**  Via `θ(p_n) = log (primorial p_n)`
and the primorial lower bound `2^(n+1) ≤ primorial p_n`. -/
theorem theta_nth_prime_ge (n : ℕ) :
    (n + 1 : ℝ) * Real.log 2 ≤ θ (Nat.nth Nat.Prime n) := by
  rw [theta_eq_log_primorial, Nat.floor_natCast]
  have h2 : ((2 : ℝ) ^ (n + 1)) ≤ (primorial (Nat.nth Nat.Prime n) : ℝ) := by
    exact_mod_cast two_pow_le_primorial n
  calc (n + 1 : ℝ) * Real.log 2
      = Real.log (2 ^ (n + 1)) := by rw [Real.log_pow]; push_cast; ring
    _ ≤ Real.log (primorial (Nat.nth Nat.Prime n)) :=
        Real.log_le_log (by positivity) h2

/-- The two-sided Chebyshev bound on θ at the n-th prime:
`(n+1)·log 2 ≤ θ(p_n) ≤ (log 4)·2^(n+1)`. -/
theorem theta_nth_prime_bounds (n : ℕ) :
    (n + 1 : ℝ) * Real.log 2 ≤ θ (Nat.nth Nat.Prime n) ∧
      θ (Nat.nth Nat.Prime n) ≤ Real.log 4 * 2 ^ (n + 1) :=
  ⟨theta_nth_prime_ge n, theta_nth_prime_le n⟩

/-! ### ψ at the n-th prime -/

/-- **Chebyshev upper bound on ψ at the n-th prime.**  From Mathlib's
`ψ(x) ≤ (log 4 + 4)·x` and the exponential prime bound. -/
theorem psi_nth_prime_le (n : ℕ) :
    ψ (Nat.nth Nat.Prime n) ≤ (Real.log 4 + 4) * 2 ^ (n + 1) := by
  have h4 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  calc ψ (Nat.nth Nat.Prime n)
      ≤ (Real.log 4 + 4) * (Nat.nth Nat.Prime n) :=
        psi_le_const_mul_self (by positivity)
    _ ≤ (Real.log 4 + 4) * 2 ^ (n + 1) :=
        mul_le_mul_of_nonneg_left (nth_prime_le_two_pow_succ_real n) h4

/-- `θ(p_n) ≤ ψ(p_n)`: the prime-power sum dominates the prime sum. -/
theorem theta_le_psi_nth_prime (n : ℕ) :
    θ (Nat.nth Nat.Prime n) ≤ ψ (Nat.nth Nat.Prime n) :=
  theta_le_psi _

/-- **The full chain at the n-th prime**, exhibiting both Chebyshev functions
sandwiched against the exponential bound:
`(n+1)·log 2 ≤ θ(p_n) ≤ ψ(p_n) ≤ (log 4 + 4)·2^(n+1)`. -/
theorem chebyshev_nth_prime_chain (n : ℕ) :
    (n + 1 : ℝ) * Real.log 2 ≤ θ (Nat.nth Nat.Prime n) ∧
      θ (Nat.nth Nat.Prime n) ≤ ψ (Nat.nth Nat.Prime n) ∧
        ψ (Nat.nth Nat.Prime n) ≤ (Real.log 4 + 4) * 2 ^ (n + 1) :=
  ⟨theta_nth_prime_ge n, theta_le_psi_nth_prime n, psi_nth_prime_le n⟩

end PrimeGapBoundsOQ03
