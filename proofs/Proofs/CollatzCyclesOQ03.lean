/-
# Collatz Cycles OQ-03: No All-Odd Cycle

For the parent `Proofs/CollatzCycles.lean`, this companion file proves the
parity intersection corollary: every Collatz cycle visits at least one even
number. The proof is two omega steps from the parent's `collatz_odd` lemma.

## Results

1. `three_n_plus_one_even`: for odd n, 3n+1 is even.
2. `collatz_of_odd_is_even`: for odd n, collatz n is even.
3. `no_all_odd_cycle`: a periodic orbit cannot be entirely odd.
4. `cycle_contains_even`: every cycle visits an even number.
5. `isPeriodic_contains_even`: same, packaged with `IsPeriodic`.

## References

- Parent: `Proofs/CollatzCycles.lean` (Parts I–VIII).
- Lagarias (1985), *The 3x+1 problem and its generalizations*.
-/

import Mathlib.Tactic
import Proofs.CollatzCycles

namespace CollatzCycles

/-- Parity flip: `3n+1` is even when `n` is odd. -/
lemma three_n_plus_one_even {n : ℕ} (h : n % 2 = 1) :
    (3 * n + 1) % 2 = 0 := by omega

/-- For odd `n`, `collatz n` is even. -/
theorem collatz_of_odd_is_even {n : ℕ} (h : n % 2 = 1) :
    (collatz n) % 2 = 0 := by
  rw [collatz_odd h]
  exact three_n_plus_one_even h

/-- **No all-odd Collatz cycle.** If every iterate of `n` up to step `k` is
    odd and `collatz^[k] n = n`, then we derive a contradiction (the
    iterate at step 1 must be even, since the iterate at step 0 = `n` is
    odd). -/
theorem no_all_odd_cycle {n k : ℕ} (hk : k ≥ 1)
    (hper : collatzIter k n = n)
    (hodd_all : ∀ i, i < k → (collatzIter i n) % 2 = 1) : False := by
  have h0 : n % 2 = 1 := by
    have h := hodd_all 0 hk
    simp [collatzIter, Function.iterate_zero] at h
    exact h
  have h1 : (collatzIter 1 n) % 2 = 0 := by
    show (collatz^[1] n) % 2 = 0
    rw [Function.iterate_one]
    exact collatz_of_odd_is_even h0
  rcases Nat.lt_or_ge 1 k with hk2 | hk1
  · -- k ≥ 2: parity at step 1 contradicts hodd_all
    have hopp := hodd_all 1 hk2
    omega
  · -- k = 1: collatzIter 1 n = n, so n is even (from h1) and odd (from h0)
    interval_cases k
    have heq : collatzIter 1 n = n := hper
    have hn_even : n % 2 = 0 := heq ▸ h1
    omega

/-- **Positive form.** Every Collatz cycle of length ≥ 1 visits at least
    one even number. -/
theorem cycle_contains_even {n k : ℕ} (hk : k ≥ 1)
    (hper : collatzIter k n = n) :
    ∃ i, i < k ∧ (collatzIter i n) % 2 = 0 := by
  by_contra hne
  push_neg at hne
  apply no_all_odd_cycle hk hper
  intro i hi
  have hmod := hne i hi
  -- hmod : (collatzIter i n) % 2 ≠ 0, so it must be 1.
  omega

/-- Repackaged with `IsPeriodic`. -/
theorem isPeriodic_contains_even {n k : ℕ} (hper : IsPeriodic n k) :
    ∃ i, i < k ∧ (collatzIter i n) % 2 = 0 :=
  cycle_contains_even hper.1 hper.2

end CollatzCycles
