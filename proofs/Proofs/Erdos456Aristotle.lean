/-
  Aristotle targets for Erdős Problem #456
  Routine supporting lemmas for automated proof search.
  See Erdos456Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result or standard technique
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Rat.Order
import Mathlib.Data.Finset.Card

open Nat Set

namespace Erdos456Aristotle

open Classical in
noncomputable section

-- ═══════════════════════════════════════════════════════════════════════
-- Definitions (duplicated from main file for self-containment)
-- ═══════════════════════════════════════════════════════════════════════

def smallestTotientDiv (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ m.totient}

def smallestPrimeMod1 (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ n ∣ (p - 1)}

-- ═══════════════════════════════════════════════════════════════════════
-- Target 1: van Doorn's φ(2^{2k+2}) = 2^{2k+1}
--
-- Needs: Nat.totient_prime_pow_succ and arithmetic
-- Strategy: 2*n = 2^(2k+2), φ(2^(2k+2)) = 2^(2k+1) * (2-1) = n
-- ═══════════════════════════════════════════════════════════════════════

/-- φ(2^(m+1)) = 2^m for all m.
    From Nat.totient_prime_pow_succ with p = 2. -/
theorem totient_two_pow_succ (m : ℕ) :
    Nat.totient (2 ^ (m + 1)) = 2 ^ m := by
  sorry

/-- 2 * 2^k = 2^(k+1) — basic power arithmetic. -/
theorem two_mul_two_pow (k : ℕ) :
    2 * 2 ^ k = 2 ^ (k + 1) := by
  sorry

-- ═══════════════════════════════════════════════════════════════════════
-- Target 2: AlmostAll counting argument
--
-- If exceptions have density < ε for any ε > 0, then for any N,
-- there exists n ≥ N satisfying the property.
-- Strategy: Take ε = 1/(2N+2), get N₀, take M = max(N₀, 2N+1).
-- Exceptions < M/2, but [0,N) has at most N elements, so some n ≥ N works.
-- ═══════════════════════════════════════════════════════════════════════

/-- If the density of exceptions in [0, M) is less than half, and M > 2N,
    then some element in [N, M) satisfies the property. -/
theorem density_implies_witness (P : ℕ → Prop) (N M : ℕ)
    (hM : 2 * N < M)
    (hcount : (Finset.filter (fun n => ¬P n) (Finset.range M)).card * 2 < M) :
    ∃ n, N ≤ n ∧ n < M ∧ P n := by
  sorry

end

end Erdos456Aristotle
