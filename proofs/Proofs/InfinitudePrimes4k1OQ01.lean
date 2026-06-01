import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# Fermat's Theorem on Sums of Two Squares (OQ-01)

This file formalizes the full biconditional Fermat two-squares characterization
for odd primes:

  p odd prime → (p % 4 = 1 ↔ ∃ a b : ℕ, p = a² + b²)

The forward direction (hard) follows directly from Mathlib's
`Nat.Prime.sq_add_sq` (`Mathlib/NumberTheory/SumTwoSquares.lean:35`,
pinned at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
The backward direction (easy) is a mod-4 case analysis on `a^2 + b^2`.

Together they strengthen `InfinitudePrimes4k1.lean`, which uses only the
forward direction implicitly via `Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one`.

## Status

- [x] Forward direction (Mathlib wrapper)
- [x] Backward direction (mod-4 case analysis)
- [x] Both wrapped in a single biconditional theorem
- 0 axioms, 0 sorries.

## Mathlib Dependencies

- `Nat.Prime.sq_add_sq` — pinned at `Mathlib/NumberTheory/SumTwoSquares.lean:35`.
- `Nat.Prime.eq_two_or_odd` (Mathlib core).
- `Nat.pow_mod` (Mathlib core).
- Standard tactics: `interval_cases`, `omega`, `rcases`, `obtain`.

## Provenance

Shipped per `research/problems/infinitude-primes-4k1-oq-01/sessions/2026-05-30-s1-observe-mathlib-sumtwosquares-api-survey.md` §4 paste-ready blueprint.
-/

namespace InfinitudePrimes4k1OQ01

open Nat

/-- Squares mod 4 are 0 or 1. -/
lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have h_pow : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := by
    rw [Nat.pow_mod]
  interval_cases (n % 4) <;> omega

/-- **Fermat's Theorem on Sums of Two Squares** (OQ-01 main result).

An odd prime `p` is a sum of two natural-number squares if and only if `p ≡ 1 (mod 4)`. -/
theorem fermat_two_squares (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2) :
    p % 4 = 1 ↔ ∃ a b : ℕ, p = a ^ 2 + b ^ 2 := by
  refine ⟨?_, ?_⟩
  · -- Forward: p % 4 = 1 → ∃ a b, p = a^2 + b^2.
    intro h_mod
    haveI : Fact p.Prime := ⟨hp⟩
    have hne3 : p % 4 ≠ 3 := by omega
    obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hne3
    exact ⟨a, b, hab.symm⟩
  · -- Backward: ∃ a b, p = a^2 + b^2 → p % 4 = 1.
    rintro ⟨a, b, hab⟩
    -- p is odd: p % 2 = 1.
    have hp_odd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    -- Case-split on (a^2 % 4, b^2 % 4) ∈ {(0,0), (0,1), (1,0), (1,1)} via sq_mod_four.
    have ha := sq_mod_four a
    have hb := sq_mod_four b
    -- p = a^2 + b^2 ⇒ p % 4 = (a^2 + b^2) % 4 and p % 2 = (a^2 + b^2) % 2.
    have h_p_mod : p % 4 = (a ^ 2 + b ^ 2) % 4 := by rw [hab]
    have h_p_2 : p % 2 = (a ^ 2 + b ^ 2) % 2 := by rw [hab]
    -- Drop into a^2 % 2 / b^2 % 2 via Nat.pow_mod for the parity step.
    have h_a2_mod2 : a ^ 2 % 2 = (a % 2) ^ 2 % 2 := by rw [Nat.pow_mod]
    have h_b2_mod2 : b ^ 2 % 2 = (b % 2) ^ 2 % 2 := by rw [Nat.pow_mod]
    have hamod : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hbmod : b % 2 < 2 := Nat.mod_lt _ (by norm_num)
    omega

end InfinitudePrimes4k1OQ01
