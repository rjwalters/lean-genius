/-
# Legendre's Conjecture: Equivalent Gap and Distance Forms

This file provides equivalent reformulations of Legendre's Conjecture, all
expressible without any analytic number theory or new axioms. Each equivalence
is a purely structural rewriting of the original, via the identity
`(n+1)^2 = n^2 + 2*n + 1`.

## Forms

| Form | Statement (for each `n ≥ 1`) |
|------|-------------------------------|
| Original (`LegendreAt`) | `∃ p prime, n^2 < p < (n+1)^2` |
| Gap form (`LegendreGapAt`) | `∃ p prime, n^2 < p ≤ n^2 + 2*n` |
| Distance form (`LegendreDistanceAt`) | `∃ p prime, p > n^2 ∧ p - n^2 ≤ 2*n` |
| Half-open form (`LegendreHalfOpenAt`) | `∃ p prime, n^2 + 1 ≤ p ≤ n^2 + 2*n` |

## Why this is useful

1. The **gap form** matches the short-interval style of Hoheisel/Huxley/BHP:
   "prime in `[x, x + h]`" with `h = 2*n` at `x = n^2`.
2. The **distance form** is the form most directly comparable to Cramér's
   conjectured bound `p_{k+1} - p_k ≤ C * (log p_k)^2`.
3. The **half-open form** makes the connection to `Finset.Ico` clear.

## What this file does NOT contain

The deeper equivalence between Legendre's conjecture and a bound on consecutive
prime gaps,

  `LegendreConjecture ↔ ∀ k, nth Prime (k+1) - nth Prime k ≤ 2 * Nat.sqrt (nth Prime k)`,

requires reasoning about consecutive primes and is left as future work. See
`research/problems/bertrands-postulate-oq-02/knowledge.md` Sub-Milestone B.

## Axioms

This file introduces 0 new axioms and depends on none: the "global"
equivalences quantify over the `Prop` `Legendre.LegendreConjecture` itself,
so all results here are unconditional. (A dead `axiom legendre_conjecture`
formerly declared in `LegendrePartial.lean` was never used and has been
removed.)
-/

import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic
import Proofs.LegendrePartial

namespace LegendreGapEquivalence

open Legendre

/-! ## Alternative pointwise forms -/

/-- Gap form at `n`: there is a prime in the half-open interval `(n², n² + 2n]`. -/
def LegendreGapAt (n : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ n^2 < p ∧ p ≤ n^2 + 2*n

/-- Distance form at `n`: there is a prime `p > n²` with `p - n² ≤ 2n`. -/
def LegendreDistanceAt (n : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ p > n^2 ∧ p - n^2 ≤ 2*n

/-- Half-open form at `n`: there is a prime in `[n² + 1, n² + 2n]`. -/
def LegendreHalfOpenAt (n : ℕ) : Prop :=
  ∃ p, Nat.Prime p ∧ n^2 + 1 ≤ p ∧ p ≤ n^2 + 2*n

/-! ## Pointwise equivalences

All four pointwise predicates are equivalent, by the identity
`(n+1)^2 = n^2 + 2*n + 1` and ordinary integer arithmetic. -/

theorem legendreAt_iff_gap (n : ℕ) : LegendreAt n ↔ LegendreGapAt n := by
  unfold LegendreAt LegendreGapAt
  have hexpand : (n+1)^2 = n^2 + 2*n + 1 := by ring
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, h1, ?_⟩
    have : p < n^2 + 2*n + 1 := by rw [← hexpand]; exact h2
    omega
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, h1, ?_⟩
    rw [hexpand]
    omega

theorem legendreAt_iff_distance (n : ℕ) : LegendreAt n ↔ LegendreDistanceAt n := by
  rw [legendreAt_iff_gap]
  unfold LegendreGapAt LegendreDistanceAt
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, h1, ?_⟩
    -- `p ≤ n² + 2n` and `p > n²`, so `p - n² ≤ 2n` (subtraction in ℕ).
    omega
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, h1, ?_⟩
    -- `p > n²` so `n² ≤ p`. With `p - n² ≤ 2n` this gives `p ≤ n² + 2n`.
    omega

theorem legendreAt_iff_halfOpen (n : ℕ) : LegendreAt n ↔ LegendreHalfOpenAt n := by
  rw [legendreAt_iff_gap]
  unfold LegendreGapAt LegendreHalfOpenAt
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, by omega, h2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, by omega, h2⟩

theorem legendreGapAt_iff_distance (n : ℕ) : LegendreGapAt n ↔ LegendreDistanceAt n := by
  rw [← legendreAt_iff_gap, legendreAt_iff_distance]

theorem legendreGapAt_iff_halfOpen (n : ℕ) : LegendreGapAt n ↔ LegendreHalfOpenAt n := by
  rw [← legendreAt_iff_gap, legendreAt_iff_halfOpen]

/-! ## Global equivalences -/

/-- Legendre's Conjecture in gap form. -/
def LegendreGapForm : Prop := ∀ n : ℕ, n ≥ 1 → LegendreGapAt n

/-- Legendre's Conjecture in distance form. -/
def LegendreDistanceForm : Prop := ∀ n : ℕ, n ≥ 1 → LegendreDistanceAt n

/-- Legendre's Conjecture in half-open interval form. -/
def LegendreHalfOpenForm : Prop := ∀ n : ℕ, n ≥ 1 → LegendreHalfOpenAt n

theorem legendre_iff_gap_form : LegendreConjecture ↔ LegendreGapForm := by
  unfold LegendreConjecture LegendreGapForm
  exact ⟨fun h n hn => (legendreAt_iff_gap n).mp (h n hn),
         fun h n hn => (legendreAt_iff_gap n).mpr (h n hn)⟩

theorem legendre_iff_distance_form : LegendreConjecture ↔ LegendreDistanceForm := by
  unfold LegendreConjecture LegendreDistanceForm
  exact ⟨fun h n hn => (legendreAt_iff_distance n).mp (h n hn),
         fun h n hn => (legendreAt_iff_distance n).mpr (h n hn)⟩

theorem legendre_iff_halfOpen_form : LegendreConjecture ↔ LegendreHalfOpenForm := by
  unfold LegendreConjecture LegendreHalfOpenForm
  exact ⟨fun h n hn => (legendreAt_iff_halfOpen n).mp (h n hn),
         fun h n hn => (legendreAt_iff_halfOpen n).mpr (h n hn)⟩

/-! ## Examples: the verified partial cases re-cast in the equivalent forms

The 20 verified base cases in `LegendrePartial.lean` transfer to each of the
equivalent forms via `(legendreAt_iff_*).mp`. We record a representative few
as sanity checks. -/

/-- Gap form at `n = 1`: there is a prime in `(1, 3]`. (Witness: 2 or 3.) -/
theorem legendre_gap_1 : LegendreGapAt 1 := (legendreAt_iff_gap 1).mp legendre_1

/-- Gap form at `n = 5`: there is a prime in `(25, 35]`. (Witness: 29.) -/
theorem legendre_gap_5 : LegendreGapAt 5 := (legendreAt_iff_gap 5).mp legendre_5

/-- Gap form at `n = 20`: there is a prime in `(400, 440]`. (Witness: 401.) -/
theorem legendre_gap_20 : LegendreGapAt 20 := (legendreAt_iff_gap 20).mp legendre_20

/-- Distance form at `n = 10`: there is a prime above 100 within distance 20.
(Witness: 101, distance 1.) -/
theorem legendre_distance_10 : LegendreDistanceAt 10 :=
  (legendreAt_iff_distance 10).mp legendre_10

/-- Half-open form at `n = 15`: there is a prime in `[226, 255]`. (Witness: 227.) -/
theorem legendre_halfOpen_15 : LegendreHalfOpenAt 15 :=
  (legendreAt_iff_halfOpen 15).mp legendre_15

/-! ## A corollary: an explicit gap bound when Legendre holds

When `LegendreAt n` holds, the distance from `n²` to the prime witness is at
most `2n`. This is a *one-sided* gap bound — Legendre does not directly imply a
bound on the gap between consecutive primes (the next prime after `p` could
still be larger than `n² + 2n` if the next square interval starts higher), but
it does imply: every interval starting at a perfect square has a prime within
distance `2n`. -/

theorem legendre_implies_close_prime (n : ℕ) (h : LegendreAt n) :
    ∃ p, Nat.Prime p ∧ p > n^2 ∧ p - n^2 ≤ 2*n := by
  obtain ⟨p, hp, h1, h2⟩ := (legendreAt_iff_distance n).mp h
  exact ⟨p, hp, h1, h2⟩

/-- Conversely, the close-prime bound at `n` implies `LegendreAt n`. -/
theorem close_prime_implies_legendre (n : ℕ)
    (h : ∃ p, Nat.Prime p ∧ p > n^2 ∧ p - n^2 ≤ 2*n) : LegendreAt n :=
  (legendreAt_iff_distance n).mpr h

/-! ## Summary

This file proves:

1. `LegendreAt n ↔ LegendreGapAt n` (interval form ↔ gap-bound form)
2. `LegendreAt n ↔ LegendreDistanceAt n` (interval form ↔ Nat-subtraction form)
3. `LegendreAt n ↔ LegendreHalfOpenAt n` (interval form ↔ closed-interval form)
4. `LegendreConjecture ↔ LegendreGapForm` (global equivalence)
5. `LegendreConjecture ↔ LegendreDistanceForm` (global equivalence)
6. `LegendreConjecture ↔ LegendreHalfOpenForm` (global equivalence)
7. Sample transferrals: the partial cases (`legendre_1, legendre_5, legendre_10,
   legendre_15, legendre_20`) hold in each equivalent form.

### Axiom delta

This file introduces **0 new axioms** and uses none. (The dead axiom
`Legendre.legendre_conjecture` formerly in `LegendrePartial.lean` has been
removed; nothing here ever depended on it.)

### Future work (Sub-Milestone B+)

The next step is the equivalence with the prime-gap function

  `g(p_k) := nth Prime (k+1) - nth Prime k`

namely

  `LegendreConjecture ↔ ∀ k, g(p_k) ≤ 2 * ⌈√(nth Prime k)⌉ + 1`.

This requires reasoning about consecutive primes (the `nth Nat.Prime` function),
and is a strictly harder proof. -/

end LegendreGapEquivalence
