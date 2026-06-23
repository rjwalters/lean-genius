/-
  Taxicab number Ta(2) = 1729  (Hardy–Ramanujan number).

  1729 is the smallest positive integer expressible as a sum of two positive
  cubes in two distinct ways:

      1729 = 1³ + 12³ = 9³ + 10³.

  This is a finite, fully decidable claim. The only nontrivial design point is
  bounding the search: for any `n ≤ 1729`, a representation `n = a³ + b³` with
  `1 ≤ a ≤ b` has `b³ ≤ n ≤ 1729 < 2197 = 13³`, so `a, b ≤ 12`. Hence the search
  may be restricted to the `12 × 12` grid `Finset.Icc 1 12 ×ˢ Finset.Icc 1 12`,
  and `decide` discharges both the value and the minimality.

  Independent numeric certificate:
  `research/problems/taxicab-number-oq-01/verify_taxicab.py` (reps(1729) = {(1,12),
  (9,10)}; no m < 1729 has ≥ 2 reps; cap 12 loses no representation for n ≤ 1729).

  STATUS: build-pending. This file is NOT registered in `Proofs.lean` and has not
  been compiled (Docker pool saturated this session). `decide` is the axiom-free
  primary tactic; if kernel reduction over the ~250k bounded-Nat checks is too
  slow, swap to `native_decide` (introduces `Lean.ofReduceBool`; would make the
  entry `axiomatized` rather than `verified`).
-/
import Mathlib

namespace TaxicabNumberOQ01

/-- Unordered pairs `(a, b)` with `1 ≤ a ≤ b ≤ 12` and `a³ + b³ = n`.

The bound `12` on the summands is sound for every `n ≤ 1729`: any representation
`n = a³ + b³` with `a ≤ b` has `b³ ≤ n ≤ 1729 < 13³`, so `b ≤ 12`. -/
def reps (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 12 ×ˢ Finset.Icc 1 12).filter
    (fun p => p.1 ≤ p.2 ∧ p.1 ^ 3 + p.2 ^ 3 = n)

/-- The two representations of 1729 as a sum of two positive cubes. -/
theorem rep_one : (1 : ℕ) ^ 3 + 12 ^ 3 = 1729 := by norm_num

theorem rep_two : (9 : ℕ) ^ 3 + 10 ^ 3 = 1729 := by norm_num

/-- 1729 has exactly two representations as a sum of two positive cubes. -/
theorem card_reps_1729 : (reps 1729).card = 2 := by decide

/-- No positive integer below 1729 has two distinct representations as a sum of
two positive cubes. Combined with `card_reps_1729`, this is `Ta(2) = 1729`. -/
theorem minimal_below_1729 : ∀ m < 1729, (reps m).card < 2 := by decide

/-- `Ta(2) = 1729`: it is the least `n` with two distinct cube representations. -/
theorem taxicab_two_eq_1729 :
    (2 ≤ (reps 1729).card) ∧ ∀ m < 1729, ¬ 2 ≤ (reps m).card := by
  refine ⟨?_, ?_⟩
  · exact card_reps_1729.ge
  · intro m hm
    have := minimal_below_1729 m hm
    omega

end TaxicabNumberOQ01
