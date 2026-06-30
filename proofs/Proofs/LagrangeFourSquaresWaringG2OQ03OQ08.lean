/-
Waring's number g(2) = 4 as a sharp least element (OQ-03-OQ-08)

Parent umbrella: `lagrange-four-squares-waring-g2` ("Waring's Problem for Squares:
g(2) = 4").  The umbrella file records the two halves separately — every `n` is a
sum of 4 squares (Lagrange) and `7` is not a sum of 3 squares — but states the
conclusion only as their conjunction, and tags the file `axiomatized` because it
uses `native_decide` for the worked `numSquaresNeeded` examples.

This file gives the **sharp, fully axiom-free** statement.  Define the Waring
predicate `Sufficient k := every natural number is a sum of k squares`.  Then `g(2)`,
the *least* `k` with this property, is exactly `4`:

  * `g2_isLeast`   : `IsLeast {k | Sufficient k} 4`
  * `waring_g2`    : `sInf {k | Sufficient k} = 4`

The upper bound is Lagrange's four-square theorem (`Nat.sum_four_squares`).  The
lower bound is genuinely sharp: no `k ≤ 3` can suffice, because a representation of
`7` by `k ≤ 3` squares would, after padding with zeros, give `7 = x² + y² + z²`,
impossible modulo `8` (squares are `0, 1, 4 (mod 8)` and no three of those sum to
`7`).  Everything is checked with `decide`/`omega` only — no `native_decide`, so the
result is `0`-axiom (`#print axioms` lists only `propext`/`Classical`/`Quot`).

Main results:
* `IsSumOfSquares` (def), `IsSumOfSquares.mono` — representability by `k` squares is
  monotone in `k` (padding with zeros).
* `four_squares_universal` — every `n` is a sum of `4` squares.
* `seven_not_three` — `7` is not a sum of `3` squares.
* `g2_isLeast`, `waring_g2` — the sharp value `g(2) = 4`.
-/

import Mathlib

namespace WaringG2Sharp

open Finset

/-- `n` is a sum of `k` perfect squares. -/
def IsSumOfSquares (k n : ℕ) : Prop := ∃ f : Fin k → ℕ, ∑ i, (f i) ^ 2 = n

/-- Padding with a zero square: a sum of `k` squares is also a sum of `k + 1` squares. -/
theorem IsSumOfSquares.succ {k n : ℕ} (h : IsSumOfSquares k n) :
    IsSumOfSquares (k + 1) n := by
  obtain ⟨f, hf⟩ := h
  refine ⟨Fin.snoc f 0, ?_⟩
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, hf]

/-- Representability by `k` squares is monotone in `k`. -/
theorem IsSumOfSquares.mono {k l n : ℕ} (hkl : k ≤ l) (h : IsSumOfSquares k n) :
    IsSumOfSquares l n := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hkl
  clear hkl
  induction d with
  | zero => simpa using h
  | succ d ih => rw [Nat.add_succ]; exact ih.succ

/-- **Upper bound (Lagrange 1770).** Every natural number is a sum of four squares. -/
theorem four_squares_universal (n : ℕ) : IsSumOfSquares 4 n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨![a, b, c, d], by rw [Fin.sum_univ_four]; simpa using h⟩

/-- **Sharp lower-bound witness.** `7` is not a sum of three squares: reducing modulo
`8`, the only squares are `0, 1, 4`, and no three of them sum to `7`. -/
theorem seven_not_three : ¬ IsSumOfSquares 3 7 := by
  rintro ⟨f, hf⟩
  rw [Fin.sum_univ_three] at hf
  have h8 := congrArg (Nat.cast : ℕ → ZMod 8) hf
  push_cast at h8
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  exact key _ _ _ h8

/-- The set of "sufficient" square-counts: those `k` for which **every** natural
number is a sum of `k` squares. -/
def Sufficient (k : ℕ) : Prop := ∀ n, IsSumOfSquares k n

/-- **Waring's theorem for squares, sharp form: `g(2) = 4`.**
`4` is the least number of squares that suffices to represent every natural number.
The upper bound is Lagrange's four-square theorem; the lower bound is sharp because
no `k ≤ 3` works (else `7` would be a sum of `≤ 3` squares). -/
theorem g2_isLeast : IsLeast {k | Sufficient k} 4 := by
  constructor
  · exact four_squares_universal
  · intro k hk
    by_contra hlt
    push_neg at hlt
    exact seven_not_three ((hk 7).mono (by omega))

/-- The Waring number for squares as an infimum: `g(2) = 4`. -/
theorem waring_g2 : sInf {k | Sufficient k} = 4 :=
  g2_isLeast.csInf_eq

/-- Human-readable restatement of the two halves. -/
theorem four_squares_suffice : Sufficient 4 := four_squares_universal

theorem three_squares_insufficient : ¬ Sufficient 3 := fun h => seven_not_three (h 7)

end WaringG2Sharp
