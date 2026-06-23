import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic

/-
# Counting Compositions: there are 2^(n−1) compositions of n

## What This Proves

A *composition* of a natural number `n` is an ordered tuple of positive integers
summing to `n` (Mathlib's `Composition n`). The classical enumerative fact is that
the number of compositions of `n` is `2 ^ (n − 1)`:

  Fintype.card (Composition n) = 2 ^ (n − 1).

The standard bijective proof inserts a "bar or no bar" into each of the `n − 1`
gaps between `n` unit boxes `□|□ □|□ …`, so a composition is the same data as a
subset of the `n − 1` internal gaps — hence `2 ^ (n − 1)` of them.

## What Mathlib Already Has — and What This Adds

Mathlib supplies the headline count as `composition_card`, proved through the
chain `Composition n ≃ CompositionAsSet n` (`compositionEquiv`) and
`compositionAsSet_card : Fintype.card (CompositionAsSet n) = 2 ^ (n − 1)`. That
single equation is re-exported here as `card_composition_eq` so the result has a
named home in the gallery.

Beyond the re-export, Mathlib does **not** record the structural consequences of
the closed form, which is what this file derives:

* the **doubling recurrence** `card (Composition (n+2)) = 2 · card (Composition (n+1))`
  — each additional unit of `n` doubles the number of compositions (for `n ≥ 1`);
* **positivity** `0 < card (Composition n)` — every `n` (including `0`) has at
  least one composition;
* the count as a genuine **bijective** statement `card (Composition n) =
  card (CompositionAsSet n)`, exposing the "subset of the gaps" model; and
* concrete cardinalities for `n = 1, …, 5` (`1, 2, 4, 8, 16`).

The doubling recurrence is the combinatorial heart of `2 ^ (n−1)`: it is exactly
the statement "splitting the last box off either starts a new part or extends the
current one", and it is the recurrence one would use to prove the count from
scratch. Note it genuinely requires `n ≥ 1`: the step from `0` to `1` does *not*
double (`card (Composition 1) = 1 ≠ 2 = 2 · card (Composition 0)` would be false,
since `card (Composition 0) = 2 ^ (0−1) = 2 ^ 0 = 1` because subtraction on ℕ is
truncated). The `n+2` phrasing below sidesteps the edge case cleanly.

## Status
- [x] Complete proof (0 sorries, 0 axiom declarations)
- [x] Headline count re-exported from Mathlib (`composition_card`)
- [x] Original derived corollaries: doubling recurrence, positivity, bijection form
- [x] Pedagogical / worked numeric instances
-/

namespace CompositionCard2PowOQ01

/-! ## The headline count (re-exported from Mathlib) -/

/-- **The number of compositions of `n` is `2 ^ (n − 1)`.** This is Mathlib's
`composition_card`, given a named home here. A composition of `n` is an ordered
tuple of positive parts summing to `n`; the count follows from the bijection with
subsets of the `n − 1` internal gaps. -/
theorem card_composition_eq (n : ℕ) :
    Fintype.card (Composition n) = 2 ^ (n - 1) :=
  composition_card n

/-- The "set" model of compositions is equinumerous with `2 ^ (n − 1)` as well
(`compositionAsSet_card`). `CompositionAsSet n` records a composition by the subset
of internal boundaries it cuts, making the `2 ^ (n−1)` count manifest. -/
theorem card_compositionAsSet_eq (n : ℕ) :
    Fintype.card (CompositionAsSet n) = 2 ^ (n - 1) :=
  compositionAsSet_card n

/-! ## The bijective content -/

/-- The count is genuinely bijective: compositions of `n` correspond exactly to
their boundary sets. This packages Mathlib's `compositionEquiv` into a cardinality
equality, exposing the "subset of the `n−1` gaps" combinatorial model that explains
the `2 ^ (n−1)`. -/
theorem card_composition_eq_card_compositionAsSet (n : ℕ) :
    Fintype.card (Composition n) = Fintype.card (CompositionAsSet n) :=
  Fintype.card_congr (compositionEquiv n)

/-! ## Derived structural facts (absent from Mathlib) -/

/-- **Positivity**: every `n` has at least one composition (the trivial one). In
particular the count is never zero — including `n = 0`, whose only composition is
the empty tuple, giving `2 ^ (0−1) = 2 ^ 0 = 1`. -/
theorem card_composition_pos (n : ℕ) : 0 < Fintype.card (Composition n) := by
  rw [card_composition_eq]
  positivity

/-- **Doubling recurrence**: increasing `n` by one doubles the number of
compositions, stated cleanly for `n + 2` to avoid the truncated-subtraction edge
case at `n = 0`. Combinatorially: detaching the final unit box from a composition
of `n+2` either opens a new singleton part or lengthens the last part — the two choices
that account for the factor of `2`. This is the recurrence behind `2 ^ (n−1)`. -/
theorem card_composition_two_mul (n : ℕ) :
    Fintype.card (Composition (n + 2)) = 2 * Fintype.card (Composition (n + 1)) := by
  rw [card_composition_eq, card_composition_eq]
  show 2 ^ (n + 1) = 2 * 2 ^ n
  ring

/-- The hypothesis form of the doubling recurrence: for `n ≥ 1`, passing from `n`
to `n + 1` doubles the count. (Equivalent to `card_composition_two_mul` after
writing `n = m + 1`.) -/
theorem card_composition_succ_of_pos {n : ℕ} (hn : 1 ≤ n) :
    Fintype.card (Composition (n + 1)) = 2 * Fintype.card (Composition n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- n = 1 + m; reduce the truncated subtractions and finish by `pow_add`
  rw [card_composition_eq, card_composition_eq, Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  ring

/-! ## Worked numeric instances -/

/-- `n = 1`: the single composition `[1]`. -/
example : Fintype.card (Composition 1) = 1 := by norm_num [card_composition_eq]

/-- `n = 2`: the `2` compositions `[2]`, `[1,1]`. -/
example : Fintype.card (Composition 2) = 2 := by norm_num [card_composition_eq]

/-- `n = 3`: the `4` compositions `[3]`, `[1,2]`, `[2,1]`, `[1,1,1]`. -/
example : Fintype.card (Composition 3) = 4 := by norm_num [card_composition_eq]

/-- `n = 4`: `8` compositions. -/
example : Fintype.card (Composition 4) = 8 := by norm_num [card_composition_eq]

/-- `n = 5`: `16` compositions. -/
example : Fintype.card (Composition 5) = 16 := by norm_num [card_composition_eq]

/-- Sanity check on the doubling recurrence at a concrete value:
`card (Composition 5) = 2 · card (Composition 4)`, i.e. `16 = 2 · 8`. -/
example : Fintype.card (Composition 5) = 2 * Fintype.card (Composition 4) :=
  card_composition_two_mul 3

end CompositionCard2PowOQ01
