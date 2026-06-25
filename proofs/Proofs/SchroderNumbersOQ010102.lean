import Mathlib

/-
# Dyck ⊆ Schröder: the Catalan numbers are dominated by the large Schröder numbers

The **Catalan number** `catalan n` counts Dyck paths (lattice paths with unit
up/down steps staying weakly above the axis), while the **large Schröder number**
`largeSchroder n` counts Schröder paths, which additionally allow horizontal
`(2,0)` steps. Every Dyck path *is* a Schröder path, so combinatorially
`catalan n ≤ largeSchroder n`. This file proves that inequality **purely from the
two convolution recurrences**, as requested by the open question of the entry
*Large Schröder numbers: the sharp tripling step* (`schroder-numbers-oq-01-oq-01`):

> Can the dominance `L(n) ≥ catalan(n)` over the Catalan numbers be proved by
> comparing their recurrences, formalizing the lattice-path inclusion of Dyck
> paths into Schröder paths?

Both sequences are governed by the *same* Cauchy-product shape over `Fin (n+1)`:

* `catalan (n+1)      = ∑ i, catalan i · catalan (n−i)`               (`catalan_succ`)
* `largeSchroder (n+1) = largeSchroder n + ∑ i, L i · L (n−i)`        (defining equation)

The large Schröder recurrence is the Catalan recurrence **plus** the extra
non-negative term `largeSchroder n`. A single strong induction therefore yields
the termwise domination, and the extra term makes the inequality *strict* for
every `n ≥ 1`. Equality holds exactly at `n = 0`.

Results:

* `largeSchroder_pos`            — `0 < largeSchroder n`;
* `catalan_le_largeSchroder`     — **`catalan n ≤ largeSchroder n`** (the open question, verbatim);
* `catalan_lt_largeSchroder`     — strict domination `catalan n < largeSchroder n` for `n ≥ 1`;
* `catalan_eq_largeSchroder_iff` — equality holds **iff** `n = 0`.

No axioms, no `sorry`, no `native_decide`. Mathlib records both `Nat.catalan` and
`Nat.largeSchroder` with their recurrences, but not the comparison between them.
-/

namespace SchroderNumbersOQ010102

open Finset
open Nat (largeSchroder)

/-- The large Schröder numbers are strictly positive. Immediate from the
recurrence `largeSchroder (n+1) = largeSchroder n + (non-negative sum)` and
`largeSchroder 0 = 1`. -/
theorem largeSchroder_pos : ∀ n, 0 < largeSchroder n
  | 0 => by simp
  | n + 1 => by
      rw [Nat.largeSchroder]
      exact Nat.lt_of_lt_of_le (largeSchroder_pos n) (Nat.le_add_right _ _)

/-- **Dyck ⊆ Schröder.** The Catalan numbers are dominated by the large Schröder
numbers, proved by strong induction comparing the two Cauchy-product recurrences.
The Schröder recurrence is the Catalan recurrence plus the extra term
`largeSchroder n ≥ 0`, so each convolution term dominates by the inductive
hypothesis. This is the open question of `schroder-numbers-oq-01-oq-01`, verbatim. -/
theorem catalan_le_largeSchroder : ∀ n, catalan n ≤ largeSchroder n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | m + 1 =>
      rw [catalan_succ, Nat.largeSchroder]
      -- goal: ∑ i : Fin m.succ, catalan i * catalan (m - i)
      --        ≤ largeSchroder m + ∑ i : Fin m.succ, L i * L (m - i)
      refine le_trans ?_ (Nat.le_add_left _ _)
      apply Finset.sum_le_sum
      intro i _
      have h1 : catalan (i : ℕ) ≤ largeSchroder i := ih i i.isLt
      have h2 : catalan (m - i) ≤ largeSchroder (m - i) :=
        ih (m - i) (by have := i.isLt; omega)
      exact Nat.mul_le_mul h1 h2

/-- Strict domination for every positive index: the extra `largeSchroder (n−1) ≥ 1`
term in the Schröder recurrence is absent from the Catalan recurrence. -/
theorem catalan_lt_largeSchroder : ∀ {n}, 1 ≤ n → catalan n < largeSchroder n := by
  intro n hn
  match n, hn with
  | m + 1, _ =>
    rw [catalan_succ, Nat.largeSchroder]
    -- ∑ i, catalan i * catalan (m-i) < largeSchroder m + ∑ i, L i * L (m-i)
    have hsum : ∑ i : Fin m.succ, catalan (i : ℕ) * catalan (m - i)
              ≤ ∑ i : Fin m.succ, largeSchroder (i : ℕ) * largeSchroder (m - i) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.mul_le_mul (catalan_le_largeSchroder i) (catalan_le_largeSchroder (m - i))
    have hpos : 0 < largeSchroder m := largeSchroder_pos m
    omega

/-- Equality between the Catalan and large Schröder numbers holds **exactly** at
`n = 0` (where both equal `1`); for all `n ≥ 1` the Schröder count strictly exceeds. -/
theorem catalan_eq_largeSchroder_iff {n : ℕ} : catalan n = largeSchroder n ↔ n = 0 := by
  constructor
  · intro h
    by_contra hne
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hne
    exact absurd h (Nat.ne_of_lt (catalan_lt_largeSchroder hn))
  · rintro rfl; simp

/-- Sanity check at `n = 3`: `catalan 3 = 5 ≤ 22 = largeSchroder 3`. -/
example : catalan 3 ≤ largeSchroder 3 := catalan_le_largeSchroder 3

end SchroderNumbersOQ010102
