import Mathlib

/-
# Partition Theorem — OQ-02: Modulus-Monotonicity of Divisibility-Restricted Partition Counts

## Research Problem: partition-theorem-oq-02

The parent (`partition-theorem`) is Euler's classical identity: the number of partitions of `n`
into **odd** parts equals the number into **distinct** parts.  Mathlib records both Euler
(`Nat.Partition.card_odds_eq_card_distincts`) and its general modulus-`m` form, *Glaisher's
theorem* (`Nat.Partition.card_restricted_eq_card_countRestricted`):

      #{partitions of n with no part divisible by m}  =  #{partitions of n with every part
                                                          used fewer than m times}.

Euler is the `m = 2` case (no even part = odd parts; used `< 2` times = distinct parts).

## What this file proves (original)

Write `A_m(n) := #{partitions of n with no part divisible by m}` (the divisibility-restricted
family) and `B_m(n) := #{partitions of n with each part used < m times}` (the
repetition-restricted family).  Glaisher says `A_m(n) = B_m(n)`.

**Main result — modulus monotonicity.**  For `0 < m ≤ m'`,

      A_m(n)  ≤  A_{m'}(n).

This is genuinely non-obvious.  The divisibility families are **not nested**: a partition that
avoids multiples of `m` may contain a multiple of `m'`, and one that avoids multiples of `m'`
may contain a multiple of `m`.  There is no set containment `A_m ⊆ A_{m'}` to read the
inequality off of — on the divisibility side the monotonicity is simply invisible.

The monotonicity becomes transparent only on the *other* side of Glaisher.  The
repetition-restricted families **are** manifestly nested: "each part used `< m` times" implies
"each part used `< m'` times" whenever `m ≤ m'`, so `B_m(n) ⊆ B_{m'}(n)` as finsets and hence
`B_m(n) ≤ B_{m'}(n)`.  Transporting this through Glaisher's equalities `A_m = B_m`,
`A_{m'} = B_{m'}` yields `A_m(n) ≤ A_{m'}(n)`.  **Glaisher's theorem is the essential bridge:**
the inequality holds between two families with no direct combinatorial comparison, and the only
route between them is the repetition reformulation.

## Consequences

* `card_not_dvd_three_eq_card_lt_three_repeats` — the named `m = 3` Glaisher case:
  partitions with no part divisible by `3` ≍ partitions with no part used three+ times.
* `card_odds_le_card_not_dvd_three` — instantiating the monotonicity at `2 ≤ 3`: the number of
  partitions of `n` into odd parts is at most the number with no part divisible by `3`.
* `card_distincts_le_card_not_dvd_three` — the same bound restated via Euler on the distinct
  side: `#(distinct-part partitions) ≤ #(no-part-divisible-by-3 partitions)`.

## What is proved

* `countRestricted_mono` — `m ≤ m'` ⟹ `countRestricted n m ⊆ countRestricted n m'`.
* `card_restricted_not_dvd_mono` — `0 < m ≤ m'` ⟹ `A_m(n) ≤ A_{m'}(n)`.
* the three corollaries above.

All statements are over Mathlib's `Nat.Partition` API and are fully machine-checked.

Tags: combinatorics, partitions, euler-partition-theorem, glaisher, monotonicity
-/

namespace PartitionTheoremOQ02

open Nat.Partition Finset

/-- **Monotonicity of the repetition-bounded family in the bound.**
    If `m ≤ m'` then every partition whose parts each repeat fewer than `m` times also
    repeats each part fewer than `m'` times, so the finsets are nested.  This is the only
    place where a containment is genuinely available; the divisibility families below are not
    nested and borrow their monotonicity from here through Glaisher's theorem. -/
theorem countRestricted_mono (n : ℕ) {m m' : ℕ} (h : m ≤ m') :
    countRestricted n m ⊆ countRestricted n m' := by
  intro x hx
  rw [countRestricted, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, fun i hi => lt_of_lt_of_le (hx.2 i hi) h⟩

/-- **Modulus-monotonicity of the divisibility-restricted partition count.**

    For `0 < m ≤ m'`, the number of partitions of `n` with no part divisible by `m` is at most
    the number with no part divisible by `m'`:

        #(restricted n (¬ m ∣ ·)) ≤ #(restricted n (¬ m' ∣ ·)).

    The two divisibility families are incomparable as sets, so this cannot be seen directly.
    Glaisher's theorem `card_restricted_eq_card_countRestricted` rewrites each side to the
    repetition family `countRestricted`, which *is* nested in the bound (`countRestricted_mono`),
    and the inequality follows by `card_le_card`. -/
theorem card_restricted_not_dvd_mono (n : ℕ) {m m' : ℕ} (hm : 0 < m) (hmm : m ≤ m') :
    #(restricted n (¬ m ∣ ·)) ≤ #(restricted n (¬ m' ∣ ·)) := by
  have hm' : 0 < m' := lt_of_lt_of_le hm hmm
  rw [card_restricted_eq_card_countRestricted n hm,
      card_restricted_eq_card_countRestricted n hm']
  exact Finset.card_le_card (countRestricted_mono n hmm)

/-- **Glaisher's `m = 3` case (a named classical generalization of Euler).**
    Partitions of `n` with no part divisible by `3` are equinumerous with partitions of `n`
    in which no part is used three or more times. -/
theorem card_not_dvd_three_eq_card_lt_three_repeats (n : ℕ) :
    #(restricted n (¬ 3 ∣ ·)) = #(countRestricted n 3) :=
  card_restricted_eq_card_countRestricted n (by norm_num)

/-- **Euler's count is dominated by the "no multiple of 3" count.**

    Partitions into odd parts are exactly partitions avoiding multiples of `2`, so the
    modulus-monotonicity at `2 ≤ 3` gives that the number of partitions of `n` into odd parts
    is at most the number avoiding multiples of `3`. -/
theorem card_odds_le_card_not_dvd_three (n : ℕ) :
    #(odds n) ≤ #(restricted n (¬ 3 ∣ ·)) := by
  have hodds : odds n = restricted n (¬ (2 : ℕ) ∣ ·) := by
    simp_rw [odds, even_iff_two_dvd]
  rw [hodds]
  exact card_restricted_not_dvd_mono n (by norm_num) (by norm_num)

/-- **Euler + monotonicity, packaged on the distinct-parts side.**

    Combining Euler's theorem `#(odds n) = #(distincts n)` with the previous bound: the number
    of partitions of `n` into *distinct* parts is at most the number of partitions of `n` with
    no part divisible by `3`. -/
theorem card_distincts_le_card_not_dvd_three (n : ℕ) :
    #(distincts n) ≤ #(restricted n (¬ 3 ∣ ·)) := by
  rw [← card_odds_eq_card_distincts]
  exact card_odds_le_card_not_dvd_three n

#check @countRestricted_mono
#check @card_restricted_not_dvd_mono
#check @card_not_dvd_three_eq_card_lt_three_repeats
#check @card_odds_le_card_not_dvd_three
#check @card_distincts_le_card_not_dvd_three

/-
## Summary

Proved (0 sorries, 0 axioms beyond Mathlib's foundational `propext` / `Classical.choice` /
`Quot.sound`; imports only Mathlib):

* `countRestricted_mono` — the repetition family is nested in its bound.
* `card_restricted_not_dvd_mono` — **modulus monotonicity**: for `0 < m ≤ m'`,
  `#(restricted n (¬ m ∣ ·)) ≤ #(restricted n (¬ m' ∣ ·))`.
* `card_not_dvd_three_eq_card_lt_three_repeats` — the named `m = 3` Glaisher identity.
* `card_odds_le_card_not_dvd_three`, `card_distincts_le_card_not_dvd_three` — Euler's
  odd/distinct count is bounded by the "no multiple of 3" count.

The point of the main theorem is structural: the divisibility-restricted families
`{no part divisible by m}` are pairwise incomparable, so the monotonicity of their *counts* in
`m` is invisible on the divisibility side.  It is recovered by transporting through Glaisher's
theorem to the repetition-restricted families `{each part used < m times}`, which are genuinely
nested.  Glaisher is the indispensable bridge between two otherwise-incomparable families.
-/

end PartitionTheoremOQ02

#print axioms PartitionTheoremOQ02.card_restricted_not_dvd_mono
#print axioms PartitionTheoremOQ02.card_distincts_le_card_not_dvd_three
