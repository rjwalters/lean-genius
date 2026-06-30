/-
# Non-Crossing Partitions are Counted by the Catalan Numbers
## (ballot-problem-oq-04-oq-02-oq-01)

**Open question** (from `ballot-problem-oq-04-oq-02`, the countable Finpartition model):
the sibling entry `ballot-problem-oq-04-oq-02` introduced `nonCrossingCount n`, the number
of non-crossing partitions of `Fin n`, as a well-typed `Fintype.card`, and pinned down its
first divergence from the Bell numbers at `n = 4`. The *exact value* was left open:

> `nonCrossingCount n = catalan n`.

This file supplies the **structural reduction** of that counting statement to a single
combinatorial recurrence, and discharges everything except that recurrence.

## The reduction

Mathlib's Catalan numbers satisfy the convolution recurrence
(`Mathlib.Combinatorics.Enumerative.Catalan`):
* `catalan 0 = 1`;
* `catalan (n+1) = ∑ (i,j) ∈ antidiagonal n, catalan i * catalan j`  (`catalan_succ'`).

So `nonCrossingCount = catalan` follows by strong induction the moment we know
`nonCrossingCount` obeys the *same* two laws:

* **Base** (`nonCrossingCount_zero`): there is a unique partition of the empty set, and it
  is (vacuously) non-crossing, so `nonCrossingCount 0 = 1`. **Proved here, 0 sorry.**

* **Recurrence** (`nonCrossingCount_recurrence`):
  `nonCrossingCount (n+1) = ∑ (i,j) ∈ antidiagonal n, nonCrossingCount i * nonCrossingCount j`.
  This is the genuine combinatorial content — the classical Catalan decomposition of a
  non-crossing partition of `{0,…,n}` according to the block structure around a distinguished
  point — and is **not** in Mathlib in any form. It remains a `sorry` here (HARD,
  bijection-level formalization; see `## Status` below).

Given those two, `nonCrossingCount_eq_catalan` is a four-line strong induction matching the
`antidiagonal` shape of `catalan_succ'`. The point of this file is that it isolates the
*entire* difficulty of `nonCrossing = Catalan` into the one recurrence lemma: a reduction in
the spirit of "one structural theorem in place of an explicit bijection".

## Status

**Sorry count**: 1 (`nonCrossingCount_recurrence`). **Axiom count**: 0 literal `axiom`
declarations; the reduction and base case use only the foundational
`propext`/`Classical.choice`/`Quot.sound`. Because a `sorry` remains, the gallery status of
this entry is `formalized`, not `verified`.

The outstanding recurrence is the natural target for proof search: it is *known* mathematics
(the non-crossing-partition Catalan recurrence) requiring a delicate but standard
decomposition, exactly the regime where automated formalization is appropriate.
-/

import Mathlib
import Proofs.BallotProblemOQ04
import Proofs.BallotProblemOQ04OQ02

open Finset
open scoped BigOperators

namespace BallotProblemOQ04OQ02OQ01

open BallotProblemOQ04OQ02 (IsNonCrossingFp nonCrossingCount nonCrossingCount_eq_card_of_n_le_three)

/-! ## The base case `n = 0` -/

/-- **Base case.** There is exactly one partition of the empty set `Fin 0`, and (with no four
indices to cross) it is non-crossing, so `nonCrossingCount 0 = 1 = catalan 0`. -/
theorem nonCrossingCount_zero : nonCrossingCount 0 = 1 := by
  rw [nonCrossingCount_eq_card_of_n_le_three (n := 0) (by norm_num)]
  have hbot : (univ : Finset (Fin 0)) = ⊥ := by
    rw [Finset.univ_eq_empty, Finset.bot_eq_empty]
  simp only [hbot]
  exact Fintype.card_unique

/-! ## The combinatorial recurrence (HARD — outstanding `sorry`) -/

/-- **Catalan recurrence for non-crossing partitions.** The non-crossing partitions of
`Fin (n+1)` split — according to the classical "first return" / block decomposition of a
non-crossing partition of a linearly ordered set — into pairs of independent non-crossing
partitions whose sizes `(i, j)` run over `antidiagonal n`. Equivalently:
`nonCrossingCount (n+1) = ∑ (i,j) ∈ antidiagonal n, nonCrossingCount i * nonCrossingCount j`.

This is the same convolution that defines `catalan` (`catalan_succ'`); proving it for
`nonCrossingCount` is the entire combinatorial content of `nonCrossing = Catalan`, and is not
available in Mathlib. **Outstanding `sorry`** (HARD, bijection-level). -/
theorem nonCrossingCount_recurrence (n : ℕ) :
    nonCrossingCount (n + 1)
      = ∑ ij ∈ antidiagonal n, nonCrossingCount ij.1 * nonCrossingCount ij.2 := by
  sorry

/-! ## The counting theorem -/

/-- **Non-crossing partitions are counted by the Catalan numbers.**
`nonCrossingCount n = catalan n` for every `n`. Strong induction: the base case is
`nonCrossingCount_zero`, and the step matches `nonCrossingCount_recurrence` against
`catalan_succ'` term-by-term over `antidiagonal n`, rewriting each factor by the inductive
hypothesis (both indices in an `antidiagonal n` pair are `< n+1`). -/
theorem nonCrossingCount_eq_catalan (n : ℕ) : nonCrossingCount n = catalan n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using nonCrossingCount_zero
    | m + 1 =>
      rw [nonCrossingCount_recurrence, catalan_succ']
      refine Finset.sum_congr rfl ?_
      intro ij hij
      rw [Finset.mem_antidiagonal] at hij
      have h1 : ij.1 < m + 1 := by omega
      have h2 : ij.2 < m + 1 := by omega
      rw [ih ij.1 h1, ih ij.2 h2]

#check @nonCrossingCount_zero
#check @nonCrossingCount_eq_catalan

end BallotProblemOQ04OQ02OQ01
