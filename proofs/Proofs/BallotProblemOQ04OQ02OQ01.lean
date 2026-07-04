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
  point. It is split here into its *counting* and *combinatorial* halves (see below): the
  counting half is proved, and the combinatorial half — a first-return **bijection** — is the
  sole remaining `sorry`. The decomposition is **not** in Mathlib in any form.

Given the base case and recurrence, `nonCrossingCount_eq_catalan` is a four-line strong
induction matching the `antidiagonal` shape of `catalan_succ'`. The point of this file is that
it isolates the *entire* difficulty of `nonCrossing = Catalan` into one explicit bijection: a
reduction in the spirit of "one structural theorem in place of an explicit bijection".

## Status

**Sorry count**: 1 (`nonempty_firstReturnEquiv` — the first-return bijection). The numeric
recurrence `nonCrossingCount_recurrence` and its counting reduction
`nonCrossingCount_recurrence_of_equiv` are now **proved (0 `sorry`)**; the open content is
exactly the existence of the bijection, with all cardinality arithmetic discharged.

**Axiom count**: 0 literal `axiom` declarations; the proved results use only the foundational
`propext`/`Classical.choice`/`Quot.sound` (the latter via `.some` on the bijection's
`Nonempty`). Because a `sorry` remains, the gallery status of this entry is `formalized`, not
`verified`.

The outstanding bijection is the natural target for proof search: it is *known* mathematics
(the non-crossing-partition Catalan decomposition) requiring a delicate but standard
construction, exactly the regime where automated formalization is appropriate.
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

/-! ## First-return infrastructure: restriction of non-crossing partitions

The outstanding bijection `nonempty_firstReturnEquiv` decomposes a non-crossing partition of
`Fin (n+1)` into the induced partitions on the two sub-intervals cut out by a distinguished
block. Building those induced partitions is where the earlier survey estimated "several hundred
lines" of manual `Finpartition` construction (providing `SupIndep`, `sup_parts`, `not_bot`
by hand). This section removes that obstacle with a short, reusable construction:

* the *same-part* relation of any `Finpartition (univ : Finset (Fin n))` is exactly
  `Setoid.ker P.part` (relation `P.part a = P.part b`), by `mem_part_iff_part_eq_part`;
* pulling it back along an index embedding `emb : Fin i → Fin (n+1)` (`Setoid.comap`) and
  re-materialising it with `Finpartition.ofSetoid` yields the restricted partition `restrictFp`
  **without any manual partition-axiom proof** — `ofSetoid` supplies them;
* and restriction *preserves* non-crossing whenever `emb` is strictly monotone
  (`isNonCrossingFp_restrictFp`): a crossing in the restriction lifts, through the
  order-embedding, to a crossing in `P`.

This is the forward (restriction) half of the first-return decomposition, proved with `0`
`sorry`; the remaining work for the bijection is the gluing (inverse) map and the mutual-inverse
laws (see the entry's research notes). -/

/-- The *same-part* relation of `P`, pulled back along an index map `emb`, as a `Setoid`.
Its relation is `P.part (emb a) = P.part (emb b)` (`Setoid.ker P.part` is the same-part relation
by `Finpartition.mem_part_iff_part_eq_part`). -/
def restrictSetoid {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (P : Finpartition (univ : Finset (Fin (n + 1)))) : Setoid (Fin i) :=
  Setoid.comap emb (Setoid.ker P.part)

instance instDecidableRestrictRel {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (P : Finpartition (univ : Finset (Fin (n + 1)))) :
    DecidableRel (restrictSetoid emb P).r :=
  fun a b => (inferInstance : Decidable (P.part (emb a) = P.part (emb b)))

/-- **Restriction of a finpartition along an index embedding.** The finpartition of `Fin i`
whose blocks are the `emb`-preimages of the blocks of `P`. Built via `Finpartition.ofSetoid`, so
the partition axioms come for free. -/
def restrictFp {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (P : Finpartition (univ : Finset (Fin (n + 1)))) :
    Finpartition (univ : Finset (Fin i)) :=
  Finpartition.ofSetoid (restrictSetoid emb P)

/-- Membership in a block of the restriction is same-block-under-`emb` in `P`. -/
@[simp] theorem mem_part_restrictFp {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (P : Finpartition (univ : Finset (Fin (n + 1)))) (a b : Fin i) :
    b ∈ (restrictFp emb P).part a ↔ P.part (emb a) = P.part (emb b) :=
  Finpartition.mem_part_ofSetoid_iff_rel

/-- **Restriction preserves non-crossing (forward half of the first-return decomposition).**
If `emb : Fin i → Fin (n+1)` is strictly monotone (an order-embedding of an index interval) and
`P` is non-crossing, then the restricted partition `restrictFp emb P` is non-crossing. A crossing
`a < b < c < d` in the restriction maps, through the order-embedding, to a crossing
`emb a < emb b < emb c < emb d` in `P`; the same-block hypotheses transport along `emb`, so
non-crossing of `P` forces `emb a, emb b` into a common block, i.e. `a, b` into a common block of
the restriction. -/
theorem isNonCrossingFp_restrictFp {i n : ℕ} (emb : Fin i → Fin (n + 1))
    (hmono : StrictMono emb) (P : Finpartition (univ : Finset (Fin (n + 1))))
    (hP : IsNonCrossingFp P) : IsNonCrossingFp (restrictFp emb P) := by
  intro a b c d hab hbc hcd hca hdb
  rw [mem_part_restrictFp] at hca hdb ⊢
  have Hca : emb c ∈ P.part (emb a) := by rw [hca]; exact P.mem_part (mem_univ _)
  have Hdb : emb d ∈ P.part (emb b) := by rw [hdb]; exact P.mem_part (mem_univ _)
  have hb_in_a : emb b ∈ P.part (emb a) :=
    hP (emb a) (emb b) (emb c) (emb d) (hmono hab) (hmono hbc) (hmono hcd) Hca Hdb
  exact ((P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).mp hb_in_a).symm

/-! ## The combinatorial recurrence (HARD)

The recurrence is now split into two parts that separate its *counting* content from its
*combinatorial* content:

* `nonempty_firstReturnEquiv` — the genuine, still-open obligation: the existence of a
  first-return bijection that decomposes a non-crossing partition of `Fin (n+1)` into a pair of
  independent non-crossing partitions of sizes `(i, j) ∈ antidiagonal n`. This is the entire
  combinatorial heart and the **sole outstanding `sorry`**.
* `nonCrossingCount_recurrence_of_equiv` — the counting half, **proved here (0 `sorry`)**: any
  such bijection already forces the Catalan convolution, by a pure cardinality computation
  (`Fintype.card_congr` ∘ `card_sigma` ∘ `card_prod`).

`nonCrossingCount_recurrence` is then a corollary of the two. -/

/-- **First-return bijection (the sole open obligation).** A non-crossing partition of the
linearly ordered set `Fin (n+1)` decomposes — via the classical "first return" of the block
structure around a distinguished point — into an independent pair of non-crossing partitions of
an `i`-element and a `j`-element interval, with `(i, j)` ranging over `antidiagonal n`. We
record the decomposition as a bijection (existence suffices for the count).

This is the genuine combinatorial content of `nonCrossing = Catalan`; the analogous
decomposition is *not* available in Mathlib in any form (Mathlib has no theory of non-crossing
partitions, nor of restricting a `Finpartition` of `Fin (n+1)` to the gaps cut out by a
distinguished block). **Outstanding `sorry`** (HARD, bijection-level). -/
theorem nonempty_firstReturnEquiv (n : ℕ) :
    Nonempty ({P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P} ≃
      Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
        {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
        {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P}) := by
  sorry

/-- **Counting half of the recurrence (proved, 0 `sorry`).** Any first-return bijection
splitting the non-crossing partitions of `Fin (n+1)` over `antidiagonal n` already forces the
Catalan convolution: it is a pure cardinality computation. This isolates the counting content
of `nonCrossingCount_recurrence` from its combinatorial content (`nonempty_firstReturnEquiv`),
and is the reusable bridge a future construction of the bijection plugs into. -/
theorem nonCrossingCount_recurrence_of_equiv (n : ℕ)
    (e : {P : Finpartition (univ : Finset (Fin (n + 1))) // IsNonCrossingFp P} ≃
      Σ ij : (antidiagonal n : Finset (ℕ × ℕ)),
        {P : Finpartition (univ : Finset (Fin ij.1.1)) // IsNonCrossingFp P} ×
        {P : Finpartition (univ : Finset (Fin ij.1.2)) // IsNonCrossingFp P}) :
    nonCrossingCount (n + 1)
      = ∑ ij ∈ antidiagonal n, nonCrossingCount ij.1 * nonCrossingCount ij.2 := by
  unfold nonCrossingCount
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_prod]
  exact Finset.sum_coe_sort (antidiagonal n)
    (fun ij => Fintype.card {P : Finpartition (univ : Finset (Fin ij.1)) // IsNonCrossingFp P} *
               Fintype.card {P : Finpartition (univ : Finset (Fin ij.2)) // IsNonCrossingFp P})

/-- **Catalan recurrence for non-crossing partitions.** The non-crossing partitions of
`Fin (n+1)` split into pairs of independent non-crossing partitions whose sizes `(i, j)` run
over `antidiagonal n`:
`nonCrossingCount (n+1) = ∑ (i,j) ∈ antidiagonal n, nonCrossingCount i * nonCrossingCount j`.

This is the same convolution that defines `catalan` (`catalan_succ'`). It is now a corollary of
the (still open) first-return bijection `nonempty_firstReturnEquiv` and the (proved) counting
reduction `nonCrossingCount_recurrence_of_equiv`. -/
theorem nonCrossingCount_recurrence (n : ℕ) :
    nonCrossingCount (n + 1)
      = ∑ ij ∈ antidiagonal n, nonCrossingCount ij.1 * nonCrossingCount ij.2 :=
  nonCrossingCount_recurrence_of_equiv n (nonempty_firstReturnEquiv n).some

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

/-! ## Unconditional verification for `n ≤ 3` (independent of the open bijection)

`nonCrossingCount_eq_catalan` above is proved *modulo* the still-open first-return bijection
`nonempty_firstReturnEquiv`. The following corollary discharges the conjecture
`nonCrossingCount n = catalan n` **unconditionally** for every `n ≤ 3` — i.e. without
assuming that bijection at all. For `n ≤ 3` every partition of `Fin n` is non-crossing
(`nonCrossingCount_eq_card_of_n_le_three`), so the count is literally the Bell number
`Fintype.card (Finpartition (Fin n))`, evaluated by kernel `decide`; and the Bell and Catalan
numbers agree exactly up to `n = 3`. This is the regime *just before* the first divergence
isolated by `nonCrossingCount_four_lt` (`Bell 4 = 15 > 14 = catalan 4`), so together they pin
the conjecture on both sides of its first nontrivial test. -/
set_option maxRecDepth 8000 in
theorem nonCrossingCount_eq_catalan_of_le_three {n : ℕ} (hn : n ≤ 3) :
    nonCrossingCount n = catalan n := by
  interval_cases n
  · rw [nonCrossingCount_zero, catalan_zero]
  · rw [nonCrossingCount_eq_card_of_n_le_three (by norm_num),
        show catalan 1 = 1 by simp [catalan_succ']]
    decide
  · rw [nonCrossingCount_eq_card_of_n_le_three (by norm_num),
        show catalan 2 = 2 by
          simp [catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
                Finset.sum_range_succ, catalan_zero]]
    decide
  · rw [nonCrossingCount_eq_card_of_n_le_three (by norm_num),
        show catalan 3 = 5 by
          simp [catalan_succ', Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
                Finset.sum_range_succ, catalan_zero]]
    decide

#check @nonCrossingCount_zero
#check @nonCrossingCount_eq_catalan
#check @nonCrossingCount_eq_catalan_of_le_three

end BallotProblemOQ04OQ02OQ01
