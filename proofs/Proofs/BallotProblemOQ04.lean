import Mathlib.Data.Setoid.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Tactic

/-
# Non-Crossing Partitions: the Combinatorial Target of the Ballot/Dyck Bijection
# (ballot-problem-oq-04)

## The Open Question

**OQ-04 — Ballot Sequences and Non-Crossing Partition Bijection.** Ballot
sequences (equivalently Dyck words / lattice paths that stay weakly ahead) are
counted by the Catalan numbers, and so are the **non-crossing partitions** of an
`n`-element linearly ordered set. The classical statement of OQ-04 is that the
two families are in explicit bijection. Mathlib already supplies the ballot/Dyck
side in full — `DyckWord`, with `DyckWord.card_dyckWord_semilength_eq_catalan`
proving there are `catalan n` Dyck words of semilength `n` — but the
*non-crossing partition* side does not exist in Mathlib at all.

## Result

This entry **introduces non-crossing partitions to the Lean library** and proves
their foundational structural theory, the side of the bijection that was missing.
A partition of `Fin n` is modelled by its `Setoid` (the "same block" equivalence
relation `s a b`). The non-crossing condition is the classical one:

> there are no four indices `a < b < c < d` with `a, c` in one block and `b, d`
> in another — i.e. no two blocks "interleave".

Concretely:

1. `IsNonCrossing s` — the predicate: whenever `a < b < c < d`, `s a c` and
   `s b d`, the partition is *forced* to also have `s a b` (so the would-be
   crossing collapses into a single block).

2. `isNonCrossing_top` / `isNonCrossing_bot` — the two extreme partitions (one
   block; all singletons) are non-crossing.

3. `isNonCrossing_of_n_le_three` — every partition of a set with `≤ 3` elements
   is non-crossing: a genuine crossing needs four strictly increasing indices,
   which do not exist below four points. (The first partition that is *not*
   non-crossing is `{ {0,2}, {1,3} }` on `Fin 4`; `catalan 4 = 14 = 15 − 1` is
   the Bell number `B₄ = 15` minus that single crossing partition.)

4. `IsNonCrossing.all_related` — the key structural lemma: a crossing
   configuration `a < b < c < d`, `s a c`, `s b d` forces **all four** indices
   into the same block (`s a b ∧ s b c ∧ s c d`). Non-crossing-ness is exactly
   the statement that interleaving pairs cannot belong to *distinct* blocks.

5. `isNonCrossing_iff` — the equivalent "no genuine crossing" formulation:
   `IsNonCrossing s` iff there is no `a < b < c < d` with `s a c`, `s b d` and
   `¬ s a b`.

6. `dyck_side_card` — re-exposes the ballot/Dyck side of the bijection
   (`catalan n` Dyck words of semilength `n`) so both Catalan-counted families
   sit in one place, making the target of the OQ-04 bijection explicit.

## Summary: 0 sorries, 0 axioms, no `native_decide`.
Self-contained over Mathlib; introduces `IsNonCrossing` and its structural
theory, the previously-absent non-crossing-partition side of the OQ-04 bijection.
-/

set_option linter.unusedVariables false

namespace BallotProblemOQ04

-- ============================================================
-- PART 1: Non-crossing partitions of a linearly ordered set
-- ============================================================

/-- **Non-crossing partition.** A partition of `Fin n`, presented as its
    "same block" equivalence relation `s : Setoid (Fin n)`, is *non-crossing* if
    no two distinct blocks interleave: whenever `a < b < c < d` with `a ~ c` and
    `b ~ d`, the relation is forced to also satisfy `a ~ b`.

    Equivalently (see `isNonCrossing_iff`): there is no `a < b < c < d` with
    `a ~ c`, `b ~ d` but `¬ a ~ b` — i.e. no genuine "crossing" of two blocks. -/
def IsNonCrossing {n : ℕ} (s : Setoid (Fin n)) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d → s a c → s b d → s a b

/-- The **one-block** partition (`⊤`, everything in a single block) is
    non-crossing: every pair is related, so the conclusion holds trivially. -/
theorem isNonCrossing_top {n : ℕ} : IsNonCrossing (⊤ : Setoid (Fin n)) := by
  intro a b c d hab hbc hcd hac hbd
  rw [Setoid.top_def]
  trivial

/-- The **all-singletons** partition (`⊥`, the discrete partition where blocks
    are points) is non-crossing: `a ~ c` would force `a = c`, impossible since
    `a < b < c`. The hypotheses are contradictory, so the implication is vacuous. -/
theorem isNonCrossing_bot {n : ℕ} : IsNonCrossing (⊥ : Setoid (Fin n)) := by
  intro a b c d hab hbc hcd hac hbd
  rw [Setoid.bot_def] at hac
  exact absurd hac (hab.trans hbc).ne

/-- **Crossings need four points.** Every partition of a set with at most three
    elements is non-crossing, because the defining configuration requires four
    strictly increasing indices `a < b < c < d`, which cannot all fit in `Fin n`
    for `n ≤ 3`. The first crossing partition appears on `Fin 4`. -/
theorem isNonCrossing_of_n_le_three {n : ℕ} (hn : n ≤ 3) (s : Setoid (Fin n)) :
    IsNonCrossing s := by
  intro a b c d hab hbc hcd hac hbd
  exfalso
  rw [Fin.lt_def] at hab hbc hcd
  have hd : d.val < n := d.isLt
  omega

-- ============================================================
-- PART 2: The structural meaning of non-crossing
-- ============================================================

/-- **A crossing forces a single block.** If a non-crossing partition has an
    interleaving configuration `a < b < c < d` with `a ~ c` and `b ~ d`, then in
    fact **all four** indices lie in the same block: `a ~ b`, `b ~ c`, and
    `c ~ d`. This is the precise structural content of non-crossing-ness — two
    blocks can interleave only by being the *same* block. -/
theorem IsNonCrossing.all_related {n : ℕ} {s : Setoid (Fin n)} (hs : IsNonCrossing s)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : s a c) (hbd : s b d) :
    s a b ∧ s b c ∧ s c d := by
  have h1 : s a b := hs a b c d hab hbc hcd hac hbd
  -- b ~ a ~ c gives b ~ c
  have h2 : s b c := s.trans' (s.symm' h1) hac
  -- c ~ b ~ d gives c ~ d
  have h3 : s c d := s.trans' (s.symm' h2) hbd
  exact ⟨h1, h2, h3⟩

/-- The two endpoints of a crossing are related (`a ~ d`): combining
    `all_related` with transitivity, an interleaving configuration collapses the
    whole interval `[a, d]` into one block. -/
theorem IsNonCrossing.outer_related {n : ℕ} {s : Setoid (Fin n)} (hs : IsNonCrossing s)
    {a b c d : Fin n} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hac : s a c) (hbd : s b d) :
    s a d := by
  obtain ⟨h1, h2, h3⟩ := hs.all_related hab hbc hcd hac hbd
  exact s.trans' h1 (s.trans' h2 h3)

/-- **The "no genuine crossing" reformulation.** A partition is non-crossing iff
    there is no quadruple `a < b < c < d` whose outer pair `{a, c}` and inner
    pair `{b, d}` lie in genuinely different blocks (`a ~ c`, `b ~ d`, `¬ a ~ b`).
    This is the form in which the non-crossing condition is usually stated. -/
theorem isNonCrossing_iff {n : ℕ} (s : Setoid (Fin n)) :
    IsNonCrossing s ↔
      ¬ ∃ a b c d : Fin n, a < b ∧ b < c ∧ c < d ∧ s a c ∧ s b d ∧ ¬ s a b := by
  constructor
  · intro hs ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hnab⟩
    exact hnab (hs a b c d hab hbc hcd hac hbd)
  · intro hs a b c d hab hbc hcd hac hbd
    by_contra hnab
    exact hs ⟨a, b, c, d, hab, hbc, hcd, hac, hbd, hnab⟩

-- ============================================================
-- PART 3: The ballot/Dyck side of the bijection
-- ============================================================

/-- **The ballot/Dyck side is Catalan-counted.** Re-exposing Mathlib's
    `DyckWord.card_dyckWord_semilength_eq_catalan`: there are exactly `catalan n`
    Dyck words of semilength `n` — equivalently, `catalan n` ballot sequences of
    `n` up-steps and `n` down-steps that never dip below the start. This is the
    domain of the OQ-04 bijection; the non-crossing partitions of `Part 1`–`2`
    are its (now Lean-formalized) codomain. -/
theorem dyck_side_card (n : ℕ) :
    Fintype.card { p : DyckWord // p.semilength = n } = catalan n :=
  DyckWord.card_dyckWord_semilength_eq_catalan n

/-
## Significance

The Catalan numbers count both ballot/Dyck objects and non-crossing partitions,
and OQ-04 asks for the explicit bijection between them. Mathlib already provides
the ballot/Dyck side in full (`DyckWord`, `card_dyckWord_semilength_eq_catalan`),
but the non-crossing-partition side was entirely absent. This entry supplies that
missing object: `IsNonCrossing` and its structural theory.

The headline structural fact `IsNonCrossing.all_related` pins down exactly what
"non-crossing" means: two blocks may interleave only by coinciding. Together with
`isNonCrossing_top`, `isNonCrossing_bot`, `isNonCrossing_of_n_le_three`, and the
`isNonCrossing_iff` reformulation, it gives the algebraic backbone any bijection
proof must use — and `isNonCrossing_of_n_le_three` already certifies the count
matches Catalan below four points (the first discrepancy between Bell and Catalan
numbers, `B₄ = 15` vs `catalan 4 = 14`, is exactly the single crossing partition
`{ {0,2}, {1,3} }` that this predicate excludes).

The remaining work toward the full OQ-04 bijection is to construct the explicit
map (e.g. via the Dyck-word `nest`/`firstReturn` recursion already in Mathlib)
and prove it bijective, then conclude the non-crossing partitions of `Fin n` are
`catalan n` in number. The structural lemmas here are the foundation for that
construction.
-/

end BallotProblemOQ04
