# S41 — `rotateSortedListPrefixSym_val_eq_sub_drop`

**Date**: 2026-05-12
**Researcher**: researcher-12
**Branch**: `research/ballot-oq03-oq01-oq01-oq01-s41-prefix-eq-sub-drop-*`
**Base**: `origin/main` (after S37/S38 merged, with S39 #17884 and S40
#17892 still in-flight at the same insertion window).

## Goal

Symmetric counterpart of S38's `rotateSortedListSuffixSym_val_eq_sub_take`
on the **prefix** side. Lifts S34's underlying-list identity `take +
drop = M.1` to a complement-form description of the prefix `Sym` against
the drop-suffix multiset.

## Deliverable

```lean
private lemma rotateSortedListPrefixSym_val_eq_sub_drop {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    (rotateSortedListPrefixSym M k j hj).1
      = M.1 - ((rotateSortedList M k).drop j : Multiset (Fin n)) := by
  have h := rotateSortedList_take_add_drop M k j
  show ((rotateSortedList M k).take j : Multiset (Fin n)) = _
  rw [← h, add_tsub_cancel_right]
```

Inserted at line 1302 in `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`
(immediately after the S38 `rotateSortedListSuffixSym_val_eq_sub_take`
block, before `totalSym` at the new line 1338).

## Why this is the right increment

The S40 next-action menu (relative to S40) listed four items, all of
which are structurally larger and commit to a particular bijection
shape: `firstDescentRotation` (~20 lines), 2B.4' bijection (~30–40
lines), Mathlib cycle lemma (~200 lines), or k=3 punt (~300 lines).

This S41 lands a fifth, cheaper option implicit in the symmetry between
S38 and S40: the prefix-side complement-form analog of S38. Together
with S38 it closes the **complement form** half of the prefix / suffix
toolkit. After S41 lands, every piece of the prefix / suffix
decomposition has matching descriptions in all three algebraic forms
(inequality, subtraction, addition); the cycle-lemma inverse direction
can recover either half from the other via complementation against
`M.1`.

## Proof verification (build pending — parent OQ03OQ02 break)

Docker build is currently blocked by `BallotProblemOQ03OQ02.lean`'s
parent break (~24 errors lines 1911–2386 on `origin/main` since
2026-05-09, per `feedback_researcher_ballot_oq03oq02_parent_break.md`).
Title precedent: S25–S40 PRs all merged with `(build pending — parent
OQ03OQ02 break)` modifier.

Build risk for this S41 PR is **extremely low**. The proof is
character-for-character symmetric to S38, with one lemma name change:

| Token                 | S38 (suffix)                            | S41 (prefix)                            |
|-----------------------|-----------------------------------------|-----------------------------------------|
| Target side           | `((rotateSortedList M k).drop j)`       | `((rotateSortedList M k).take j)`       |
| Subtraction direction | `M.1 - ((take j))`                      | `M.1 - ((drop j))`                      |
| `add_tsub_cancel_*`   | `_left` (`a + b - a = b`)               | `_right` (`a + b - b = a`)              |

Both `add_tsub_cancel_left` and `add_tsub_cancel_right` are standard
Mathlib lemmas in `Mathlib.Algebra.Order.Sub.Basic` (transitive imports
already in scope). The downstream lemma `rotateSortedList_take_add_drop`
(S34, file line 1098) is on `origin/main` since PR #17695 merged
2026-05-11.

## Coexistence with in-flight PRs #17892 (S40) and #17884 (S39)

Both PRs insert at the same anchor window (post-S38, pre-`totalSym`).
Three S41 declaration positions are possible depending on merge order:

- **S39 first → S41 → S40**: S41 inserts immediately after S39's three
  `@[simp]` lemmas, before S40's `_val_add_SuffixSym_val`.
- **S40 first → S41 → S39**: S41 inserts immediately after S40's
  `_val_add_SuffixSym_val`, before S39's `@[simp]` lemmas.
- **All three open**: order at merge time decides.

All three orderings are file-level non-overlapping (disjoint declaration
names). The only collision is in `meta.json` (shared `lineCount` /
`theoremCount` fields) and `state.md` (Current State header + Iteration
line), which are mechanical last-writer-wins text resolutions.

## File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 2312 → 2348
  (+36: section sub-header + 1 lemma with docstring).
- `meta.json`: `lineCount` 2312 → 2348; `theoremCount` 47 → 48;
  `definitionCount` 12 (unchanged); both `meta.*` and `leanFile.*`
  fields updated.
- `state.md`: +S41 Summary block (~115 lines); Current State header
  bumped.
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).

## Toolkit status after S41

| Form        | Prefix                                  | Suffix                                  |
|-------------|-----------------------------------------|-----------------------------------------|
| Inequality  | `_le` (S37, merged #17777)              | `_le` (S35, merged #17721)              |
| Subtraction | `_val_eq_sub_drop` (S41, this PR)       | `_val_eq_sub_take` (S38, merged #17779) |
| Addition    | `_val_add_SuffixSym_val` (S40, #17892)  | (same lemma)                            |
| Degenerate  | `_zero_val` / `_self_val` (S39, #17884) | `_zero_val` / `_self_val` (S36, merged) |
| Period      | `_mod` (S39, #17884)                    | `_mod` (S38, merged)                    |

After S39/S40/S41 land, the prefix/suffix structural API is **closed
under symmetry**: every form of one side has a matching companion on
the other. The next iteration (S42+) is free to commit to the
bijection's exact shape.
