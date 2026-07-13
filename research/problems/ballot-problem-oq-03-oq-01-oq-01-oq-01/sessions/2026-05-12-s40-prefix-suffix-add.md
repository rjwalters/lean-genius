# S40 — Sym-level `prefix + suffix = M.1` reconstitution lemma

**Date**: 2026-05-12
**Researcher**: researcher-12
**Branch**: `research/ballot-oq03-oq01-oq01-oq01-s40-prefix-suffix-add-*`
**Base**: `origin/main` at S38 (PR #17779, #17777 already merged)

## Goal

Land the smallest concrete item from S39's `### Next action (S40+)` menu:
the **Sym-level `_take_add_drop` analog (~5 lines)** trivial corollary
lifting S34's `rotateSortedList_take_add_drop` to the prefix/suffix
`Sym`-pair via `Subtype.1` definitional reduction.

## Deliverable

```lean
private lemma rotateSortedListPrefixSym_val_add_SuffixSym_val {n c : ℕ}
    (M : Sym (Fin n) c) (k j : ℕ) (hj : j ≤ c) :
    (rotateSortedListPrefixSym M k j hj).1
      + (rotateSortedListSuffixSym M k j).1 = M.1 := by
  show ((rotateSortedList M k).take j : Multiset (Fin n))
       + ((rotateSortedList M k).drop j : Multiset (Fin n)) = M.1
  exact rotateSortedList_take_add_drop M k j
```

Inserted at line 1300+ in `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`,
right after `rotateSortedListSuffixSym_val_eq_sub_take` (S38) and before
`totalSym` (S19).

## Why this is the right increment

S39's menu (in roughly increasing cost):

1. **Sym-level `_take_add_drop` analog (~5 lines)** ← THIS S40
2. `firstDescentRotation` def (~20 lines)
3. 2B.4' refined-codomain bijection (~30–40 lines)
4. Mathlib-side cycle lemma (~200 lines)
5. Punt to k=3 SSYT (~300 lines)

Item 1 lands a "complete the toolkit" milestone with negligible build risk:
together with S38's `_val_eq_sub_take` (`suffix = M.1 − prefix`) and
S35's `_le` (`suffix ≤ M.1`), the prefix/suffix decomposition now has
all three equivalent algebraic descriptions at the `Sym` level:

- subtraction form: `suffix = M.1 − prefix` (S38)
- inequality form: `suffix ≤ M.1`, `prefix ≤ M.1` (S35 / S37)
- addition form: `prefix + suffix = M.1` (S40, this iteration)

The 2B.4' refined-codomain bijection (item 3) requires the addition
form to verify that its forward map lands in the canonical
`totalSym`-fibre `{(P', Q') : P'.1 + Q'.1 = M.1}` — so item 1 is a
prerequisite, not a parallel branch.

## Proof verification (build pending — parent OQ03OQ02 break)

The Docker build is currently blocked by `BallotProblemOQ03OQ02.lean`'s
parent break (~24 errors lines 1911–2386 on `origin/main` since
2026-05-09, per `feedback_researcher_ballot_oq03oq02_parent_break.md`).
Title precedent: S25–S39 all merged with `(build pending — parent
OQ03OQ02 break)` modifier.

Build risk for this S40 PR is very low. The proof uses:

- `show` — Lean kernel `δ`-reduction of `Subtype.1` on anonymous
  constructor. Pattern exercised in dozens of other proofs in this
  file, including S38's `_val_eq_sub_take` (line 1297, `show
  ((rotateSortedList M k).drop j : Multiset (Fin n)) = _`).
- `exact rotateSortedList_take_add_drop M k j` — direct call to S34's
  lemma at line 1098, merged in PR #17695 (2026-05-11) and on
  `origin/main` since.

No new Mathlib imports, no new sorries, no new axioms.

## Coexistence with in-flight PR #17884 (S39)

PR #17884 (open, S39) inserts at the same anchor window: just after S38's
`_val_eq_sub_take` (line 1300) and before `totalSym` (line 1302). It
adds three prefix-`Sym` boundary / period lemmas at that point. This S40
PR inserts a single prefix+suffix reconstitution lemma at the same
window.

Both PRs are independent in the strict sense (no shared declaration
names, no shared file lines), so they will merge in either order with a
trivial rebase. The only collision is the `state.md` Current State
header block (2-3 lines: `Last Updated`, `Iteration`) — a 4-line text
resolution.

## File deltas

- `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`: 2312 → 2368
  lines (+56: section sub-header + 1 lemma with docstring).
- `meta.json`: `lineCount` 2312 → 2368; `theoremCount` 47 → 48;
  `definitionCount` 12 (unchanged); both `meta.*` and `leanFile.*`
  fields updated.
- `state.md`: + S40 Summary block; Current State header bumped.
- Sorry count: 2 (unchanged).
- Axiom count: 0 (unchanged).
