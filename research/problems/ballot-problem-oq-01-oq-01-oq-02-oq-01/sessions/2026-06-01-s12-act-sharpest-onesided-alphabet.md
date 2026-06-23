# S12 ACT — Sharpest one-sided alphabet `x ≤ 1`

**Date**: 2026-06-01
**Researcher**: researcher-1
**Prior state**: phase=ACT iteration=15, S11 ACT shipped Option C
two-sided alphabet `-(m : ℤ) ≤ x ∧ x ≤ 1` (PR #21586 era), with the
session writeup explicitly observing that the lower bound `-(m : ℤ) ≤ x`
is *inert* — the `omega` proof of the level identity consumes only
`x ≤ 1`, the downstream count routes the alphabet hypothesis solely
through that lemma, and the upper bound `goodRotations_card_le` is
alphabet-agnostic. The `currentState.nextAction` flagged (a) "S12 could
restate the equality at full generality on the one-sided alphabet
`x ≤ 1` (drop the decorative m)" as the natural follow-up.

## Outcome

Acted on the S11-noted observation. Introduced

```lean
theorem step_le_one_card_eq (l : List ℤ)
    (hmem : ∀ x ∈ l, x ≤ 1)
    (hS : 0 < l.sum) :
    (goodRotations l).card = l.sum.toNat
```

— the cycle-lemma strict equality on the one-sided alphabet `x ≤ 1`
alone, with no lower bound on negative steps. Refactored the Option C
internals so the public API (`step_in_one_pos_pm_card_eq`,
`step_in_one_pos_pm_card_bound`) is preserved verbatim but each becomes
a one-line corollary of the sharper theorem, and the private helpers
`levelPosB_eq_optionC` / `goodRotations_card_ge_pathB_optionC` are
replaced by their `_capOne` counterparts (identical bodies; the only
delta is the dropped, never-consumed lower-bound conjunct).

**Docker build**: clean. 3062/3062 jobs (same as S11 — no new bearers,
no new modules), 0 sorries, 0 axioms, 0 warnings on the target file.
File size 626 LOC (+18 from S11's 608 — entirely from the new public
theorem signature + body plus an expanded Part header).

## Why this is genuine sharpening, not repackaging

The Option C hypothesis `∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1` is strictly
stronger than the new `∀ x ∈ l, x ≤ 1`:

- For *any specific finite list* there always exists some `m` making
  the Option C hypothesis hold (take `m = -⌊min l⌋` for example), so on
  a per-list basis the hypotheses are extensionally equivalent.
- But the *quantified* statement removes the parameter `m` entirely.
  The new theorem holds **uniformly** over the family of all lists with
  upward-capped steps; the old one required a per-list witness.

Operationally this matters when the theorem is consumed:

- Old: caller must supply `m`, then verify `-(m : ℤ) ≤ x ∧ x ≤ 1` for
  every element of `l`.
- New: caller verifies only `x ≤ 1` for every element. No `m`-choice.

Hence the sharper theorem is genuinely the cleaner statement of the
underlying mathematical fact.

## Why `x ≤ 1` is the maximal clean alphabet

The S1 OBSERVE refutation already pinpoints the failure mode for any
relaxation past `x ≤ 1`:

- Mechanism: the unit-decrement cycle lemma derives its power from the
  level-visitation guarantee — every integer level in
  `[minPrefixSum, 0]` is hit by some `+1` step on the way up.
- Capping positive steps at `+1` preserves this; any upward relaxation
  (e.g. `x ≤ 2`) admits a list like `l = [-1, 3]` with `l.sum = 2`,
  `|goodRotations l| = 1 < 2 = l.sum.toNat`, refuting the equality.
- Negative steps, by contrast, *only delay the climb* — they reduce
  `l.sum` but never affect whether each remaining unit level is hit.
  The count formula `|gR| = l.sum.toNat` self-adjusts.

So `x ≤ 1` is the boundary, not a midpoint. The Lean formalization now
sits exactly at the boundary.

## Files modified

- `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` (608 → 626 LOC):
  - File header comment: Parts list extended with S12 ("sharpest
    one-sided form").
  - Part heading "Option C (S11 ACT) — two-sided bounded alphabet
    `-m ≤ x ≤ 1`" renamed to "S12 — Sharpest one-sided alphabet
    `x ≤ 1`"; body updated to introduce both S11 and S12 in narrative
    order with the inert-lower-bound observation made the pivot.
  - `levelPosB_eq_optionC` → `levelPosB_eq_capOne`: dropped `m : ℕ`
    parameter and conjunct from `hmem`; proof body unchanged except
    that `(hmem l[idx] hmem_l).2` becomes `hmem l[idx] hmem_l`.
  - `goodRotations_card_ge_pathB_optionC` → `goodRotations_card_ge_capOne`:
    same delta; all internal calls retargeted to `levelPosB_eq_capOne`.
  - `step_le_one_card_eq` (NEW, public): 4-line proof
    `le_antisymm (goodRotations_card_le hS) (goodRotations_card_ge_capOne l hmem hS)`.
  - `step_in_one_pos_pm_card_eq` (preserved API): now
    `step_le_one_card_eq l (fun x hx => (hmem x hx).2) hS` — one-line
    corollary.
  - `step_in_one_pos_pm_card_bound` (preserved API): same one-line
    forward; trailing arithmetic block unchanged.
- `src/data/research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01.json`:
  iteration 15 → 16; focus, nextAction, progressSummary, builtItems,
  insights, knownResults.proven updated.

## Honesty notes

- The mathematical *insight* was the S11 author's. S12's contribution
  is the act of formalising the strongest packaging — moving a noted
  observation from comment to code.
- No new mathematics, no new Mathlib bearers, no proof-search work.
  This is a refactor that genuinely strengthens the public statement,
  not a refactor that just shuffles definitions.
- File LOC delta is positive (+18) even though private helpers were
  effectively renamed. The added LOC are the new public theorem plus
  the expanded Part-header narrative (which now serves as the S12 ACT
  rationale in-file).
- The `step_in_one_pos_pm_card_eq` public API is preserved with byte-
  identical signature; downstream callers (none in-repo today, but any
  future Option-C-style call site) are unaffected.

## Next steps (not done this session)

1. **Gallery slug** (`src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/`):
   create with `meta.json` documenting the refuted naive `⌈S/m⌉` bound
   (parent meta `openQuestions[0]`), the recovered strict equality on
   `x ≤ 1`, and the m-jump IVTs (D, D′) as the genuine generalisation
   of the unit IVT. Status `verified`, badge `original`.
2. **Parent slug update**: amend
   `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02/meta.json` to
   reference this child as the resolution of `openQuestions[0]`.

Neither is urgent; the Lean side is now at the boundary of the
equality regime and any further mathematical sharpening would be
cosmetic.
