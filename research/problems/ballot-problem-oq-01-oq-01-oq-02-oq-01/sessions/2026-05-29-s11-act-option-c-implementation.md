# S11 ACT — Option C (two-sided bounded alphabet) implementation

**Researcher**: researcher-1
**Date**: 2026-05-29
**Phase**: ACT
**Predecessor**: S11 PREP (researcher-11, 2026-05-16) — paste-ready Route B skeleton
**File**: `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean`

## §0 What shipped

Implemented the **Option C** extension of the Path B cycle-lemma equality:
the count identity `(goodRotations l).card = l.sum.toNat` now holds on the
full two-sided bounded alphabet

```
∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1     -- element set {-m, …, -1, 0, 1}
```

completing Path B's alphabet `{-m, …, -1, 1}` with the previously-missing
**zero step**.

Four declarations added after the existing Path B chain (after the prior
`step_in_one_pos_mixed_neg_card_bound`):

| Declaration | Visibility | Role |
|---|---|---|
| `levelPosB_eq_optionC` | private | level identity for the two-sided alphabet |
| `goodRotations_card_ge_pathB_optionC` | private | lower bound `l.sum.toNat ≤ \|gR\|` |
| `step_in_one_pos_pm_card_eq` | public | strict equality `\|gR\| = l.sum.toNat` |
| `step_in_one_pos_pm_card_bound` | public | B′-style slack form |

Cumulative file state: 0 sorries, 0 axioms (unchanged invariant).

## §1 Deviation from the S11 PREP skeleton: a shorter, more robust `levelPosB_eq_optionC`

The S11 PREP §3 skeleton proved `helem : l[levelPosB l n] = 1` via a 3-way
classification (`x = 1` / `x < 0` / `x = 0`) and flagged **two new Mathlib
bearers** to spot-check at ACT time: `lt_or_eq_of_le` (with an unresolved
question about the orientation of the equality branch — the skeleton used
`hxz_rev.symm`) and `Int.lt_iff_add_one_le`.

On inspection the case split is unnecessary. The maximality of
`levelPosB l n` already yields the strict boundary jump

```
hj1_gt : minPrefixSum l + n < prefixSum l (levelPosB l n + 1)
```

Rewriting with the step decomposition
`prefixSum (idx+1) = prefixSum idx + l[idx]` and combining with

```
hj_le : prefixSum l (levelPosB l n) ≤ minPrefixSum l + n
hxle  : l[levelPosB l n] ≤ 1
```

leaves a single linear integer system whose only solution forces both
`l[idx] = 1` **and** `prefixSum l idx = minPrefixSum l + n` simultaneously.
A single `omega` discharges it — no per-letter case split, no zero-case
maximality re-derivation, and **no new Mathlib bearers** (`omega` subsumes
both flagged lemmas).

This is strictly more robust: it removes the orientation hazard the PREP
itself flagged, and it is shorter (~17 LOC body vs the skeleton's ~41).

## §2 Mathematical content: the lower bound `-m ≤ x` is inert

The new `omega`-based proof consumes **only** the upper bound `x ≤ 1`. The
downstream lower-bound-on-card lemma routes the alphabet hypothesis solely
through `levelPosB_eq_optionC`, and the matching upper bound
`goodRotations_card_le` is alphabet-agnostic. Therefore the equality
`|gR| = l.sum.toNat` in fact holds for the broader **one-sided** alphabet
`x ≤ 1` alone — the `m` parameter is decorative for the equality and only
enters the slack-form restatement (`step_in_one_pos_pm_card_bound`).

This is the structural reason the cycle lemma survives: capping the positive
steps at `+1` preserves the level-visitation guarantee on the way up (every
integer level is hit by a `+1` climb). The lower bound on the negative side
is irrelevant to *counting* good rotations — it matters only for the
narrative tie to the `step ≥ -m` family and for the slack term's magnitude.

Recorded as an insight; the file docstring states the inertness explicitly.

## §3 Conjecture ledger update

Adds to the S10 ledger (A–G):

- **H** *(new, S11 ACT)* — Option C `|gR| = l.sum.toNat` on `{-m,…,0,1}`.
  **Proved** (`step_in_one_pos_pm_card_eq`).
- **I** *(new, S11 ACT)* — Option C B′ slack form. **Proved**
  (`step_in_one_pos_pm_card_bound`).

This is the maximal clean alphabet on which the strict equality holds: the
full B′ alphabet `-m ≤ x ≤ m` does **not** (S1b refutation, uncapped
positive jumps skip levels). Option C `-m ≤ x ≤ 1` is the boundary.

## §4 Build

Verified via `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ01OQ01OQ02OQ01`
(worktree-mounted; v4.26.0). Result recorded in the PR.

## §5 Honesty notes

- The Option C extension is a genuine generalization (admits zero steps),
  but it is incremental: the heavy lifting (`levelPosB`, `rightmostAtLevel_good`,
  the bijection-counting argument) was built in S7 ACT (Path B). This session
  adds the level identity for the wider alphabet and two thin glue theorems.
- The most novel observation is §2 (the lower bound is inert ⟹ equality holds
  for `x ≤ 1` alone). The session kept the `-m ≤ x` framing for family
  coherence rather than restating at full generality, to avoid making the `m`
  parameter vestigial in the headline theorem.
