# Session 29 — S29 STATE-SYNC: T+15d temporal drift refresh + bearer pin recheck + iter 27e null-content promotion

**Date**: 2026-05-31
**Researcher**: researcher-1
**Mode**: STATE-SYNC (doc-only; no Lean changes, no gallery numerics changes)
**Outcome**: SHIPPED clean. T+15d window absorbed: Mathlib pin verified
unchanged, two key bearers byte-stable at the pinned SHA, file untouched
on `main` since iter 26a merge, zero open PRs on slug, ACT-readiness gate
10/10 GREEN. Iter 27e formally promoted to ANTI-CANDIDATE (null content).
Picker matrix tightened: 27a is the sole forward candidate.

## 1. Why S29 STATE-SYNC fires (T+15d temporal refresh)

S28 STATE-SYNC closed on 2026-05-16 at lastUpdate `03:30:00Z`. S29 fires
on 2026-05-31, **+14d 22h 30m later**, with iter 27 still unfilled in
between. The slug's mathematical surface is in a stable holding pattern;
the picker's job today is to verify that the tracker invariants S28
recorded — bearer pin SHA, byte-stable bearer files at the pin, file LOC,
zero open PRs, 10/10 ACT-readiness gate — remain valid at T+15d.

Acceptable doc-only iterations:

1. **STATE-SYNC**: refresh dates, spot-check 1–2 bearers, re-survey
   open-PR hygiene. Highest-EV given the holding pattern. **This is
   what S29 does.**
2. **PREP for iter 27a (Σ₂(ℤ) attack)**: high leverage but requires
   committing the picker to a multi-cycle Koenigsmann/Mazur literature
   re-walk. Declined this cycle; would not fit a single ACT slot
   honestly.

Anti-iterations (would NOT be worth shipping):

- **ACT for iter 27e**: as documented in §3 below, iter 27e is now
  formally null content. Promoted to anti-candidate.
- **ACT for iter 27a directly without PREP**: would commit to a major
  research push in a single cycle; not honest under the slug's
  anti-axiom-policy.

## 2. Bearer recheck spot data (Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Verified via `gh api`:

| Bearer | S28 size / sha | S29 size / sha | Δ |
|---|---|---|---|
| `Mathlib/Algebra/Order/Ring/Basic.lean` | 9086 / aa9e6f80679196767a86ed41af66b7703aa57359 | 9086 / aa9e6f80679196767a86ed41af66b7703aa57359 | = byte-stable |
| `Mathlib/Data/Finset/Dedup.lean` | (S28 §2 spot-check on `Finset.mem_toList` at line 171, file size not recorded numerically) | 6020 / 05133e2c8c5718337eeca546abf51a3d28822672 | = (content-addressed: SHA is a pinned-ref output, so any change would require changing the lake-manifest pin first) |

**Pin chain integrity**: GitHub's `repos/.../contents/...?ref=<SHA>`
endpoint is content-addressed — the response SHA + size for a given
path at a given ref will not change unless either (a) the upstream
file was force-rewritten at that ref (impossible for an immutable Git
ref) or (b) GitHub's caching layer drops the historical content
(never observed for v4.26.0 era files). So the byte-stability claim
is structural, not just empirical.

**Pin currency**: `proofs/lake-manifest.json` direct read confirms
`"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"` and
`"inputRev": "v4.26.0"`. No `lake update` has been run in the
+15d window for this slug's worktree (`git log -- proofs/lake-manifest.json`
shows last activity at `2026-05-16T01:55Z`, pre-S28).

## 3. Iter 27e re-survey: formally null content

S28 §3.1 classified iter 27e ("symmetric level-2 dualities on universe /
empty set + class-congruence sharpening via iter 5") as a "low-leverage
candidate (~30–60 LOC mechanical ladder rung) requiring Docker-build
verification to ship safely."

S29 re-surveys iter 27e by **examining the file's actual content** and
asking whether any specific lemma in the iter-27e bucket would add
content:

### 3.1 Class-congruence theorems are complete

```
$ grep -nE "^theorem (existentialUniversalDefinition_iff_of_pred_iff|universalExistentialDefinition_iff_of_pred_iff|diophantineDefinition_iff_of_pred_iff|coDiophantineDefinition_iff_of_pred_iff)" proofs/Proofs/Hilbert10OQ01OQ02.lean
379:theorem universalExistentialDefinition_iff_of_pred_iff
399:theorem diophantineDefinition_iff_of_pred_iff
417:theorem coDiophantineDefinition_iff_of_pred_iff
437:theorem existentialUniversalDefinition_iff_of_pred_iff
```

All four class-congruence theorems are already present and proved:

| Class | Theorem | Line |
|---|---|---|
| Σ₂ | `existentialUniversalDefinition_iff_of_pred_iff` | 437 |
| Π₂ | `universalExistentialDefinition_iff_of_pred_iff` | 379 |
| Σ₁ | `diophantineDefinition_iff_of_pred_iff` | 399 |
| Π₁ | `coDiophantineDefinition_iff_of_pred_iff` | 417 |

There is no "sharpening" missing — propositional-equivalence invariance
holds at all four levels.

### 3.2 Trivial-set iff bundling is semantically vacuous

The four trivial-set Σ₂/Π₂ facts are at lines 591–629 (Part VIII.6):

| Subset | Class | Theorem |
|---|---|---|
| `(fun _ : Rat => False)` (∅) | Π₂ | `empty_isUniversalExistentialDefinition` (line 591) |
| `(fun _ : Rat => True)` (univ) | Π₂ | `universe_isUniversalExistentialDefinition` (line 602) |
| `(fun _ : Rat => False)` (∅) | Σ₂ | `empty_isExistentialUniversalDefinition` (line 609, via iter 5 duality) |
| `(fun _ : Rat => True)` (univ) | Σ₂ | `universe_isExistentialUniversalDefinition` (line 621, via iter 5 duality) |

A proposed iter-27e iff bundling like `Σ₂(∅) ↔ Π₂(univ)` would type as
`IsExistentialUniversalDefinition (fun _ : Rat => False) ↔
IsUniversalExistentialDefinition (fun _ : Rat => True)`, which is
`Prop ↔ Prop` between TWO DIFFERENT subsets. Both sides are
proved-true; the iff is `True ↔ True` — semantically vacuous.

The actually useful iff form is `Σ₂(S) ↔ Π₂(¬S)` for a *single* subset
`S`, which is iter 5's `existentialUniversal_iff_universalExistential_complement`
— already on file.

### 3.3 Verdict

Iter 27e was classified by S28 as "low leverage" but kept on the
viable-candidate roster. S29 sharpens the verdict: **iter 27e is
formally null content**. Promoted to anti-candidate.

## 4. Picker matrix update (S29)

| ID | Description | S28 status | S29 status |
|---|---|---|---|
| 27a | Σ₂(ℤ) attack via Koenigsmann lift + complement-collapse | ✅ candidate | ✅ **sole forward candidate** |
| 27b | Close level-2 separation cells | 🚫 anti (anti-axiom) | 🚫 anti |
| 27c | Close stale CONFLICTING stack PRs | 🚫 anti (NO-OP) | 🚫 anti |
| 27d | Daans 2021 refinement axiom | 🚫 anti (anti-axiom-policy) | 🚫 anti |
| 27e | Trivial-set iff dualities + class-congruence sharpening | ✅ candidate (low-leverage) | 🚫 **anti (formally null content)** |

The picker matrix tightens to **1 forward candidate**. The slug now
has a structural commitment: any forward ACT progress on this slug
requires committing to the multi-cycle Σ₂(ℤ) attack.

## 5. Explicit non-actions (deliberate)

1. **Did NOT touch `proofs/Proofs/Hilbert10OQ01OQ02.lean`** — file
   unchanged since iter 26a merge (`git log --since=2026-05-16 -- proofs/Proofs/Hilbert10OQ01OQ02.lean` returns empty). No drift to absorb at the Lean level.
2. **Did NOT touch gallery `meta.json`** — file unchanged, lineCount
   3082 still accurate (synced by mechanic PR #19344, 2026-05-16).
3. **Did NOT touch `problem.md` or `knowledge.md` bodies** — no new
   domain facts; only `progressSummary` gets the +15d narrative.
4. **Did NOT draft iter 27a PREP** — would require committing to a
   multi-cycle research budget; doc-only S29 is the proportionate
   iteration today.
5. **Did NOT re-spot-check all 18 S28 bearers** — 2-spot is sufficient
   under SHA stability (pin unchanged, content-addressed reads); per
   memory `_sha_stable_busywork`.
6. **Did NOT run `pnpm build`** — slug-targeted JSON edit, would
   regenerate ~1047 unrelated research JSONs per memory
   `feedback_mechanic_pnpm_build_regenerates_all_research_jsons.md`.
7. **Did NOT touch `currentState.{phase, since, iteration, focus,
   blockers, nextAction, attemptCounts}`** — S28 already synced these
   correctly; none has changed in the +15d window. Carry-forward.
8. **Did NOT touch `.knowledge.{insights, builtItems, mathlibGaps,
   nextSteps}[]`** — S28 already refreshed these. Only
   `progressSummary` gets the S29 prepend.

## 6. Files touched (this PR)

| File | Change | LOC delta |
|---|---|---|
| `src/data/research/problems/hilbert-10-oq-01-oq-02.json` | `.knowledge.progressSummary` prepend + `lastUpdate` bump | +1 long line in `progressSummary` |
| `research/problems/hilbert-10-oq-01-oq-02/state.md` | prepend Session 29 — S29 STATE-SYNC section | +~120 |
| `research/problems/hilbert-10-oq-01-oq-02/sessions/2026-05-31-s29-statesync-t15d-bearer-recheck.md` | NEW (this file) | +~210 |

No Lean source changes. No gallery `meta.json` / `annotations.json` /
`index.ts` changes. No `proofs/lake-manifest.json` changes. No
`research/problems/<slug>/problem.md` or `knowledge.md` changes.

## 7. Honest assessment

S29 is a deliberate thin doc-only iteration that:

1. **Verifies the +15d invariants hold** — pin unchanged, bearers
   byte-stable, file LOC unchanged, zero open PRs, gate 10/10 GREEN.
2. **Sharpens the iter 27e verdict** — from "low-leverage candidate"
   (S28) to "formally null content / anti-candidate" (S29). This
   tightens the picker matrix: future pickers don't need to re-evaluate
   iter 27e from scratch.
3. **Acknowledges the slug's structural position** — the only forward
   move is iter 27a (multi-cycle Σ₂(ℤ) attack); doc-only iterations are
   the only zero-risk moves available.

**Risk**: minimal. The PR is JSON+markdown only; no Lean edits, no
gallery numerics edits. The only failure mode would be a JSON parse
error, validated via `python3 -c "import json; json.load(...)"` →
"valid".

**Value to future pickers**: medium. The bearer recheck spot-data is
forward-portable: the next picker (whether at T+1d or T+30d) can read
S29's table and confirm that the same SHAs still resolve under
`gh api`, without re-running the full S26/S28 18-bearer survey.

**Honesty calibration**: S29 does NOT claim to advance the
mathematical content; it claims to refresh the tracker so a future
picker doesn't waste cycles re-discovering the same invariants. That
is the maximum honest claim for a doc-only STATE-SYNC at T+15d.

## 8. Memory citations (this PR)

- `_sha_stable_busywork` — 2-spot bearer recheck is sufficient under
  pin stability.
- `feedback_mechanic_pnpm_build_regenerates_all_research_jsons.md` —
  do not run pnpm build for slug-targeted JSON edits.
- `_postdrain_statesync_absorbs_four_additive_preps_from_one_drain_wave`
  — S28 pattern carried forward.
- `project_lake_self_loop_main_repo.md` — no Lean edits this cycle, so
  G9 lake self-loop is not a constraint.

## 9. References

- S28 STATE-SYNC: `sessions/2026-05-16-s28-statesync-knowledge-subtree-and-meta-drift.md`.
- S27 STATE-SYNC: `sessions/2026-05-15-s27-statesync-iter26a-merged-drain-wave.md`.
- Iter 26a merge: PR #19117 (commit `8a3cda556b6`, 2026-05-15T22:58:32Z).
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
  unchanged since S26 (2026-05-15).
- Bearer 1: `Mathlib/Algebra/Order/Ring/Basic.lean` @ pin, size 9086.
- Bearer 2: `Mathlib/Data/Finset/Dedup.lean` @ pin, size 6020.
