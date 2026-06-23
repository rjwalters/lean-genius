# Session S9 STATE-SYNC — post-S8-ACT-merge reconciliation

**Date**: 2026-06-04
**Researcher**: researcher-1
**Phase transition**: ACT-S8-PASTED → ACT-MERGED
**Type**: doc-only state reconciliation (no Lean, no gallery, no build)
**Iteration**: 12 (preceded by S8 ACT iteration 11, merged 2026-06-02 via #22088)

## Context

The S8 ACT PR #22088 (researcher-1, polymorphic main theorem
`riemannianVolumeBall_hasDerivWithinAt`) was merged on
2026-06-02T13:20:45Z, commit `fd413760cf7`. As of this S9 STATE-SYNC
claim (2026-06-04), `state.md` and the JSON cursor
`src/data/research/problems/circumference-via-differentiation-oq-03.json`
both still presented the S8 ACT PR as open (`phase: ACT-S8-PASTED`,
"build pending — G9 lake self-loop") — a 2-day drift between merged
reality and the recorded state.

The S8 ACT documents (state.md "Next Action" section, written 2026-06-02
in anticipation of the merge) explicitly listed STATE-SYNC as one of
the four valid next-claim options after the R1 vector-space ACT
roadmap completes:

> For the next claim on this slug: there is no meaningful in-repo ACT
> deliverable remaining. Recommend **release-and-cycle silently** unless
> (a) a substantive Mathlib bearer drift is observed, (b) the G9 blocker
> clears and a Docker re-verification PR makes sense, or (c) a follow-up
> gallery slug is seeded for the R2/R3 path.

The literal recommendation was "release-and-cycle silently", but
the S5 STATE-SYNC precedent on this same slug (2026-05-30, doc-only
reconciliation of the S2 ACT bulk-merge landing) demonstrates that
STATE-SYNCs are the appropriate cycle when state documents have
drifted from merged reality, even when no Mathlib bearer drift is
observed. This S9 STATE-SYNC follows that precedent.

## Verification on main (researcher-1 worktree, HEAD ac6fb953b79)

Verified state of the OQ-03 file post-S8-ACT-merge:

- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`:
  - **194 LOC** (matches state.md S8 ACT prediction)
  - **6 theorems** (`grep -c "^theorem \|^lemma "` returns 6)
  - **0 sorries** (`grep -c "sorry"` returns 0)
  - **0 axioms** (`grep -c "^axiom "` returns 0; the matched `"axiom"`
    occurrence is the comment header `"Status: 0 sorries, 0 axioms."`)
  - **4 imports**, including `import Proofs.CircumferenceViaDifferentiationOQ01`
    (added by S7 ACT-S3, preserved through S8 ACT)
  - The 6 theorems:
    1. `riemannianVolumeBall_fin_two` — S2 ACT, n=2 Bridge 1
    2. `riemannianVolumeBall_fin_three` — S2 ACT, n=3 Bridge 1
    3. `riemannianVolumeBall_hasDerivWithinAt_fin_two` — S2 ACT, n=2 Main
    4. `riemannianVolumeBall_hasDerivWithinAt_fin_three` — S2 ACT, n=3 Main
    5. `riemannianVolumeBall_eq_nBallVolumeFn` — S7 ACT-S3, polymorphic Bridge 1
    6. `riemannianVolumeBall_hasDerivWithinAt` — S8 ACT, polymorphic Main

- `proofs/Proofs.lean`: `import Proofs.CircumferenceViaDifferentiationOQ03`
  present (S2 ACT bulk-merge landed it; unchanged since).

- `src/data/proofs/circumference-via-differentiation-oq-03/meta.json`
  (S6 GALLERY-WIRING, updated through S8 ACT, on main):
  - `meta.status: "verified"`
  - `meta.badge: "original"`
  - `meta.sorries: 0`
  - `meta.axiomCount: 0`
  - `meta.lineCount: 194` ✓ (matches reality)
  - `meta.theoremCount: 6` ✓ (matches reality)
  - `assumptions`: refreshed under S8 ACT to credit
    `CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt` as
    the parent-derivative bearer composed via `HasDerivWithinAt.congr`.

No drift detected between meta.json and reality. No meta.json edit
needed.

## Mathlib bearer pre-flight

Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`: unchanged from
S7 ACT-S3 / S8 ACT (4-day gap from S7 ACT-S3 write; 2-day gap from
S8 ACT merge). Per the S8 ACT iteration's SHA-pin transitivity, all
S3 PREP §2.1 bearer rows (`InnerProductSpace.volume_closedBall` at
line 372 of `VolumeOfBalls.lean`; `EuclideanSpace.volume_closedBall_fin_two`
at line 325; `EuclideanSpace.volume_closedBall_fin_three` at line 342;
and the sibling rows at 361, 377, 383, 389, 399, 417, 427) remain
in force. No bearer drift observed.

This S9 STATE-SYNC introduces **zero new Mathlib bearer dependencies**
(doc-only).

## Changes shipped in this PR

| File | Δ | Nature |
|------|---|--------|
| `research/problems/circumference-via-differentiation-oq-03/state.md` | ~80 net lines | Header phase ACT-S8-PASTED → ACT-MERGED; Since updated 2026-06-04T16:30Z; Iteration 11 → 12; new Current Focus (S9) ahead of Previous Focus (S8); Verified Deliverables retitled to "post-S8 ACT merge #22088" with all 6 theorems listed; Open PRs reframed (S8 ACT marked MERGED via #22088, this S9 STATE-SYNC PR added); Iteration History +1 row (this S9 STATE-SYNC); Reference Files extended with this session doc. |
| `src/data/research/problems/circumference-via-differentiation-oq-03.json` | 1 currentState block | phase ACT-S8-PASTED → ACT-MERGED; since → 2026-06-04T16:30:00.000Z; iteration 11 → 12; focus rewritten as S9 STATE-SYNC summary; blockers refreshed (G9 + R2/R3 Mathlib roadmap); nextAction unchanged in spirit (release-and-cycle silently); attemptCounts.total 11 → 12; lastUpdated → 2026-06-04T16:30:00.000Z. |
| `research/problems/circumference-via-differentiation-oq-03/sessions/2026-06-04-s9-state-sync-post-s8-act-merge.md` | new file | this session doc. |

**No Lean modification. No gallery `meta.json` modification. No
`annotations.json` modification. No new imports. No build needed.**

## R1 vector-space ACT roadmap: CLOSED

After this S9 STATE-SYNC reconciles the records, the R1 vector-space
ACT roadmap is CLOSED on main with 6 theorems shipped (4 concrete +
2 polymorphic). The remaining theoretical scope on the OQ-03 question
is exclusively Mathlib-roadmap (R2 full Riemannian, R3 n-dim coarea
formula), each gated on >500 LOC of foundational Mathlib bearer that
does not exist at v4.26.0. These are out of scope for in-repo OQ-03
work.

## Next-claim guidance

For subsequent researcher claims on this slug:

1. **Release-and-cycle silently** is the recommended baseline. The R1
   roadmap is closed; no in-repo ACT deliverable remains.
2. **Mathlib bearer drift STATE-SYNC**: if a future SHA pin update
   breaks the S7 ACT-S3 or S8 ACT bearers (`InnerProductSpace.volume_closedBall`,
   `EuclideanSpace.volume_closedBall_fin_two/three`,
   `CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt`,
   `HasDerivWithinAt.congr`), a repair-style STATE-SYNC is warranted.
3. **G9 lake self-loop clears**: a Docker re-verification PR re-checking
   the 6-theorem file becomes possible. Likely ceremonial if bearers
   haven't drifted (the file is structurally simple — 4 imports +
   composition of in-repo theorems via congr).
4. **R2/R3 follow-up slug seeded by seeker**: a brand-new slug for
   one of the Mathlib-roadmap gaps (injectivityRadius, expMap,
   geodesicBall, n-dim coarea) — claim it as a fresh OQ rather than
   continuing OQ-03.

## Calibration / honesty

This S9 STATE-SYNC ships **zero** in-repo correctness change: it
brings the documentation into agreement with what merged 2 days ago.
The S5 STATE-SYNC precedent on this same slug (2026-05-30) sized
similar reconciliations as legitimate doc-only deliverables — they
prevent future researcher cycles from re-running pre-flight on a
file that is already merged.

Phase: ACT-MERGED. Iteration: 12. Status preserved: verified, 0/0/194/6.
