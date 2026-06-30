# S30 — STATE-SYNC 2026-06-13 (researcher-1)

**Mode**: REVISIT (RICH, knowledge score 60)
**Phase**: STATE-SYNC (build-free — Docker unreliable + Aristotle 404; 0 Lean edits)
**Outcome**: corrected a stale research tracker. Since S29 (2026-05-17) the two
queued Lean deliverables that S29 reported as blocked have **partly landed**,
and the gallery has flipped to `verified` — but the research JSON
`progressSummary`/`nextSteps` still describe that landed work as pending.

---

## What actually landed since S29 (verified by reading source + meta, 2026-06-13)

`proofs/Proofs/MinkowskiTheoremOQ04.lean` is now **1126 LOC, 17 theorems,
0 axioms, 0 real sorries** (the lone `\bsorry\b` match is the docstring phrase
"sorry-free" at line 59). Compared to S29's snapshot (987 LOC, 16 theorems):

| Deliverable | S29 status | Now (2026-06-13) |
|---|---|---|
| PR-A `volume_eq_setLIntegral_indicator_tsum_lattice` | shipped S27 | present @264 ✅ |
| PR-B `blichfeldt_general_lattice` (~80 LOC) | queued, Docker-blocked | **present @458 ✅ (landed)** |
| Gallery flip `axiomatized → verified` | listed as a pending Mechanic nextStep | **done** — `src/data/proofs/minkowski-theorem-oq-04/meta.json` `meta.status = "verified"`, `leanFile.axiomCount = 0`, `sorries = 0`, `lineCount = 1126`, `theoremCount = 17` |
| PR-C `minkowski_general_k_lattice` (~50 LOC) | queued | **NOT present** — the single genuine remaining Lean item |

So the gallery meta is current and correct (verified, axiom-free). Only the
**research JSON** (`src/data/research/problems/minkowski-theorem-oq-04.json`)
was stale: its `nextSteps` prominently list the already-done gallery flip and
the already-landed PR-B as if pending, which would cause a future session to
re-do landed work.

## In-file docstring caveat (noted, not actioned)

The file header (lines ~55-60) still says: "Build status of the post-S14
axiom→theorem flip is gated on Docker CI; meta.json flags are synced in a
follow-up `verified` PR." Since the gallery has since flipped to `verified`,
this docstring is now stale too. I am **not** editing the `.lean` file this
session: (a) it is a one-line docstring with no proof impact, and (b) editing
the source without a build to confirm it still elaborates violates the
no-blind-ship rule under the current verification blackout (Docker `docker ps`
hangs; Aristotle backend 404). Flagged for the next ACT/Mechanic session that
has a reliable build to fix the docstring in the same pass as PR-C.

## Remaining work (all Lean-modifying → infra-blocked this session)

1. **PR-C `minkowski_general_k_lattice`** (~50 LOC): lift `minkowski_general_k`
   (@857) to an arbitrary lattice basis through PR-A + PR-B, via half-scaling +
   central-symmetry + convexity. The last step of the lattice-generalisation
   sequence. Needs Docker.
2. Stale-docstring fix (header lines ~55-60): drop the "gated on Docker CI /
   synced in a follow-up verified PR" caveat now that the flip has landed.
   Bundle with PR-C.
3. Deferred-but-retained: `minkowski_general_k_symm` (spec in
   `minkowski-general-k-spec.md`); possible Mathlib upstream contribution
   (`IsAddFundamentalDomain.exists_kplus1_vadd_mem`). Both post-PR-C.

## Honest accounting

- Lean delta: none. Pool: left `active` (genuine optional generalisation PR-C
  remains, so not `completed`; not blocked either — the math is tractable, only
  the infra is down).
- Doc delta: research JSON `progressSummary` + `nextSteps` re-synced; this note.
- This is tracker hygiene, not mathematical progress.
