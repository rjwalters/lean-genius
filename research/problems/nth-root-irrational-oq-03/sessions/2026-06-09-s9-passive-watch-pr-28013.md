# S9 Passive Watch — PR #28013 staleness at T+4d post-S8

**Date**: 2026-06-09T23:59:00Z (T+4d post-S8 ACT)
**Researcher**: researcher-1 (claim id researcher-13378)
**Mode**: STATE-SYNC (doc-only; passive PR #28013 watch tick + invariant verification)
**Outcome**: progress — PR #28013 SHA still unchanged at T+11.7d since last update; grace period through ~2026-06-26 (17 days out)

## Headline

S8 ACT (researcher-11, 2026-06-05) shipped `PiTranscendental.lean` axiom
reduction (1 → 0 local) via the `IsFractionRing.isAlgebraic_iff` bridge
to `HermiteLindemann.lean`'s `hermite_lindemann` axiom — Docker-verified
GREEN 3092/3092 jobs. The S8 next-step menu is dominated by passive watch
of Mathlib PR #28013 (Lindemann-Weierstrass Theorem), which would let us
discharge the `hermite_lindemann` axiom itself.

**PR #28013 status at S9 (2026-06-09)**:

```
$ gh api repos/leanprover-community/mathlib4/pulls/28013 \
    --jq '{state, headSha, updatedAt}'
{
  "state": "open",
  "headSha": "5abb7c68488b527e4d7ecf5d7bbe085db8d2a388",
  "updatedAt": "2026-05-29T07:22:48Z"
}
```

`headSha` and `updatedAt` are **identical** to S8 ACT's reading
(2026-06-05). Staleness: T+11.7 days since last update.

S6 PREP (researcher-11, 2026-06-03) extended the grace period to "~3-4
weeks after crossing the staleness threshold", crossing happened
2026-06-05, so grace period extends through **~2026-06-26** (17 days out
from S9). Continue passive watch.

## Invariants at S9 (file unchanged at T+4d)

| Item | S8 ship (2026-06-05) | S9 check (2026-06-09) |
|------|----------------------|------------------------|
| `proofs/Proofs/PiTranscendental.lean` LOC | 432 | 432 |
| `^axiom ` count | 0 (was 1 pre-S8) | 0 |
| `sorry` count | 0 | 0 |
| `pi_transcendental` proof | alias to `HermiteLindemann.pi_transcendental_real` | unchanged |
| `lindemann_theorem` | theorem (derived from hermite_lindemann) | unchanged |
| Mathlib pin SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) | unchanged |

The file is bit-identical to S8 ship state. All other S8 deliverables
(meta.json axiomCount 1→0, theoremCount 18→19, lineCount 457→432;
`HermiteLindemann.lean` import wiring) also remain on main.

## What S9 STATE-SYNC ships

Doc-only iteration counter bump + passive watch documentation. **No Lean
edits.** Documents PR #28013's 11.7-day stale status to give the next
picker accurate signal for when to escalate from passive watch to either:

1. **Active intervention** (e.g., audit PR #28013's review queue, ping
   the author, propose a refactor) — currently not warranted; the
   `~2026-06-26` grace period is far off.
2. **S5d.A fallback** (CF expansion of e to discharge
   `e_not_liouvilleWith_gt_two`, 280-480 LOC) — banked for after the
   grace period expires without merge.

## Updated next-step menu (S10+)

1. **(S10 passive watch — recommended)**: Re-check PR #28013 SHA at the
   next claim cycle. If still stale through `~2026-06-26`, switch
   approach to (2).
2. **(S5d.A active fallback)**: CF expansion of e for
   `e_not_liouvilleWith_gt_two` axiom discharge. 280-480 LOC,
   multi-session.
3. **(S8 follow-up — low priority)**: `pi_transcendental_over_rationals`
   has a cleaner ℚ-direct path via the new theorem; current proof routes
   through ℤ. Not on critical path.
4. **(Mechanic scope, out of researcher)**: `ETranscendentalOQ02.lean`
   pre-existing build error at line 708 ("no goals"). Out of researcher
   scope.

## Out of scope (deferred)

- Lean file edits — explicit scope: passive watch tick + invariant verify.
- Gallery `meta.json` numerics — file unchanged, no drift.
- PR #28013 audit (commits, conversation, review state) — defer until
  grace period expires.
- S5d.A fallback — banked.
