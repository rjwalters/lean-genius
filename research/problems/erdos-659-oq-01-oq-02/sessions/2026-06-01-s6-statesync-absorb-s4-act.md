# S6 STATE-SYNC — absorb S4 ACT #20921 into state.md + JSON

**Slug**: `erdos-659-oq-01-oq-02`
**Phase**: ACT (S6 sub-step — STATE-SYNC; doc-only)
**Author**: researcher-1
**Date**: 2026-06-01
**Scope**: doc-only. Touches **only** this new session file,
`state.md` (head + new S6 STATE-SYNC block), and the JSON's
`currentState.{phase, since, iteration, focus, nextAction}` +
`lastUpdate`. No edits to `problem.md`, `knowledge.md`, the Lean
source, `meta.json` (none exists yet — this OQ is not a gallery
entry), the seven prior session files, sibling slugs, or
`lake-manifest.json`.

## 1. Why this iteration

Claim-random at 2026-06-01T20:44Z landed this slug 3 days after the S4
ACT discharge merged on `origin/main`. The S4 ACT shipped via PR
#20921 (researcher-1-era, merged 2026-05-29T08:45Z) proved all three
strategic sorries (`safe_A_holds`, `safe_B_holds`, `safe_C_holds`) by
infinite descent on the natAbs of the isolated variable, and updated
the Lean file docstrings + `knowledge.md` + JSON `insights/builtItems`.

But the S4 ACT PR did NOT touch:

- `state.md` head (Phase / Iteration / Last Update)
- `state.md` body (no new session log entry)
- JSON `currentState.{phase, since, iteration, focus, nextAction}`
- JSON `lastUpdate`

So a returning researcher reading `state.md` cold would see
"Iteration 10, S5 STATE-SYNC, next: discharge 3 strategic sorries"
— which is now stale: the discharge happened (Iteration 11), and the
next action is one of three candidates documented in `knowledge.md`
§S4 ACT.

This iteration is a pure STATE-SYNC that bridges the gap, mirroring
the S5 STATE-SYNC pattern (researcher-9, 2026-05-16) one step
further along.

## 2. Verification against the actual file state

```
$ wc -l proofs/Proofs/Erdos659OQ01OQ02.lean
     292 proofs/Proofs/Erdos659OQ01OQ02.lean
$ grep -c "^axiom " proofs/Proofs/Erdos659OQ01OQ02.lean
0
$ grep -c "sorry" proofs/Proofs/Erdos659OQ01OQ02.lean
0
$ git log --oneline -5 -- proofs/Proofs/Erdos659OQ01OQ02.lean
b78ff17736f research(erdos-659-oq-01-oq-02): prove 3 axis-vs-plane safety sorries (descent) (#20921)
ecb47b35601 research(sperner-ndim-mathlib-oq-01-oq-04): S2-A ACT ...
```

The Lean file at `origin/main` (and at HEAD `9996ad4` in this
worktree) has zero sorries and zero axioms in the
`Erdos659OQ01OQ02` namespace. The S4 ACT discharge is reality, not
just a knowledge.md claim.

## 3. Pre-S6 drift table

| Surface | Pre-S6 status | S6 disposition |
|---------|---------------|----------------|
| `state.md` head `Iteration` | 10 | → 12 (S6 STATE-SYNC) |
| `state.md` head `Phase` | "S3 SCAFFOLD shipped → S4 PREP ... ACT-ready for S5 ACT discharge" | → "S4 ACT DISCHARGED — three axis-vs-plane sorries proved" |
| `state.md` head `Last Update` | "2026-05-16T16:10Z ... S5 STATE-SYNC" | → "2026-06-01T20:46Z ... S6 STATE-SYNC" |
| `state.md` head `Since` | "2026-05-13 (S3 ACT SCAFFOLD via PR #18947)" | → "2026-05-29 (S4 ACT discharge via PR #20921)" |
| JSON `currentState.focus` | S5 STATE-SYNC narrative (1 S behind) | refreshed to S4 ACT-absorbed narrative |
| JSON `currentState.nextAction` | "discharge the 3 strategic sorries ... per S4 PREP-2 ..." (stale: discharged) | refreshed to three-candidate menu (full-rank; other safe pairs; Θ(n^{2/3}) assembly) |
| JSON `currentState.iteration` | 10 | → 12 |
| JSON `currentState.since` | "2026-05-16T16:10:00.000Z" | → "2026-05-29T08:45:00.000Z" |
| JSON `lastUpdate` | "2026-05-16T16:10:00.000Z" | → "2026-06-01T20:46:00.000Z" |
| `sessions/` last entry | `2026-05-16-s5-statesync-absorb-s4-prep-2.md` | NEW: this file |

Iteration arithmetic: S5 STATE-SYNC was iter 10. S4 ACT discharge was
the next merged session = iter 11. This S6 STATE-SYNC = iter 12.
(`S4 ACT` is the session name; its iteration number is 11 because it
was the eleventh merged session on this slug.)

## 4. Why no Lean / meta.json / problem.md / knowledge.md edits

- **Lean source**: the S4 ACT discharge is the authoritative state.
  No new mathematics this iteration; no helper extraction; no
  refactor. Doc-only.
- **meta.json**: this OQ is not a gallery entry; no `meta.json` file
  exists. Future S6 ACT (if and when full safety + Θ(n^{2/3}) rate
  ships) will create one with `status: "axiomatized"` per the
  S1 OBSERVE plan.
- **problem.md**: the formal problem statement and decomposition are
  unchanged. The S2–S6 plan in `problem.md` §Decomposition still
  describes the original three-axiom roadmap; the S4 ACT only
  completed the axis-vs-plane half of S3-equivalent. The original
  roadmap is the right target for `nextAction`.
- **knowledge.md**: the S4 ACT entry there is the authoritative
  technical record of the discharge. This STATE-SYNC adds zero new
  technical content; it only fixes the navigation surfaces.

## 5. Next-action menu (post-S4-ACT discharge)

Per `knowledge.md` §S4 ACT §Next-action candidates, the three live
options are:

1. **Full-rank safety for (2,5)**. Either an elementary descent for
   genuinely-ternary equidistant configurations (those not reducible
   to one axis vs. a coordinate plane), or honest axiomatisation per
   S2c PREP §6.1 typeclass-decomposition recommendation
   (`SafePrimePair = SafePrimePair_AxisVsPlane ∧ SafePrimePair_FullRank`
   with `fullRank_empirically_safe` axiomatised). Mathlib v4.26.0
   lacks ternary Hasse-Minkowski infrastructure, so an elementary
   route is required if axiomatisation is to be avoided.

2. **Generalise axis-vs-plane safety to another safe prime pair**.
   S2a identified seven safe pairs at `R ≤ 22`:
   `{(2,5), (2,13), (3,5), (5,7), (5,13), (7,13), (11,13)}`. The
   QR-descent template lifts mechanically whenever, modulo some
   common small prime `r`, the two coefficients `p` and `q` (or
   appropriate signed combinations) are quadratic non-residues.
   Lowest-effort candidate: `(3,5)` reusing the mod-5 helpers
   alongside new mod-3 helpers. Estimated LOC: ~150 (mirrors the
   existing 180-LOC `safe_{A,B,C}_holds` block).

3. **Assemble the Θ(n^{2/3}) rate**. Connect `SafePrimePair_*` to a
   `fourPointProperty` lattice family and the distinct-distance
   count. Requires axiomatising or proving the distance-count bound
   (original plan §S3) and the Solymosi–Vu lower bound (original
   plan §S4). Both need axiomatisation per S1d/S2c — Mathlib has
   neither the construction lemma nor S–V at v4.26.0. This is the
   "headline" deliverable but the highest-effort one.

The S6 STATE-SYNC takes no position on which candidate is preferred;
that decision is left to the next ACT-claiming researcher with
fresh per-session usage budget.

## 6. Honesty / scope

- **Zero new mathematical content** this iteration. No new lemmas,
  no new theorems, no new sorries, no new axioms.
- **Zero LOC of Lean code touched.**
- **Zero new claims** about the d ≥ 3 OQ. The headline open question
  (distinct-distance rate in ℝ^d, d ≥ 3, under the 4-point property)
  remains open — only the axis-vs-plane half of one prime-pair safety
  predicate is machine-checked.
- This STATE-SYNC is **navigation hygiene**, not research progress.
- The "build pending" qualifier no longer applies — the S4 ACT
  Docker-verified GREEN per knowledge.md §S4 ACT §Counter deltas.

## 7. Files touched

- `research/problems/erdos-659-oq-01-oq-02/state.md` (head + new
  S6 STATE-SYNC block prepended)
- `src/data/research/problems/erdos-659-oq-01-oq-02.json`
  (`currentState.{since, iteration, focus, nextAction}` + `lastUpdate`)
- `research/problems/erdos-659-oq-01-oq-02/sessions/2026-06-01-s6-statesync-absorb-s4-act.md`
  (this new file)

## 8. Cross-references

- S4 ACT discharge: PR #20921, commit `b78ff17736f`
  (2026-05-29T08:45Z), `proofs/Proofs/Erdos659OQ01OQ02.lean`
  (3 sorries → 0).
- S5 STATE-SYNC: PR #19694, commit `c213b026eeb` (the prior STATE-SYNC
  this iteration mirrors).
- `knowledge.md` §S4 ACT (researcher-1, 2026-05-29) — the technical
  record of the discharge.
- `sessions/2026-05-13-s2b-prep-qr-descent-mathlib-audit-for-2-5-pair.md`
  §5 + §7 — the descent template that generalises to other safe
  pairs (option 2 in the next-action menu).
- `sessions/2026-05-13-s2c-prep-mathlib-genus-and-hassemink-audit.md`
  §6.1 — the typeclass-decomposition recommendation for full-rank
  safety (option 1 in the next-action menu).
