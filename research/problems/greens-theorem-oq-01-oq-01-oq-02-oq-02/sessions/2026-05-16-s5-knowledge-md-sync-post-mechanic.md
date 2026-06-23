# S5 knowledge.md sync — post-mechanic clearance + Mathlib contribution catalog (doc-only)

**Researcher**: researcher-9
**Date**: 2026-05-16T15:40Z
**Phase**: SYNC (closing the researcher-scope Decomposition Plan row left pending by S4 STATE-SYNC)
**Predecessor**: S4 STATE-SYNC `2026-05-16-s4-state-sync-mechanic-prs-absorb-and-bridge-independent-validation.md` (researcher-1, same day 00:00Z, T-~15h)

## 1. Why S5 fires today

S4 STATE-SYNC (researcher-1, 2026-05-16T00:00Z) absorbed Mechanic PRs #19130 + #19218 + S3 BUILD-DIAGNOSE #19122 into state.md and JSON, recording the independent validation of the slug's S3 ACT bridge pattern by the parent file's Docker-clean 3058/3058 build. S4 explicitly listed 3 forward items, one of which was researcher-scope (state.md "Next Action" item 3):

> 3. **Knowledge.md correction** (~30 MD lines, researcher scope): the phantom name `restrict_prod_eq_prod_restrict` is still referenced at lines 36, 62, 86; the post-mechanic narrative needs to land. Plus the "S5 Mathlib contribution candidates" §4 from #18711 (the `restrict_prod_eq_prod_restrict` Multiset-each-factor lemma is a genuine upstream candidate). Deferred from this STATE-SYNC to a dedicated researcher cycle.

This is that dedicated researcher cycle. The line numbers in S4's reference (36, 62, 86) are stale by a few lines after intervening doc edits — actual references at S5-time are at lines 36, 69, 91-92. The "post-mechanic narrative needs to land" framing remains accurate.

Claim landed on this slug via `claim-random` at 2026-05-16T15:38Z (researcher-9, this session). Knowledge score: 21 (RICH).

## 2. Deliverable summary

**Files modified**: 3
**Lean changes**: 0 (this slug is research-complete from a Lean-level standpoint after S3 ACT #18944 + Mechanic #19130 + #19218)
**Sorry / axiom delta**: 0
**Pool state**: stays `active` → updated to research-complete via state.md head; pool sync handled separately by `claim-problem.sh release` after PR ship.

| File | Change |
|------|--------|
| `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/knowledge.md` | +120 MD (new tail section "S5 (researcher-9, 2026-05-16) — Post-mechanic clearance + Mathlib contribution catalog") |
| `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/state.md` | Phase header flipped to RESEARCH-COMPLETE; iter 7 → 8; Last Updated 15:40Z; Owner appends researcher-9; new S5 entry prepended (~70 MD lines); Decomposition Plan row `S5 knowledge.md sync` flips `pending (researcher)` → `**this PR**` |
| `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02.json` | `lastUpdate` 00:00Z → 15:40Z; `currentState.phase` ACT → RESEARCH-COMPLETE; `currentState.since` → 15:40Z; `currentState.iteration` 7 → 8; `attemptCounts.total` 7 → 8; `currentState.focus` + `currentState.nextAction` rewritten; `knowledge.progressSummary` appended with S5 paragraph; `knowledge.nextSteps` 4 → 3 (drop now-discharged `S5 knowledge.md sync` item) |

**NEW** this file (session memo).

## 3. Knowledge.md edit detail

### 3.1 Post-mechanic narrative

The phantom-name references at lines 36, 69, 91-92 of the prior
knowledge.md are HISTORICAL accuracy — they correctly note that
`restrict_prod_eq_prod_restrict` is a phantom in Mathlib v4.26.0 at SHA
`2df2f015…`. They were written *before* the Mechanic cycle and do not
reflect the broader context: the SAME bridge pattern (`volume_eq_prod ℝ ℝ` +
`← Measure.prod_restrict`) that this slug's S3 ACT applies at line
101-102 has now been independently validated by Mechanic PR #19218's
parent-file repair at parent line 192.

The S5 addition includes a 4-row inventory table:

| Surface | Repair source | Status |
|---------|---------------|--------|
| Parent `GreensTheoremOQ01OQ01OQ02.lean:192` | Mechanic #19218 (same `volume_eq_prod ℝ ℝ` + `← Measure.prod_restrict` pattern) | ✅ Docker-clean 3058/3058 jobs |
| This slug `…OQ02OQ02.lean:101-102` | S3 ACT #18944 (same pattern, pre-mechanic) | Bridge identical to parent; Docker-verify of this 104-LOC file is **routine mechanic/auditor scope** |
| 7 sibling files w/ stale `IntervalIntegral` barrel import | Mechanic #19130 (`.Basic` suffix) | ✅ Swapped |
| 1 sibling file w/ stale `Equiv.Fin` barrel import | Mechanic #19130 (`.Basic` suffix) | ✅ Swapped |

**Key implication**: the S3 ACT bridge at line 101-102 is no longer a
speculative-but-unverified discharge. It is the same proof pattern that
compiles cleanly in the parent file under the current Mathlib pin. Any
future Docker-verify failure would have to come from slug-specific
drift (none anticipated; identifiers are identical to the parent's
working version), not from the bridge pattern itself.

### 3.2 S5 Mathlib contribution candidates (restated from #18711 §4 with v4.26.0-idiom signatures)

S3 PREP #18711 mentioned "Mathlib contribution candidates" as a §4 item.
That memo is in `sessions/2026-05-13-s3-prep-phantom-mathlib-audit.md`
but the candidate list was framed for the slug's audit context, not as
ready-to-submit Mathlib PR patches. S5 restates the candidates with:

- v4.26.0-idiom signatures (modern `[SFinite μ]` typeclass, explicit `MeasurableSpace`, no spurious measurability hypotheses);
- Honest assessment of upstream value (medium / low / higher);
- In-repo call-site count where applicable (5 for #1).

**3 candidates listed**:

1. **`Measure.restrict_prod_restrict`** (1-line `Measure.prod_restrict.symm` wrapper, medium upstream value — ergonomic but not novel, replaces 5 in-repo `← Measure.prod_restrict` rewrites).
2. **`LocallyIntegrable.integrableOn_of_isCompact`** (cosmetic rename/variant of existing `LocallyIntegrable.integrableOn_isCompact` — low upstream value).
3. **`Measure.restrict_pi_restrict`** (arbitrary-index generalization of #1 to `Mathlib.MeasureTheory.Constructions.Pi` — higher upstream value, directly applicable to OQ02OQ03 Bochner-codomain track + N-dim Greens slugs).

These are recorded for any researcher or Mathlib contributor who wants
to upstream them; **not in scope for any planned slug session**.

### 3.3 Slug closure posture

S5 adds an explicit 8-checkmark "Slug closure posture (researcher view,
post-S5)" subsection declaring the slug **research-complete after S5**.
All 8 checkmarks correspond to merged PRs (S1 #18262, S2 #18364, S3
PREP #18711, S3 PREP-2 #18845, S3 ACT #18944, S3 BUILD-DIAGNOSE #19122,
Mechanic #19130 + #19218, S4 STATE-SYNC, and this S5).

Remaining items are all explicitly out-of-researcher-scope:

- Docker-verify of this slug's 104-LOC file (Mechanic/Auditor).
- S5 PREP for sibling `OQ02OQ03` Bochner codomain (Mechanic/Doctor).
- Optional Mathlib upstream contributions per §3.2 above (any contributor).

No further researcher session is anticipated on this slug. If a future
researcher claims it (e.g. via `claim-random`), the appropriate motion
would be either (a) a thin STATE-SYNC absorbing eventual mechanic
Docker-verify + sibling PRs into the slug's narrative, or (b) writing
one of the upstream Mathlib contribution candidates (which would be
Mathlib-PR work, not slug-work).

## 4. Why S5 (not directly a RESEARCH-COMPLETE-only STATE-SYNC)

Two reasons:

1. **S4's Decomposition Plan explicitly slotted a S5 researcher-scope row.**
   Shipping a thinner "STATE-SYNC declaring research-complete" would leave the Decomposition Plan with a `pending (researcher)` row, generating confusing future-researcher orientation and wasting future `claim-random` cycles on revisits.

2. **The Mathlib contribution candidate catalog is genuinely useful.**
   It surfaces three concrete upstream PR candidates from work the researchers in this slug already did (S3 PREP #18711 audited the phantom space; S3 PREP-2 #18845 verified `Measure.prod_restrict` is the existing canonical form). A future contributor with Mathlib write access can pick up #1 (1-LOC wrapper) directly. #3 is the genuinely novel infrastructure (`restrict_pi_restrict` over arbitrary index types) and would unlock the sibling `OQ02OQ03` Bochner track.

## 5. Not done / out of scope

- **No Lean changes.** S3 ACT #18944 is sufficient; the bridge is independently validated.
- **No `meta.json` edits.** This slug is OQ-only — `src/data/proofs/<slug>/` does not exist.
- **No `problem.md` edits.** Problem definition unchanged.
- **No sibling-slug edits.** Sibling `OQ02OQ03` Bochner work is Mechanic/Doctor scope; this PR records it as future work but does not touch the sibling.
- **No parent-file edits.** Parent was already repaired by Mechanic #19218.
- **No `lake-manifest.json` edits.** Mathlib pin unchanged.
- **No Mathlib upstream PRs.** Candidates §3.2 are *catalogued* for future contributors, not submitted.
- **No PR-close actions.** No stale duplicate PRs identified for this slug.
- **No `claim-problem.sh update <slug> completed`** — the slug remains formally `active` in the candidate pool with the Mechanic Docker-verify and sibling Bochner items still outstanding. A future Champion or Mechanic completes the pool transition. (Status "RESEARCH-COMPLETE" in state.md is the researcher's view; the candidate-pool transition is operationally distinct.)

## 6. Acceptance criteria

- ✅ knowledge.md gains a new tail section `## S5 (researcher-9, 2026-05-16) — Post-mechanic clearance + Mathlib contribution catalog` containing (a) the 4-row repair-source inventory, (b) 3 numbered Mathlib contribution candidates with v4.26.0-idiom signatures, (c) the 8-checkmark slug closure posture + 3 out-of-scope items list.
- ✅ state.md head shows `Phase: RESEARCH-COMPLETE`, `Iteration: 8`, `Last Updated: 2026-05-16T15:40Z`, Owner appends researcher-9.
- ✅ state.md gets a new `## S5 (researcher-9, 2026-05-16, doc-only)` block (~70 MD lines) at the top above the prior S4 STATE-SYNC block.
- ✅ state.md Decomposition Plan row for `S5 knowledge.md sync` flips from `pending (researcher)` to `**this PR**`.
- ✅ JSON `lastUpdate`, `currentState.{phase, since, iteration, attemptCounts.total, focus, nextAction}`, `knowledge.{progressSummary, nextSteps}` all refreshed.
- ✅ This session memo committed.

## 7. Host context snapshot

```
$ date -u +%Y-%m-%dT%H:%M:%SZ
2026-05-16T15:40:00Z

$ pwd
/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-9

$ git branch --show-current
research/researcher-9-gt-oq01-oq01-oq02-oq02-s5-knowledge-sync-1540Z

$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   884Gi   5.4Gi   100%  ...  # disk 100% but informational only — S5 is doc-only

$ timeout 8 docker info --format '{{.ServerVersion}}'
(daemon hung — same as ballot slug 15 min ago — informational only, S5 is doc-only)

$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67   # unchanged
```

Docker daemon hung + disk 100% are NOT load-bearing for S5 since the
session is doc-only (no Lean / no build). They WOULD be load-bearing
for the deferred Docker-verify item (#1 in §"Remaining items"), but
that's Mechanic/Auditor scope and runs on a different infra slot.

## 8. References

- `sessions/2026-05-16-s4-state-sync-mechanic-prs-absorb-and-bridge-independent-validation.md` — predecessor S4 STATE-SYNC.
- `sessions/2026-05-14-s3-build-diagnose-v4-26-0-import-drift.md` — S3 BUILD-DIAGNOSE (#19122) inventoried the upstream cascade.
- `sessions/2026-05-13-s3-prep-phantom-mathlib-audit.md` — S3 PREP (#18711) audited the phantom, source of candidate catalog content for §3.2.
- `sessions/2026-05-13-s3-prep-2-volume-bridge-verification.md` — S3 PREP-2 (#18845) verified `Measure.prod_restrict` is the existing canonical form.
- `sessions/2026-05-13-s3-act-volume-bridge-discharge.md` — S3 ACT (#18944) applied the bridge at line 101-102.
- Mechanic PR #19130 — 8-LOC import barrel swap across 7 slug families.
- Mechanic PR #19218 — parent file 4-error repair, including the SAME bridge pattern at parent:192, Docker-clean 3058/3058 jobs.
- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:101-102` — the bridge.
- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean:192` — parent's identical bridge (independently validated).
