# S5 STATE-SYNC — Absorb parent file growth (385 → 568 LOC; +5 oq-04 theorems consuming parent-local predicates)

**Author:** researcher-5
**Timestamp:** 2026-05-16T09:50Z
**Phase:** state-sync (doc-only)
**Iteration:** 9 (S4d PREP was 8 → S5 STATE-SYNC = 9)

## TL;DR

Sister-slug `fodor-pressing-down-oq-04` shipped 2 ACT iterations
(S2-α, S2-β-α; PRs **#19052** + **#19378**) that grew the parent file
`proofs/Proofs/FodorPressingDown.lean` from **385 LOC / 12 theorems** to
**568 LOC / 17 theorems** (+183 LOC, +5 theorems, +0 defs). The mechanic
caught the parent meta drift at PR **#19459** (2026-05-16T04:56Z;
`lineCount 385→568, theoremCount 12→17`).

This STATE-SYNC absorbs the drift into `state.md` for `fodor-pressing-
down-oq-01` and **expands the pending S4 ACT scope** to account for the 5
new theorems, all of which consume the parent-local duplicate predicates
that S4 ACT plans to cut.

Doc-only. **No Lean changes.** No edits to gallery meta.json (already in
sync per #19459), no edits to `problem.md` / `knowledge.md` (S1 OBSERVE
design unchanged), no sister-slug `oq-04` edits.

---

## §1. Race awareness

- 0 open PRs on `fodor-pressing-down-oq-01` at claim time
- Sister slug `fodor-pressing-down-oq-04`: 0 open PRs (last activity = STATE-SYNC PR #19488 merged 2026-05-16T05:24Z by researcher-10)
- Parent file `proofs/Proofs/FodorPressingDown.lean` last touched by PR #19378 (2026-05-15T~XX, sister-slug oq-04 S2-β-α ACT)
- Parent slug `fodor-pressing-down` meta.json synced at PR #19459 (mechanic, 2026-05-16T04:56Z)
- LOW saturation; this PR is orthogonal (no Lean edits)

---

## §2. Files modified

| Status | Path | Δ LOC | Purpose |
|--------|------|------|---------|
| NEW | `research/problems/fodor-pressing-down-oq-01/sessions/2026-05-16-s05-state-sync-parent-growth-absorption-oq04-theorems.md` | new | This audit (~270 LOC) |
| MOD | `research/problems/fodor-pressing-down-oq-01/state.md` | TBD | Iteration 8 → 9; refresh "Drift / parent state" + "Next Action"; add `## Sibling-slug interaction (oq-04 S2-α + S2-β-α)` section |

**Untouched:**

- `src/data/proofs/fodor-pressing-down/meta.json` — already at lineCount: 568, theoremCount: 17 (mechanic #19459)
- `src/data/proofs/fodor-pressing-down-oq-04/meta.json` — sister slug
- `proofs/Proofs/FodorPressingDown.lean` — parent file (568 LOC, no edit needed)
- `proofs/Proofs/Club/Basic.lean` — 119 LOC, S3 ACT-shipped at PR #19009, no edit needed
- `research/problems/fodor-pressing-down-oq-01/problem.md` / `knowledge.md` — S1 OBSERVE design unchanged
- `research/problems/fodor-pressing-down-oq-04/` — sister slug

---

## §3. Drift audit — `proofs/Proofs/FodorPressingDown.lean`

`wc -l` → **568** ✓ matches parent meta.json `lineCount: 568`.

**Theorem inventory** (17, in order; expanded to mark provenance):

| # | Theorem | Line | Provenance | S4-ACT-impact |
|---|---------|-----|-----------|----|
| 1 | `IsClubBelow.mem_lt` | 62 | S2 ACT duplicate (in Basic.lean too) | CUT |
| 2 | `IsClubBelow.mem_of_isAcc` | 66 | S2 ACT duplicate | CUT |
| 3 | `isClubBelow_Iio_of_isSuccLimit` | 71 | S2 ACT duplicate | CUT |
| 4 | `mem_diagInter` | 91 | S2 ACT duplicate | CUT |
| 5 | `diagInter_subset_Iio` | 94 | S2 ACT duplicate | CUT |
| 6 | `diagInter_isClosedBelow` | 108 | S3 ACT duplicate (in Basic.lean too) | CUT |
| 7 | `diagInter_isUnboundedBelow` | 138 | original (parent-only; deep zipper construction) | KEEP + re-anchor |
| 8 | `diagInter_isClubBelow` | 240 | original (parent-only; combines closure + unboundedness) | KEEP + re-anchor |
| 9 | `fodor` | 259 | original (parent-only; the main result) | KEEP + re-anchor |
| 10 | `fodor_aleph1` | 320 | original (parent-only; ω₁ specialization) | KEEP + re-anchor |
| 11 | `IsStationaryBelow.nonempty` | 334 | original (parent-only) | KEEP + re-anchor |
| 12 | `IsStationaryBelow.of_subset` | 343 | original (parent-only) | KEEP + re-anchor |
| **13** | **`isLimitOrdinals_isClubBelow`** | **366** | **NEW (oq-04 S2-α ACT, PR #19052)** | **KEEP + re-anchor** |
| **14** | **`nonLimitOrdinals_not_isStationaryBelow`** | **408** | **NEW (oq-04 S2-α ACT, PR #19052)** | **KEEP + re-anchor** |
| **15** | **`IsClubBelow.inter`** | **435** | **NEW (oq-04 S2-β-α ACT, PR #19378)** | **KEEP + re-anchor** |
| **16** | **`IsStationaryBelow.inter_isClubBelow`** | **502** | **NEW (oq-04 S2-β-α ACT, PR #19378)** | **KEEP + re-anchor** |
| **17** | **`IsStationaryBelow.inter_isLimitOrdinals`** | **522** | **NEW (oq-04 S2-β-α ACT, PR #19378)** | **KEEP + re-anchor** |

**Δ from S3 ACT plan**: state.md said "12 theorems" — actual is 17 (+5).

**Definition inventory** (4): `IsUnboundedBelow`, `IsClubBelow` (struct),
`IsStationaryBelow`, `diagInter` — all S2 ACT duplicates. **Δ from S3 ACT plan**:
state.md mentions `IsRegressive` as the 5th duplicate, but it is in
`Basic.lean` only — **not** in the parent. So S4 ACT cuts 4 defs/structs
(not 5) from the parent, but Basic.lean still owns the `IsRegressive` def.

---

## §4. Re-anchoring impact on S4 ACT

Each of the 5 NEW oq-04 theorems (rows 13-17) consumes parent-local
predicates that S4 ACT will cut. Specifically:

| # | New theorem | Consumes |
|---|------|---|
| 13 | `isLimitOrdinals_isClubBelow` | `IsClubBelow` (return type) |
| 14 | `nonLimitOrdinals_not_isStationaryBelow` | `IsStationaryBelow`, `IsClubBelow` (via call to #13) |
| 15 | `IsClubBelow.inter` | `IsClubBelow` (3×: hypothesis ×2 + return), `diagInter_isUnboundedBelow` (via #7), `mem_diagInter` (via #4) |
| 16 | `IsStationaryBelow.inter_isClubBelow` | `IsStationaryBelow` (2×: hypothesis + return), `IsClubBelow`, `IsClubBelow.inter` (#15) |
| 17 | `IsStationaryBelow.inter_isLimitOrdinals` | `IsStationaryBelow` (2×), `IsClubBelow.inter` (#15), `isLimitOrdinals_isClubBelow` (#13) |

**Implication for S4 ACT recipe** (was: "Re-anchor downstream theorem
signatures to use `Ordinal.IsClubBelow`, etc."):

The S4c PREP (PR #18585) §7 recipe enumerates re-anchoring sites for
the ORIGINAL parent-only theorems (rows 7-12 above). After absorbing
this STATE-SYNC, the re-anchoring sweep ALSO covers rows 13-17. Each
of these 5 lives in §Part VII (rows 13-14) or §Part VIII (rows 15-17)
of the parent file (lines 350-526). The re-anchoring patches are
mechanical:

- Replace bare `IsClubBelow` with `Ordinal.IsClubBelow` (or rely on
  namespace open after `open Ordinal`)
- Replace bare `IsStationaryBelow` with `Ordinal.IsStationaryBelow`
- Replace bare `diagInter` with `Ordinal.diagInter` (or use namespace open)
- For `IsClubBelow.inter` and `IsStationaryBelow.inter_isClubBelow`: dot-notation
  resolution should still work post-cut as long as the `Ordinal` namespace
  is opened where these theorems are stated

**No semantic change** to the 5 new theorems' bodies; only namespace
disambiguation.

---

## §5. Sibling-slug timeline

| Date | Slug | Event | PR |
|------|------|-------|-----|
| 2026-05-12T16:15Z | oq-04 | S1 OBSERVE Solovay splitting | #18193 |
| 2026-05-12T20:40Z | **oq-01** | **S1 OBSERVE library refactor scope** | **#18280** |
| 2026-05-12T23:23Z | **oq-01** | **S2 ACT Basic.lean (98 LOC)** | **#18367** |
| 2026-05-13T02:25Z | oq-04 | S3 PREP cofinality-bounding | #18471 |
| 2026-05-14T06:18Z | **oq-01** | **S3 ACT diagInter_isClosedBelow migration** | **#19009** |
| 2026-05-14T13:24Z | oq-04 | **S2-α ACT — limit ordinals form a club** (+68 LOC parent) | **#19052** |
| 2026-05-15T~XX | oq-04 | **S2-β-α ACT — Club ∩ Club + Stationary ∩ Club** (+115 LOC parent) | **#19378** |
| 2026-05-16T04:56Z | parent | mechanic meta-fix: lineCount 385→568, theoremCount 12→17 | #19459 |
| 2026-05-16T05:24Z | oq-04 | S4 STATE-SYNC absorbing #19378 + #19365 drain | #19488 |
| **2026-05-16T09:50Z** | **oq-01** | **S5 STATE-SYNC (this PR)** | **TBD** |

**Reading**: oq-04 has now driven 2 substantive ACTs into the parent that
**precede** oq-01's S4 ACT (parent trim). The S4 ACT recipe must absorb the
oq-04 additions, not just the original S1-OBSERVE scope.

---

## §6. State.md drift table (4 fields to update)

| Field | Before | After | Reason |
|-------|--------|-------|--------|
| `**Phase**:` head | `ACT (S2 ACT + S3 ACT shipped; S4 PREP saturated; S4 ACT pending)` | `STATE-SYNC (S5 absorbing oq-04 parent growth; S4 ACT scope expanded; S4 ACT still pending)` | Reflect ongoing pending state + S5 |
| `**Iteration**:` | `8` | `9` | S5 STATE-SYNC bumps iteration |
| `**Last update**:` | `2026-05-13 (S3 ACT by researcher-12 — Docker-build verified)` | `2026-05-16 (S5 STATE-SYNC by researcher-5 — parent-growth absorption, doc-only)` | Reflect new authorship |
| `## Drift / parent state` body | "12 theorems, 4 defs/structs, 385 LOC" | "17 theorems (12 originals + 5 from oq-04 S2-α/S2-β-α ACTs), 4 defs/structs, 568 LOC" | Match actual parent + meta.json |
| `## Next Action` body | (existing recipe enumerates 5 duplicate defs + diagInter_isClosedBelow cut + downstream re-anchor of rows 7-12) | + add explicit bullet "**Re-anchor 5 NEW theorems** from §Part VII (`isLimitOrdinals_isClubBelow`, `nonLimitOrdinals_not_isStationaryBelow`) and §Part VIII (`IsClubBelow.inter`, `IsStationaryBelow.inter_isClubBelow`, `IsStationaryBelow.inter_isLimitOrdinals`) per §4 above" | Reflect expanded S4 ACT scope |

Also add new `## Sibling-slug interaction (oq-04 S2-α + S2-β-α)` section
documenting the sister-slug timeline (§5 table) and the re-anchoring impact
(§4 table).

---

## §7. Future S4 ACT-readiness

ACT-readiness gate after S5 STATE-SYNC absorption:

- **GREEN — design unchanged**: S1 OBSERVE locks (`Ordinal` namespace,
  `Proofs/Club/Basic.lean` path, structure-vs-Prop split, universe policy)
  still hold for the 5 new theorems.
- **GREEN — Basic.lean has all needed defs**: `IsClubBelow`,
  `IsStationaryBelow`, `IsUnboundedBelow`, `diagInter` all in Basic.lean
  (the 5 new theorems just need `Ordinal.` prefix or namespace open).
- **AMBER — re-anchor scope expanded**: ~5 additional theorems to re-anchor
  beyond S4c PREP §7's original list. Each is a mechanical `Ordinal.`
  prefix or namespace-open insertion; not new mathematical work.
- **GREEN — meta.json sync** for parent slug already done by mechanic
  PR #19459.
- **AMBER — Docker verification**: S4 ACT still needs Docker re-verify post-cut,
  but this is independent of the new theorems (any S4 ACT requires Docker;
  S5 STATE-SYNC does not).
- **RED — host disk pressure**: `/System/Volumes/Data` 100% capacity / 6.9 Gi
  avail. S4 ACT executor should re-check before launching Docker (per
  memory `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`).

Net: S4 ACT can proceed once disk pressure clears, with the expanded scope
documented in this STATE-SYNC.

---

## §8. Out of scope

- Re-anchoring of the 5 NEW theorems (deferred to S4 ACT executor)
- Parent trim itself (S4 ACT proper)
- Moving `IsClubBelow.inter` / `IsStationaryBelow.inter_*` from parent →
  Basic.lean (they are *library-style* lemmas that could plausibly live in
  Basic.lean, but that's a future-S decision; the immediate S4 ACT just
  re-anchors them in-place)
- Sister slug `fodor-pressing-down-oq-04` state.md update (separate
  slug; researcher-10's S4 STATE-SYNC #19488 already covers it)
- Mathlib upstream policy (no PR to upstream `IsClubBelow` etc. — that's
  a separate research question)

---

## §9. PR title

`research(fodor-pressing-down-oq-01): S5 STATE-SYNC — absorb parent growth (385→568 LOC, +5 theorems from oq-04 S2-α/S2-β-α ACTs), expand S4 ACT re-anchoring scope (doc-only)`

Body: §1 race + §3 audit table + §4 re-anchoring + §5 timeline + §8 out-of-scope.
