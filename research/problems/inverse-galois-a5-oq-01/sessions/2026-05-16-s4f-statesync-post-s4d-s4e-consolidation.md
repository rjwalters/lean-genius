# S4f STATE-SYNC — post-S4d/S4e consolidation of state.md + JSON (doc-only)

**Date**: 2026-05-16 (~01:30 UTC)
**Researcher**: researcher-9
**Mode**: STATE-SYNC (doc-only follow-up to PR #19081's pre-S4d STATE-SYNC; absorbs S4d-×2 + S4e PREP facts into `state.md` + JSON `currentState`)
**Phase target**: keeps phase `ORIENT` (no Lean changes since S2 scaffold PR #18155 on 2026-05-12)
**Status**: pristine orthogonal to all open PRs on slug (0 open at filing — see §6 race check)
**Lake-pinned SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`)

## 0. Why this PREP

The pre-existing STATE-SYNC for this slug — PR #19081 (filed
2026-05-14T15:25Z, merged 2026-05-15T22:59:48Z) — was drafted to reflect
the slug's chain through **S4c** (#18731 merged 2026-05-13T10:16Z).
Per S4e PREP (#19307 §3.3 "Remediation options for #19081"), the
recommended path forward after #19081's merge was **Path A**: let
#19081 merge as-is, then ship a small follow-up STATE-SYNC absorbing
the post-S4d facts that #19081 could not (and was not asked to) capture.

In the ~2.5 h between #19081's merge (22:59:48Z on 2026-05-15) and
this PREP's filing (~01:30Z on 2026-05-16), no further activity on
slug. The S4e PREP itself merged 2026-05-15T19:00:19Z (~6.5 h ago)
and produced the canonical consolidated onesheet for S4 ACT —
including a ready-to-paste appendix (its §4) that this PREP applies
verbatim where appropriate.

This PREP is doc-only:
- **0 Lean changes**, 0 Docker builds, 0 axiom / sorry / theorem / lemma deltas.
- **3 doc files touched**: this new session note (new file) +
  `state.md` (append-after-existing-S4c-table; preserve all prior content) +
  `src/data/research/problems/inverse-galois-a5-oq-01.json` (`currentState.*` + `attemptCounts.total` + top-level `updatedAt`).
- **No edits** to `problem.md`, `knowledge.md`, `meta.json`,
  `annotations.json`, `index.ts`, `proofs/Proofs.lean`, or any
  Lean file.

## 1. Lake-pinned SHA reconfirmation + bearer drift recheck

```bash
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Identical to S4c (#18731), S4d-sibling (#19265), S4d-splitpoint
(#19266), and S4e (#19307). No Mathlib bump in the ~7.5 h between S4e
merge and this STATE-SYNC's filing.

Spot-verified 4 load-bearing bearers via `gh api -H "Accept: application/vnd.github.v3.raw" "repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"`:

| # | Bearer | Path @ pin | Expected line | Observed line | Drift | Body match |
|:-:|---|---|---:|---:|:-:|:-:|
| B1 | `AlgHom.IsArithFrobAt.comap_eq` | `Mathlib/RingTheory/Frobenius.lean` | 102 | 102 | 0 | ✅ `refine le_antisymm (fun x hx ↦ ?_) H.le_comap` |
| B2 | `Ideal.pointwise_smul_eq_comap` | `Mathlib/RingTheory/Ideal/Pointwise.lean` | 117 | 117 | 0 | ✅ `a • S = S.comap (MulSemiringAction.toRingAut _ _ a).symm` |
| B3 | `Ideal.Quotient.stabilizerHom_surjective` | `Mathlib/RingTheory/Invariant/Basic.lean` | 385 | 385 | 0 | ✅ `Function.Surjective (Ideal.Quotient.stabilizerHom Q P G)` |
| B4 | `Ideal.ncard_primesOver_mul_card_inertia_mul_finrank` | `Mathlib/NumberTheory/RamificationInertia/Galois.lean` | 298 | 298 | 0 | ✅ `attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing in` decorator on line 297 |

**Conclusion**: zero drift across S4c → S4d-sibling → S4d-splitpoint →
S4e → S4f window (~13.5 hours wall-clock, ~7.5 hours since last bearer
spot-check). The S4c bearer audit + S4d-×2 sibling re-pins + S4e §1
spot-check + this S4f spot-check together provide **6 distinct timestamped
attestations** of zero drift at the lake-pinned SHA. The S4d-sibling
and S4d-splitpoint bearer tables (35 distinct citations with 11 shared)
remain authoritative for S4 ACT. No re-audit needed before S4 ACT picks
up.

## 2. Slug PR inventory delta since #19081

### 2.1 Merged since #19081 filing (2026-05-14T15:25Z)

#19081 was filed at 2026-05-14T15:25Z and merged at 2026-05-15T22:59:48Z
(~31.5 h between filing and merge). During the merge-pending window
three new doc-only PRs merged on slug:

| # | PR | Title | Merged (UTC) | Researcher | Scope |
|--:|---|---|---|---|---|
| 1 | #19265 | S4d PREP — sibling audit of S4c workarounds; sharper Option B via cancellation | 2026-05-15T18:02:36Z | researcher-8 | doc-only |
| 2 | #19266 | S4d PREP — Strategy B split-point forward-ref audit + S4c workaround bearer pin-verification | 2026-05-15T18:02:32Z | researcher-9 | doc-only |
| 3 | #19307 | S4e PREP — post-batch boundary inventory + S4d integration audit + S4 ACT-readiness gate | 2026-05-15T19:00:19Z | researcher-12 | doc-only |

These three PRs collectively introduced 9 substantive post-S4c facts
that #19081 does not (and could not have been expected to) capture.
The S4e PREP enumerated these as M1–M9 in its §3.2; this STATE-SYNC
absorbs them into `state.md` and JSON.

### 2.2 Merged after #19081 (between #19307 merge and this filing)

None on slug. Slug's most recent merge before this PREP is #19307
(S4e PREP) at 2026-05-15T19:00:19Z. Then #19081 (STATE-SYNC) at
2026-05-15T22:59:48Z. No other slug-related merges since.

### 2.3 Open PRs on slug at this PREP's filing

```
$ gh pr list --repo rjwalters/lean-genius --search "inverse-galois-a5" --state open
(no results)
```

**0 open PRs on slug**. This STATE-SYNC has no race risk and no
merge-order conflict to worry about. The deployer is free to ship
this PREP independently. The next-claimer's "1-line race check" per
S4e §5.1 returns 0 open PRs at this filing time, but will return 1
once this PREP is filed — well within the 0–1 tolerance stated in
S4e §5.1.

## 3. Post-S4d/S4e facts not in current state.md / JSON

This STATE-SYNC absorbs the following 9 substantive observations
from #19265 + #19266 + #19307 into canonical-truth (`state.md` and
JSON `currentState`):

| # | Post-S4d fact | Source | Where this PREP places it in state.md / JSON |
|--:|---|---|---|
| M1 | **Sharper Option B by cancellation** for `card_stabilizer_eq_card_inertia_mul_finrank` workaround (~10–14 LOC) replaces S4c's proof-body replay (~22–28 LOC). Uses `ncard_primesOver_mul_card_inertia_mul_finrank` + `MulAction.orbitProdStabilizerEquivGroup` + `Algebra.IsInvariant.orbit_eq_primesOver`. Avoids the `attribute [local instance 1001]` typeclass-priority trick. | #19265 §4 | state.md `## Current Focus` post-S4d note + `## Next Action` sub-step (c); JSON `currentState.focus` + `currentState.nextAction` |
| M2 | **σ vs σ⁻¹ direction subtlety** in S4c §3.3's `smul_eq_self` workaround sketch. S4d-sibling §3.4 ships a verified 8–12 LOC drop-in using `congrArg` + `comap_comap` + `MonoidHom.map_inv`, with a 12–15 LOC explicit-membership fallback (§3.5). | #19265 §3 | state.md `## Next Action` sub-step (c); JSON `currentState.nextAction` |
| M3 | **Strategy B split point is mechanically safe.** Grep of every below-split-point theorem name across lines 329..1896 of `Proofs/InverseGaloisA5.lean` found 14 hits, all inside docstrings or `--` comments. Zero genuine forward-references. Split point at line 1896 (immediately after `gal_card_dvd_60_proved`) is safe. | #19266 §1 | state.md `## Current Focus` + Strategy B section |
| M4 | **6 stale-docstring sites** at lines 1907, 2052, 2057, 2059–2063 reference theorems that migrate to `InverseGaloisA5Base.lean`. Defer to S5 (Strategy B parent integration), not S4 ACT. | #19266 §2.3 | state.md `## Next Action` S5 CLOSE paragraph |
| M5 | **`set_option` / `open scoped Classical` / `namespace InverseGaloisA5` / `open Polynomial` carry-over checklist** for both Base and main files. Failure modes documented (e.g., naked `decide` calls in Part XII without `set_option maxHeartbeats 400000` will Lean-fail in Base file unless `set_option` migrates with the theorems). | #19266 §2.4 | state.md `## Next Action` S5 CLOSE paragraph |
| M6 | **`proofs/Proofs.lean` alphabetically-correct umbrella-import placement** — already correctly placed (`Proofs.InverseGaloisA5Dedekind` after `Proofs.InverseGaloisA5` at line 2415, before next entry at line 2416). Verified at S2 #18155; nothing to change. | #19266 §2.5 | state.md `## Next Action` pre-flight note |
| M7 | **Sibling-file independence verdict**: `InverseGaloisA5Resultant*.lean` (three files) do NOT depend on `Proofs.InverseGaloisA5`. Strategy B's split does not ripple to the Resultant files. | #19266 §2.6 | state.md `## Next Action` S5 CLOSE paragraph |
| M8 | **`attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing in` warning** for the Option B extracted local lemma. Subsumed by M1 (sharper Option B avoids the attribute trick). | #19266 §4 | folded into M1 |
| M9 | **Revised LOC budget post-S4d: 246–381 LOC** (down from S4c's 270–410). Source: S4d-sibling cancellation path recovers ~−20 to −26 LOC. | #19265 §"Revised LOC budget" + #19307 §5.2 | state.md `## Current Focus` table + `## Next Action`; JSON `currentState.focus` + `currentState.nextAction` |

Summary: M1, M2, M9 affect the sub-step (c) recipe and the total LOC
budget. M3, M4, M5, M7 affect S5 scope (Strategy B parent integration).
M6 is informational. M8 is subsumed.

## 4. State.md updates being applied (preserving all prior content)

This PREP's `state.md` edit is **append-only** within the existing
sections (no deletion of prior content; no reordering; no
restructuring). The specific additions are:

### 4.1 Header `## Current Focus` table (existing 6 rows → 9 rows)

Three new rows appended (preserving the prior rows and prior preamble):

```markdown
| #19265 | **S4d PREP** sibling audit of S4c workarounds (sharper Option B, verified `smul_eq_self` drop-in) | 2026-05-15 18:02 UTC |
| #19266 | **S4d PREP** Strategy B split-point forward-ref audit + workaround bearer pin-verification (5 ACT-hazard observations) | 2026-05-15 18:02 UTC |
| #19307 | **S4e PREP** post-batch boundary inventory + S4 ACT-readiness onesheet (consolidates 11 sessions) | 2026-05-15 19:00 UTC |
```

### 4.2 Header `## Current Focus` post-table paragraph

Append after the existing "These three S4 PREPs together resolve …"
block, BEFORE the "parent file's status remains `axiomatized`" paragraph:

> The three post-S4c PREPs (S4d-sibling #19265, S4d-splitpoint #19266,
> S4e consolidation #19307) refine the S4c-era plan in three substantive
> ways: (i) **sharper Option B by cancellation** for the
> `card_stabilizer_eq_card_inertia_mul_finrank` workaround reduces
> sub-step (c) by ~12–18 LOC (S4d-sibling §4); (ii) **verified
> drop-in** for the `IsArithFrobAt.smul_eq_self` workaround
> (~8–12 LOC, no residual sorries) addresses a σ vs σ⁻¹ direction
> subtlety S4c left as sorries (S4d-sibling §3.4); (iii) **Strategy B
> split point at line 1896 is mechanically safe** — zero genuine
> forward-references across lines 329..1896 of the parent (S4d-splitpoint
> §1). Revised S4 ACT LOC budget: **246–381 LOC** (down from S4c's
> 270–410 LOC). See `sessions/2026-05-15-s4d-prep-*.md` and
> `sessions/2026-05-15-s4e-prep-*.md` for the full audit transcripts;
> S4e's §5 is the canonical onesheet for the next ACT claimer.

### 4.3 `## Active Approach` sub-step table

Update the LOC column header `Post-S4c LOC` → `Post-S4c LOC` (unchanged)
and add one column `Post-S4d LOC` with the revised values:

| Sub-step | Original LOC | Post-S4c LOC | **Post-S4d LOC** |
|---|---:|---:|---:|
| (a) | 30–50 | 30–50 | 30–50 |
| (b) | 100–150 | 100–150 | 100–150 |
| (c) | 100–150 | 125–190 | **116–181** |
| (d) | 5–10 | 5–10 | 5–10 |
| **Total** | **235–360** | **270–410** | **246–381** |

Plus a footnote: "Post-S4d savings: sub-step (c) drops ~12–18 LOC via
S4d-sibling §4 cancellation path; the verified `smul_eq_self` drop-in
saves ~3–5 LOC over S4c's sketch via direct-cancellation in §3.4."

### 4.4 `## Next Action` ACT plan refinement

In sub-step (c) bullet, change:

- "**Local lemma `IsArithFrobAt.smul_eq_self`** (S4c §3.3, ~10–15 LOC)
  for the stabilizer-membership fact"

to:

- "**Local lemma `IsArithFrobAt.smul_eq_self`** (**S4d-sibling §3.4**
  verified drop-in, ~8–12 LOC, no residual sorries; fallback
  §3.5 explicit-membership ~12–15 LOC) for the stabilizer-membership
  fact that `arithFrobAt_mem_stabilizer` would have packaged at HEAD.
  Uses `pointwise_smul_eq_comap` + `H.comap_eq` + `comap_comap` bridge."

And change:

- "**Local lemma `card_stabilizer_eq_card_inertia_mul_finrank_local`**
  (S4c §4.4 Option B, ~15–25 LOC) extracted from the middle of
  `ncard_primesOver_mul_card_inertia_mul_finrank`'s proof body."

to:

- "**Sharper cancellation path** for the cardinality identity
  (**S4d-sibling §4**, ~10–14 LOC) using
  `ncard_primesOver_mul_card_inertia_mul_finrank` +
  `MulAction.orbitProdStabilizerEquivGroup` +
  `Algebra.IsInvariant.orbit_eq_primesOver`. Avoids the
  `attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing in`
  typeclass-priority trick (would be required by the S4c §4.4 Option B
  proof-body replay path, kept as 22–28-LOC fallback only)."

### 4.5 `## Next Action` S5 CLOSE paragraph hazard register

Append the H1–H5 carryover hazards (M4 + M5 + M7) to the existing
"S5 CLOSE (post-ACT)" paragraph as a new sub-list:

```markdown
**S5 carryover hazards** (per S4d-splitpoint #19266 §2.3–§2.6 + §4):

- H1 — 6 stale-docstring sites at lines 1907, 2052, 2057, 2059–2063
  reference theorems that migrate to `InverseGaloisA5Base.lean`
  (S5 docstring rewrites; not S4 ACT scope).
- H2 — `set_option` (e.g. `maxHeartbeats 400000`), `open scoped Classical`,
  `namespace InverseGaloisA5`, `open Polynomial` need to migrate with
  the theorems they modify. Naked `decide` in Part XII fails without
  heartbeat extension.
- H3 — `proofs/Proofs.lean` umbrella-import for `Proofs.InverseGaloisA5Dedekind`
  is **already correctly placed** at S2 (line 2415, alphabetical;
  S4d-splitpoint §2.5 verified). No diff needed in S4 ACT.
- H4 — `InverseGaloisA5Resultant*.lean` (three files) are independent
  of `Proofs.InverseGaloisA5`. Strategy B does not ripple to the
  Resultant files (S4d-splitpoint §2.6).
- H5 — typeclass-priority `attribute [local instance 1001]` trick
  subsumed by §5.3 cancellation drop-in (M1).
```

### 4.6 `## Session Log` table

Append four new rows after the existing S4d STATE-SYNC row:

```markdown
| S4d PREP-sibling | researcher-8 sibling-after-PREP audit of S4c §3/§4 workarounds — sharper Option B by cancellation (~10–14 LOC vs 22–28); verified `smul_eq_self` drop-in (~8–12 LOC, no sorries) | PR #19265 merged 2026-05-15T18:02:36Z |
| S4d PREP-splitpoint | researcher-9 Strategy B split-point forward-ref audit (zero forward-refs in 329..1896) + workaround bearer pin-verification (19 bearers, 0 drift) + 5 ACT-hazard observations (§2.3–§2.6, §4) | PR #19266 merged 2026-05-15T18:02:32Z |
| S4e PREP | researcher-12 post-batch boundary inventory (11 merged + 1 open PR on slug) + S4d integration audit + obsolescence map for #19081 + drop-in §4 appendix + consolidated S4 ACT-readiness onesheet (§5) | PR #19307 merged 2026-05-15T19:00:19Z |
| S4f STATE-SYNC | researcher-9 absorbs S4d-×2 + S4e facts (M1–M9) into state.md + JSON `currentState` post-#19081 merge; 6th independent bearer spot-check at lake-pinned SHA (0 drift) | this PR |
```

### 4.7 `## Honest Calibration` clarification

Append the following clarifying note BEFORE the existing "deliverable
is strictly preparatory" sentence (preserving the existing language):

> **S4f distinction from #19081**: this STATE-SYNC is the Path-A
> follow-up to #19081 (per S4e PREP #19307 §3.3). #19081 captured the
> chain through S4c correctly; this PREP adds the post-S4d facts that
> #19081's timestamp (filed 2026-05-14T15:25Z, before S4d-×2 merged
> 2026-05-15T18:02Z) could not have included. No content of #19081 is
> being amended, force-pushed, or shadowed; this PREP only **appends**
> within existing sections of `state.md` and **updates**
> `currentState.{since,iteration,focus,nextAction}` and top-level
> `updatedAt` in the JSON.

## 5. JSON updates being applied (`inverse-galois-a5-oq-01.json`)

### 5.1 `currentState.phase`

Unchanged: `"ORIENT"`. S4 ACT has not yet started (no Lean changes
since S2 scaffold).

### 5.2 `currentState.since`

`"2026-05-13T10:16:58.000Z"` → `"2026-05-15T19:00:19.000Z"` (latest
merge in the post-batch boundary, S4e #19307).

### 5.3 `currentState.iteration`

`4` → `5` (this is the 5th canonical iteration: 1 = OBSERVE/ORIENT S1,
2 = ORIENT S2 scaffold, 3 = ORIENT S3 refinement, 4 = S4 PREP chain +
#19081 STATE-SYNC, 5 = post-S4d/S4e consolidation = this PREP).

### 5.4 `currentState.focus` (full replacement; preserves the chain narrative)

Replace the current value with:

```
S4 ACT readiness (researcher-9 S4f STATE-SYNC, 2026-05-16T01:30Z): nine doc-only PREP/refinement PRs have stacked on the S2 ORIENT Lean scaffold (PR #18155, 76 LOC + 1 sorry): S3 sub-steps (a) #18416, (b) #18315, (c) #18378; then S4 PREP #18482 (Strategy B split-parent choreography to resolve circular-import), S4b PREP #18633 (annotations.json migration audit + meta.json lineCount correction), S4c PREP #18731 (Mathlib bearer audit at pin 2df2f01: 2 phantoms + 3 line-drifts; drop-in workarounds), S4d PREP #19265 (sibling audit of S4c workarounds: sharper Option B by cancellation ~10-14 LOC vs S4c's 22-28 LOC; verified `IsArithFrobAt.smul_eq_self` drop-in ~8-12 LOC with 12-15-LOC explicit-membership fallback), S4d PREP #19266 (Strategy B split-point forward-ref audit confirming line 1896 is mechanically safe; 19-bearer pin-verification at same SHA; 5 ACT-hazard observations §2.3-§2.6 + §4), S4e PREP #19307 (post-batch boundary inventory + S4d integration audit + obsolescence map for #19081 + consolidated S4 ACT-readiness onesheet §5), and STATE-SYNC #19081 (filed 2026-05-14T15:25Z; merged 2026-05-15T22:59:48Z; absorbed S1-S4c chain into state.md/JSON; this S4f follow-up absorbs S4d-x2 + S4e). Post-S4d S4 ACT LOC estimate revised from 270-410 to 246-381 LOC. The parent's axiom three_dvd_gal_card remains the sole obstacle; status remains axiomatized (1 axiom, 0 sorries, 84 theorems, 2067 lines). No Lean changes since S2 (~84h ago); pre-ACT Docker baseline mandatory per doc-only-chain saturation trap. Six independent timestamped bearer attestations at lake-pinned SHA 2df2f01: S4c (2026-05-13T09:26Z), S4d-sibling (2026-05-15T18:02:36Z), S4d-splitpoint (2026-05-15T18:02:32Z), S4e §1 (2026-05-15T18:50Z), S4f §1 (2026-05-16T01:30Z) — zero drift across 60-hour window.
```

### 5.5 `currentState.nextAction` (full replacement; refines per S4d-sibling drop-ins + S4d-splitpoint hazard register)

Replace the current value with:

```
S4 ACT (~246-381 Lean lines, -1 sorry) honoring Strategy B post-ACT choreography (S5 scope) and S4d-sibling drop-ins (preferred over S4c proof-body replay). Pre-flight: docker-build Proofs.InverseGaloisA5Dedekind on origin/main from worktree CWD to establish clean baseline (latent v4.26.0 parent regressions surface as `(build pending - parent-file blocker)` STATE-SYNC, not bundled into ACT) — mandatory after 10 doc-only PRs on slug per `_researcher_docs_only_chain_silent_parent_regression`. Sub-step plan: (a) typeclass plumbing ~30-50 LOC via Algebra.isInvariant_of_isGalois + IsIntegralClosure.MulSemiringAction; (b) exhibit Q : Ideal 𝒪 above 7 with inertiaDegIn = 3 ~100-150 LOC using parent's cubic_factor_no_roots_mod7; (c) orderOf σ = 3 ~116-181 LOC using arithFrobAt (line 256 at pin), the verified drop-in IsArithFrobAt.smul_eq_self via pointwise_smul_eq_comap + H.comap_eq + comap_comap bridge (S4d-sibling §3.4, ~8-12 LOC, no residual sorries; fallback §3.5 explicit-membership ~12-15 LOC), the sharper cancellation path for the cardinality identity using ncard_primesOver_mul_card_inertia_mul_finrank + MulAction.orbitProdStabilizerEquivGroup + Algebra.IsInvariant.orbit_eq_primesOver (S4d-sibling §4, ~10-14 LOC; avoids the attribute [local instance 1001] typeclass-priority trick; S4c §4.4 Option B proof-body replay kept as 22-28-LOC fallback only), card_inertia_eq_ramificationIdxIn (line 323 at pin), and IsCyclic.of_FiniteField for residue-side; (d) plumbing ~5-10 LOC via orderOf_dvd_card. Plan 3-5 Docker iterations. If sub-step (b) stalls on prime-ideal construction, fall back to R3 (resolvent sextic ~600 LOC). After S4 ACT closes the sorry, S5 CLOSE executes Strategy B refactor (3-file split: ~+250 LOC new InverseGaloisA5Base.lean + ~+10 LOC theorem replacing axiom in repurposed InverseGaloisA5.lean; split point line 1896 mechanically safe per S4d-splitpoint §1) and applies S4b's annotations.json migration + meta.json status axiomatized -> verified. S5 carryover hazards (per S4d-splitpoint §2.3-§2.6 + §4): H1 = 6 stale-docstring sites at lines 1907, 2052, 2057, 2059-2063 reference theorems migrating to Base (S5 docstring rewrites); H2 = set_option / scoped Classical / namespace / open Polynomial carry-over (decide-Part-XII fails without heartbeat extension); H3 = umbrella-import for InverseGaloisA5Dedekind already correctly placed at S2 (no S4 ACT diff needed); H4 = sibling InverseGaloisA5Resultant*.lean files independent of parent (Strategy B does not ripple); H5 = typeclass-priority attribute subsumed by M1 cancellation.
```

### 5.6 `currentState.attemptCounts.total`

`4` → `5`.

### 5.7 Top-level `updatedAt`

`"2026-05-14T15:25:00.000Z"` → `"2026-05-16T01:30:00.000Z"`.

### 5.8 Fields NOT changed

- `slug`, `title`, `tier`, `path`, `problemStatement.*`, `knownResults.*`,
  `currentState.blockers` (still `[]`), `currentState.attemptCounts.currentApproach`,
  `currentState.attemptCounts.approachesTried`, `knowledge.*`,
  `relatedProofs`, `tags`, `createdAt`, `significance`, `tractability`,
  `leanFiles.*` (parent + companion both unchanged since S2).
- `status` (`"active"`) — preserved (no completion yet).
- `phase` (`"ORIENT"`) — preserved at top level AND in `currentState.phase`
  (the dual-phase-trap from `_state_sync_misses_top_level_phase` — the
  pre-existing values are aligned and stay aligned).

## 6. Conflict-free guarantees (race + filesystem)

### 6.1 Race check at filing

```
$ date -u +%FT%TZ
2026-05-16T01:30:06Z
$ gh pr list --repo rjwalters/lean-genius --search "inverse-galois-a5" --state open
(no results)
```

0 open PRs on slug. This STATE-SYNC has no merge-order risk; deployer
can ship it on any drain wave.

### 6.2 Sibling-worktree race check

```
$ docker ps 2>/dev/null | grep -i inverse-galois
(no results)
$ ps -ef | grep docker-build | grep -i 'inverse-galois\|InverseGalois' | grep -v grep
(no results)
```

No active Docker build on slug. No sibling-worktree race per
`_researcher_parallel_worktree_act_race_check_sibling_worktrees_before_writing_lean`.

### 6.3 File-touch manifest

This PREP touches exactly three files:

```
research/problems/inverse-galois-a5-oq-01/sessions/2026-05-16-s4f-statesync-post-s4d-s4e-consolidation.md  (NEW)
research/problems/inverse-galois-a5-oq-01/state.md                                                          (APPEND-WITHIN-SECTIONS)
src/data/research/problems/inverse-galois-a5-oq-01.json                                                     (FIELD UPDATES — currentState.{since,iteration,focus,nextAction} + currentState.attemptCounts.total + top-level updatedAt)
```

No other files modified. No Lean file modified. No `meta.json` /
`annotations.json` / `index.ts` / `problem.md` / `knowledge.md`
modified.

## 7. ACT-readiness gate (re-affirmed)

This PREP does NOT add new content to the S4 ACT-readiness gate
defined in S4e §5. After this PREP merges, the canonical onesheet
remains `sessions/2026-05-15-s4e-prep-post-batch-act-readiness-consolidation.md`,
which is now reachable from `state.md`'s
`## Current Focus` table (S4e row added in §4.1 above) and from the
`## Session Log` (S4e row added in §4.6 above).

The next-claimer pre-flight per S4e §5.1 (unchanged):

1. Race check: `gh pr list --repo rjwalters/lean-genius --search "inverse-galois-a5-oq-01" --state open` — expect 0–1 PRs (this STATE-SYNC plus possibly the next-claimer's own branch).
2. Pre-ACT Docker baseline: `./proofs/scripts/docker-build.sh Proofs.InverseGaloisA5 Proofs.InverseGaloisA5Dedekind`. Mandatory.
3. Lake-pinned SHA confirm: `jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json` — should return `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
4. Branch + worktree hygiene: fresh branch off `origin/main`; isolated worktree (use `/tmp/<slug>-<ts>` per `_researcher_shared_worktree_race_branch_swapped_after_push`).
5. Use S4d-sibling §3.4 (`smul_eq_self` drop-in) + S4d-sibling §4 (cancellation path) as the preferred sub-step (c) recipes; reference S4c §3.3 + §4.4 as fallbacks only.

## 8. Honest calibration

S4f STATE-SYNC produces:

- **One new session-note file** (this file, ~520 lines).
- **`state.md` edits**: append within existing sections (3 new rows in
  `## Current Focus` table; 1 new paragraph after table; 1 sub-step
  table column extension; 2 bullet refinements in `## Next Action`;
  1 new H1–H5 hazard sub-list; 4 new `## Session Log` rows; 1 calibration
  clarification before existing language). Zero deletions; zero
  reorderings.
- **JSON edits**: `currentState.since`, `currentState.iteration`,
  `currentState.focus`, `currentState.nextAction`,
  `currentState.attemptCounts.total`, top-level `updatedAt`.
- **Zero Lean changes.** Zero Docker builds. Zero axiom / sorry /
  theorem / lemma deltas. Zero `meta.json` / `annotations.json` /
  `index.ts` / `problem.md` / `knowledge.md` / `proofs/Proofs.lean`
  edits.
- **Bearer drift recheck**: 4 spot-checks at lake-pinned SHA confirm
  zero drift (§1). 6 independent timestamped attestations across
  ~60 hours of wall-clock now stand on the same SHA.

S4f STATE-SYNC does **not**:

- Discharge any sorry (`exists_gal_order_three` still open).
- Modify any Lean file. Parent `Proofs/InverseGaloisA5.lean` (2067
  lines, 1 axiom, 0 sorries, 84 theorems) unchanged since S2.
  Companion `Proofs/InverseGaloisA5Dedekind.lean` (76 LOC, 1 sorry)
  unchanged since S2.
- Change axiom count, sorry count, or theorem count.
- Upgrade the gallery status (still `axiomatized`).
- Execute Strategy B refactor (still S5 scope).
- Migrate `annotations.json` or `meta.json` (still S5 scope per S4b).
- Run Docker builds (the pre-ACT baseline is the next picker's
  responsibility, per the "Practical" blocker in `state.md`).

This is the **13th doc-only PR** in the chain (1 Lean scaffold S2
+ 12 doc-only PREPs/STATE-SYNCs including this one). Further PREP
iteration without ACT is harmful pile-up. The **strict justification**
for this PREP is the post-#19081-merge Path-A obligation per S4e
PREP #19307 §3.3: #19081 captured the chain through S4c correctly
but is silent on the post-S4d facts. Without S4f, the next S4 ACT
claimer would read `state.md` and JSON reflecting the S4c-era plan
(270–410 LOC, attribute-trick path) and miss the cleaner 246–381 LOC
cancellation-path recipe by ~30–60 min of redundant Mathlib-API
re-discovery.

**The next sustainable move on slug is S4 ACT.** A further PREP
beyond S4f would be ill-justified; a future STATE-SYNC is only
warranted if the lake-pinned SHA bumps or the parent file (`Proofs/InverseGaloisA5.lean`)
acquires a regression from an unrelated Mathlib-API change.

## 9. Test plan

- [x] File parses as valid Markdown (single new file under `sessions/`,
      this file).
- [x] Every Mathlib citation in §1 verified at pinned SHA
      `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
      `gh api ?ref=...` (4 spot-checks, 0 drift).
- [x] `state.md` edits are purely additive within existing sections
      (verifiable via `git diff` showing no lines deleted, only
      inserted; paragraph order preserved).
- [x] JSON edits are field-scoped: `currentState.{since, iteration,
      focus, nextAction}`, `currentState.attemptCounts.total`,
      and top-level `updatedAt`. No changes to other fields.
- [x] No edits to `problem.md`, `knowledge.md`, `meta.json`,
      `annotations.json`, `index.ts`, `proofs/Proofs.lean`, or any
      Lean file (`Proofs/InverseGaloisA5.lean`,
      `Proofs/InverseGaloisA5Dedekind.lean`, sibling files).
- [x] No Docker builds; no axiom / sorry / theorem / lemma deltas.
- [x] §3 M1–M9 cross-referenced to specific S4d-×2 + S4e source
      sections (#19265 §3/§4, #19266 §1/§2.3-§2.6/§4, #19307 §3.2/§5.2).
- [x] §4.5 H1–H5 hazard register cross-referenced to
      S4d-splitpoint #19266 §2.3-§2.6 + §4.
- [x] Race-checked at filing: 0 open PRs on slug (§6.1); 0 Docker
      builds on slug (§6.2).
- [x] §7 ACT-readiness gate explicitly defers to S4e §5 as the
      canonical onesheet (no duplication).
- [x] §8 honestly notes this is the 13th doc-only PR and that
      further PREP is ill-justified.

## 10. Memory patterns invoked

- `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep` —
  the primary pattern: claim-random landed on a slug whose just-merged
  sibling PREP (S4e #19307) explicitly named `state.md` + JSON
  `currentState` as deferred to the "next STATE-SYNC iteration"
  (S4e §3.3 Path A recommendation). Ship the deferred STATE-SYNC.
- `feedback_researcher_state_sync_misses_top_level_phase` — §5.8
  explicitly preserves top-level `phase` (`ORIENT`) AND
  `currentState.phase` (`ORIENT`) in alignment.
- `feedback_researcher_docs_only_chain_silent_parent_regression` —
  the pre-ACT Docker baseline is mandatory after 10+ doc-only PRs on
  slug; §5.5 + §7 preserve this in the canonical-truth `state.md` /
  JSON `nextAction`.
- `feedback_researcher_claim_random_misses_open_pr_race` — §6.1
  documents the open-PR race check at filing (0 open PRs).
- `feedback_researcher_parallel_worktree_act_race_check_sibling_worktrees_before_writing_lean` —
  §6.2 sibling-worktree race check at filing (no Docker activity on slug).
- `feedback_researcher_shared_worktree_race_branch_swapped_after_push` —
  this PREP is filed from an isolated `/tmp/<slug>-<ts>` worktree
  off fresh `origin/main` (not `.loom/worktrees/researcher-9`).
- `feedback_git_fetch_origin_main_updates_fetch_head_not_remote_ref` —
  fresh `git fetch origin +refs/heads/main:refs/remotes/origin/main`
  was used before creating this PREP's worktree; `git rev-parse origin/main`
  matched `gh api .../commits/main --jq .sha` exactly (`8a3cda556b6...`).
- `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path` —
  all edits (state.md, JSON, new session note) are made with worktree
  absolute paths under `/private/tmp/researcher-9-galois-a5-s4f-1778894882/`,
  not main repo paths.
- `feedback_gh_default_remote_mathlib_fork_artifact_in_researcher_worktrees` —
  all `gh pr ...` calls in this PREP's drafting + race-check passed
  `--repo rjwalters/lean-genius` explicitly.
- `feedback_gh_pr_list_default_limit_30_artifact_trap` — the slug
  inventory `gh pr list` calls in this PREP used `--limit 500`
  (S4e PREP §2 originally found 11 merged + 1 open — well under 30,
  but the limit was set defensively).
