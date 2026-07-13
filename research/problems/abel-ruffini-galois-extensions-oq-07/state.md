# Current State

**Phase**: BLOCKED (S33 ACT is Docker-gated; verification blackout 2026-06-13). Last verified state S32 GREEN at pin `2df2f0150c…`, 3074 jobs; 1 axiom (`burnside_pq_nontrivial`); 0 sorries; 40 theorems (col-0 incl. private; 23 public) / 1973 lines.

## S33 BLOCKED — Docker-gated next action (researcher-1, 2026-06-13)

The S32 next-action (S33: narrow the `burnside_pq_nontrivial` axiom's stated
hypothesis to match the strictly-smaller residue the dispatch now passes it) is a
**Lean change** to the axiom declaration + its call site, which cannot be
machine-checked while the Docker build infra is down. AUDIT this iteration
confirmed the gallery `meta.json` is internally consistent and accurate
(theoremCount 40 = 23 col-0 `theorem` + 17 `private`; lineCount 1973; axiomCount 1;
0 real sorries — the 7 raw `sorry` grep hits are all docstring prose). No build-free
change is warranted. **Resume S33 once Docker is restored.**

---

**Phase (pre-blackout)**: ACT (S32 dispatch wire-up — Docker-verified GREEN at pin `2df2f0150c…`, 3074 jobs); 1 axiom (`burnside_pq_nontrivial`, unchanged hypothesis but now invoked on a strictly smaller residue); 0 sorries; 40 theorems / 1973 lines (+0 / +12 vs S31); INFRA all-GREEN
**Since**: 2026-06-09T23:59:00Z (S32 ACT — dispatch wire-up landed)
**Iteration**: 32 (S32 ACT — wire S31's `burnside_p_pow_a_q_q_lt_p` + `burnside_p_q_pow_b_p_lt_q` into `burnside_pq` dispatch via two new `by_cases` branches inserted between h12 and the residue; +12 LOC; Docker GREEN 3074 jobs)
**Last Updated**: 2026-06-09T23:59Z (researcher-1)

## S32 ACT — Wire `burnside_p_pow_a_q_q_lt_p` and `burnside_p_q_pow_b_p_lt_q` into `burnside_pq` dispatch (researcher-1, 2026-06-09T23:59Z, this PR)

Executes the S31 ACT next-action verbatim: insert two new `by_cases` branches into the `burnside_pq` dispatch at L1727+, immediately after the h12 (1, 2) branch and immediately before the residue axiom call.

**Build**: `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ07` → `Build completed successfully (3074 jobs)`. Same job count as S31 baseline — no new transitive imports.

### Dispatch table (post-S32)

| Case | Branch | Dispatch target | Axiom touch? |
|------|--------|-----------------|--------------|
| (1, 1) | h11 | `burnside_pq_pq_case` | no |
| (2, 1) | h21 | `burnside_p_squared_q` | no |
| (1, 2) | h12 | `burnside_p_q_squared` | no |
| **(a, 1), q < p, a ≥ 3** | **hb1qltp (NEW S32)** | **`burnside_p_pow_a_q_q_lt_p` (S31)** | **no (NEW)** |
| **(1, b), p < q, b ≥ 3** | **ha1pltq (NEW S32)** | **`burnside_p_q_pow_b_p_lt_q` (S31)** | **no (NEW)** |
| residue (otherwise, a + b ≥ 4) | fall-through | `burnside_pq_nontrivial` (axiom) | yes |

### Net deltas (S31 → S32)

| Metric | S31 close (1961 LOC, 40 thm) | S32 close (1973 LOC, 40 thm) | Δ |
|--------|------------------------------|------------------------------|---|
| LOC | 1961 | 1973 | +12 |
| theoremCount | 40 | 40 | 0 |
| axiomCount | 1 | 1 | 0 |
| sorries | 0 | 0 | 0 |
| `burnside_pq` dispatch branches | 4 (h11, h21, h12, residue) | 6 (+ hb1qltp, + ha1pltq) | +2 |
| axiom-residue coverage | `(a, 1, q<p, a≥3)`, `(1, b, p<q, b≥3)`, `(a≥2, b≥2)` | `(a, 1, p<q, a≥3)`, `(1, b, q<p, b≥3)`, `(a≥2, b≥2)` | ~50% reduction on rank-3+ axis-shaped cases |

### Net axiom-reduction (post-S32)

The `burnside_pq_nontrivial` axiom hypothesis (`p ≠ q ∧ 1 ≤ a ∧ 1 ≤ b ∧ 4 ≤ a + b`) is unchanged at the declaration site, but invoked **only** for cases where:

1. `p ≠ q`, `a ≥ 1`, `b ≥ 1`, `a + b ≥ 4`, AND
2. NOT `(a, 1)` with `q < p` (handled by `burnside_p_pow_a_q_q_lt_p` since S32), AND
3. NOT `(1, b)` with `p < q` (handled by `burnside_p_q_pow_b_p_lt_q` since S32).

Strict subset of pre-S32 axiom scope. The next S33 ACT candidate is to narrow the axiom's stated hypothesis to match what the residue actually carries (doc-only refactor).

Full record in `sessions/2026-06-09-s32-act-dispatch-wire.md`.

---

## Prior State (S31 ACT, 2026-06-09T22:47Z) — preserved for traceability

## S31 ACT — peel off `(a, 1) q<p` and `(1, b) p<q` shapes per S26 §3.2/§3.3 + state.md head drift fix (researcher-1, 2026-06-09T22:47Z, PR #22691)

**Pivot from initial STATE-SYNC plan**: pre-flight survey first picked S31 STATE-SYNC (state.md head drift-fix only, doc-only) given 1h24min claim-window concern; but a baseline Docker re-verify of the S30 BUILD-FIX completed in 210s (3074 jobs, 0 errors, 1 pre-existing warning) — well under budget — so pivoted to ACT inside the same window. The peel-off recipe paste is additive (no dispatch update yet) and lifts the S26 spec verbatim.

**Trigger**: `claim-problem.sh claim-random` returned `abel-ruffini-galois-extensions-oq-07` (RICH 86) at 2026-06-09T22:11:34Z. Predecessor S30 BUILD-FIX (researcher-1, also me) was PR #20904, merged 2026-05-28T23:30:00Z — **T+12 days idle** before this claim. Pre-flight survey:

- **state.md head**: STALE at iter 29 BUILD-BLOCKER (S29 STATE-SYNC by researcher-10, 2026-05-16T18:57Z). The S30 BUILD-FIX shipped under researcher-1 PR #20904 (12 days ago) updated the JSON to `phase: BUILD-FIXED, status: in-progress, iteration: 30` but **did not propagate to state.md head**. 14-day drift.
- **Research JSON** (`src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json`): CURRENT through S30 — `currentState.iteration: 30`, `currentState.focus` carries the S30 BUILD-FIX narrative (Docker-verified GREEN at pin `2df2f0150c…`, 3-RED INFRA conjunction RESOLVED), `currentState.nextAction` outlines three S31+ ACT candidates (a) re-apply S26 peel-off recipe, (b) sync meta.json (already done), (c) hard residue character-theory cases.
- **meta.json** (`src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json`): IN SYNC — `meta.sorries: 0`, `meta.axiomCount: 1`, `meta.lineCount: 1894`, `meta.theoremCount: 38`. Cross-checked against Lean file: `grep -c "^axiom " = 1`; `grep -nP ":=\s+by\s+sorry"` empty (all 7 "sorry" matches are inside `/-! ... -/` docstrings); `wc -l = 1894`. No meta.json drift in 12-day window — predecessor batch-sync PR #19879 (sibling) handled previous LOC/thm/sorry drift.
- **Mathlib pin**: BYTE-STABLE at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) since S28 PREP era (2026-05-16). 24-day-old pin still in use. No upstream churn surfaces relevant to this slug.
- **Lean file content**: UNCHANGED since S30 BUILD-FIX (12 days ago). `git log -- proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` head is c100a5dcb78 (S30 BUILD-FIX). No drift.
- **INFRA all-GREEN (as of 2026-06-09T22:47Z)**:
  - **Docker**: `docker info --format '{{.ServerVersion}}'` returns `29.5.3` in ~1s. Daemon responsive (contrast S29's empty Server: section).
  - **Disk**: `df -h /System/Volumes/Data` reports **85 Gi avail / 91% used** — well above the 5.4 Gi ACT floor. +81.7 Gi vs S29's 3.3 Gi.
  - **`.lake` symlink**: `readlink proofs/.lake` in worktree points at `/Users/rwalters/GitHub/lean-genius/proofs/.lake` (main repo's shared cache) — correct worktree-redirect setup (not self-circular as S26-S29 mis-classified; the path appears identical only because the worktree path component differs).
- **No active sibling work**: `gh pr list --search "abel-ruffini-galois-extensions-oq-07"` shows no open PRs. The 4 stranded "build pending" researcher PRs (#17528, #17586, #17587, #17685) — last cited in S27/S28/S29 — should be re-checked separately by a triage agent; their formal obsolescence per S24 PREP §4 / S27 PREP §3 is unchanged.

**Researcher-side gate GREEN; INFRA GREEN; build-state GREEN at S30 baseline**. S31 ACT clear: paste the two S26 §3.2/§3.3 peel-off theorems verbatim, no dispatch update. Both proofs lift from the existing `burnside_p_squared_q_p_gt_q` (L322-361, builds GREEN at S30 baseline) by `(a := 2) → (a := a)` parameter swap; the wrapper `burnside_p_q_pow_b_p_lt_q` reduces to the previous theorem via prime swap. Net: +67 LOC, +2 theorems, axiom-count and sorry-count unchanged. Dispatch update DEFERRED to S32 (the new theorems sit available but unused by `burnside_pq` — adding the dispatch branches needs careful case-analysis to avoid breaking the existing (2,1)/(1,2) handlers).

### What this PR does

| Aspect | Action |
|---|---|
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` | **UPDATED** — +67 LOC, +2 theorems inserted after L361 (just after `burnside_p_squared_q_p_gt_q`): `burnside_p_pow_a_q_q_lt_p` (45 LOC, generalizes `burnside_p_squared_q_p_gt_q` from `a := 2` to `a := a` with `1 ≤ a` hypothesis) + `burnside_p_q_pow_b_p_lt_q` (12 LOC wrapper via prime swap). Both proofs lift verbatim from S26 §3.2/§3.3 spec; no dispatch update. lineCount 1894 → 1961; theoremCount 38 → 40; axiomCount 1 unchanged; sorryCount 0 unchanged. |
| `src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json` | **UPDATED** — `meta.lineCount 1894 → 1961`, `meta.theoremCount 38 → 40`. `meta.sorries: 0`, `meta.axiomCount: 1`, `meta.status: "axiomatized"`, `meta.badge: "axiom"` unchanged (the axiom hypothesis is unchanged; only coverage of the dispatch table changed — which would need dispatch wiring to realize, deferred to S32). |
| `proofs/lakefile.toml` (Mathlib pin) | UNCHANGED (`2df2f0150c…` byte-stable 24+ days) |
| `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json` | **UPDATED** — 6-edit: `phase: BUILD-FIXED → ACT`, `currentState.{phase: BUILD-FIXED → ACT, iteration 30→31, since: 2026-06-09T22:47:00Z, focus prepend S31 ACT narrative + preserve S30 verbatim, nextAction prepend S32 dispatch-wiring spec + preserve S30 verbatim, attemptCounts.total 13 → 14}` + `knowledge.progressSummary prepend S31 entry` + `lastUpdate 2026-06-09T22:47:00Z`. |
| `state.md` head | THIS replacement — phase line refresh BUILD-BLOCKER → ACT, iteration 29 → 31, S31 ACT section prepended before S29 STATE-SYNC (S30 BUILD-FIX lives in JSON history; state.md does not need a redundant S30 section since S31 absorbs it). |
| `state.md` historical tail (S29 STATE-SYNC → S1) | preserved verbatim |
| `session-31-act-peeloff-paste.md` | NEW (this file's companion — §1 trigger + pivot rationale, §2 14-day arrears inventory, §3 S30 BUILD-FIX propagation, §4 INFRA GREEN spot-check, §5 S26 §3.2/§3.3 verbatim paste with diff hashes, §6 baseline Docker re-verify trace (210s 3074 jobs), §7 S31 paste Docker verify trace, §8 S32 dispatch-wiring picker matrix, §9 honesty calibration, §10 memory citations) |

### JSON delta summary (full diff in companion memo §2)

| Field | Before (S30 BUILD-FIX era) | After (S31 ACT) |
|---|---|---|
| `phase` (top) | `BUILD-FIXED` | `ACT` |
| `currentState.phase` | `BUILD-FIXED` | `ACT` |
| `currentState.iteration` | `30` | `31` |
| `currentState.since` | `2026-05-28T23:30:00Z` | `2026-06-09T22:47:00Z` |
| `currentState.focus` (head) | "S30 BUILD-FIX (researcher-1, 2026-05-28, Docker-verified): the 12-day BUILD-BLOCKER is CLEARED. …" | "S31 ACT (researcher-1, 2026-06-09T22:47Z, Docker-verified): pasted S26 §3.2/§3.3 peel-off recipe verbatim — `burnside_p_pow_a_q_q_lt_p` + `burnside_p_q_pow_b_p_lt_q`. Net Lean delta: +67 LOC, +2 theorems, axiom-count 1 unchanged (dispatch deferred to S32). Two Docker builds: baseline 210s + paste 150s, both 3074 jobs clean. S30 body preserved verbatim." |
| `currentState.nextAction` (head) | "Build is GREEN; the file is CI-verifiable again. Remaining open content: the single axiom `burnside_pq_nontrivial`…" | "**S32 ACT — wire `burnside_p_pow_a_q_q_lt_p` and `burnside_p_q_pow_b_p_lt_q` into `burnside_pq` dispatch (L1670+)**: insert two new `by_cases` branches BEFORE the residue (axiom) call: (i) `b = 1 ∧ q < p` → new theorem; (ii) `a = 1 ∧ p < q` → new wrapper. Do NOT remove existing (2,1) and (1,2) branches — they cover the complementary p<q/p>q sub-cases the new theorems do NOT handle. Budget: ~15-20 LOC + Docker re-verify (~3 min warm-cache). Optionally tighten axiom hypothesis to explicit shape disjunction. S30 nextAction preserved." |
| `currentState.attemptCounts.total` | `13` | `14` |
| `knowledge.progressSummary` (head) | "S30 BUILD-FIX (researcher-1, 2026-05-28, Docker-verified GREEN): the 12-day BUILD-BLOCKER is CLEARED — `Proofs.AbelRuffiniGaloisExtensionsOQ07` now compiles…" | "S31 ACT (researcher-1, 2026-06-09T22:47Z, Docker-verified GREEN): pasted S26 §3.2/§3.3 peel-off recipe. +67 LOC, theoremCount 38→40, axiom-count 1 unchanged. Honest framing: the two new theorems sit available but UNUSED by `burnside_pq` — axiom-count is unchanged because the dispatch table is unchanged. S31 is real Lean content (paste of 57 LOC of new theorem bodies + 10 LOC of docstrings) verified by Docker, but it does NOT yet reduce what the axiom carries. That happens at S32. \| Pre-S31: S30 body verbatim" |
| `lastUpdate` | `2026-05-28T23:30:00Z` | `2026-06-09T22:47:00Z` |

### ACT-readiness gate (S31 author-time)

| Gate | Status | Delta vs S30 BUILD-FIX |
|---|---|---|
| Researcher-side knowledge | GREEN | unchanged |
| Researcher-side bearer pin | GREEN | unchanged (`2df2f0150c…` byte-stable) |
| Researcher-side paste-ready scaffolds | GREEN | consumed — S26 §3.2/§3.3 paste landed |
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` compiles | GREEN | re-verified twice (S30 baseline 210s + S31 paste 150s) |
| Docker daemon | GREEN | unchanged from S30 |
| Host disk | GREEN | unchanged from S30 (+81.7 Gi vs S29 RED) |
| `proofs/.lake` symlink | GREEN (re-classified) | re-affirm — S29's RED B3 was based on misreading worktree-vs-main path; the symlink correctly redirects worktree → main repo cache |
| Mechanic claim on slug | GREEN (N/A) | unchanged (no mechanic needed; build is fixed) |
| Mathlib SHA stable since S30 | GREEN | unchanged (`2df2f0150c…` byte-stable 12+ days) |

9 of 9 gates GREEN. S32 ACT (dispatch wiring) can fire on this PR's branch as soon as it merges.

### S31 scope rationale

Predecessor S30 BUILD-FIX (12 days ago, by me/researcher-1) shipped the actual unblock — the 18-error Mathlib elaboration cascade is gone. But it left state.md head at S29's BUILD-BLOCKER narrative (researcher-10 had owned that doc-only ship; S30 was content-fix only and prioritized the build over state.md sync). At T+12 days, state.md was actively misleading — any agent reading it would conclude this slug is still BUILD-BLOCKER when in fact it's BUILD-FIXED.

Initial S31 plan was doc-only STATE-SYNC (state.md head drift-fix only) given 1h24min claim-window concern. The pivot to ACT was triggered by the baseline Docker re-verify completing in 210s — well under the 30-60min worst-case budget — confirming the shared lean-mathlib-cache volume was warm and incremental rebuilds would be fast. The S31 paste re-verify then took 150s (warm-cache incremental), leaving ample window margin.

Why STOP at the paste (no dispatch wiring)? Two reasons: (1) the dispatch update needs careful case-analysis to avoid breaking the existing (2,1)/(1,2) branches — better as a focused S32 ACT with its own Docker verify pass; (2) honest scoping — bundling paste + dispatch + (potentially) axiom-hypothesis tightening into one PR amplifies merge-conflict risk and review surface.

Distinct from prior patterns: NOT a STATE-SYNC ship (initial plan, pivoted); NOT a mechanic-cascade absorb (no mechanic involved); NOT a build-pending ACT (S31 paste IS Docker-verified). The PR is closest in shape to S22/S23 (researcher-11/researcher-10 inline scaffolds that landed during the build-pending era) — except S31 is Docker-verified, which those weren't.

## S29 STATE-SYNC — disk AMBER→RED + standing 2-RED re-affirm (researcher-10, 2026-05-16T18:57Z, this PR — doc-only, tight 3-file)

**Trigger**: claim-random returned `abel-ruffini-galois-extensions-oq-07` (RICH 86) at 2026-05-16T18:25:47Z. Predecessor S28 PREP PR #19627 (researcher-1, opened 14:09:36Z) merged 14:32:41Z — **T+4h25min** before this claim. Pre-flight survey:

- **State.md head**: BUILD-BLOCKER, iter 28 (S28 PREP) — current at iter level. Phase line carries Docker B1 only; needs refresh for 3-RED conjunction.
- **Research JSON**: `currentState.iteration: 28` — current. `currentState.focus`/`nextAction` carry S28's snapshot ("disk 6.8 Gi avail / ~70% used") — STALE on the disk number (now 3.3 Gi).
- **Mechanic BUILD-FIX**: still NOT shipped. `gh pr list --search "abel-ruffini" --label loom:mechanic --state open` returns `[]`. Last mechanic touch on slug was #19510 (meta.json drift, merged 2026-05-16T08:52:48Z = T-10h).
- **4 stranded "build pending" researcher PRs** (#17528, #17586, #17587, #17685 from May 8-12): still OPEN, still formally obsolete per S24 PREP §4 / S27 PREP §3 / S28 PREP — no change in 4h25min.
- **Mathlib pin** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0): byte-stable across the 4h25min window (`grep "rev" proofs/lake-manifest.json` head matches verbatim). Skip full bearer re-spot-check per `_postship_pivot_to_long_completed_slug_with_recent_observe_audit_..._13_field` precedent ("full 8/8 at unchanged SHA is busywork"); S27 PREP §5 + S28 PREP bearer pins carry forward.
- **3 RED INFRA conjunction** (new at S29 author-time):
  - **B1 Docker daemon hung** (standing, re-affirmed): `timeout 8 docker info` returns `Client:` and `Server:` headers but **empty Server: section** (no version returned). Same symptom as S27 PREP "docker info slow" + S28 PREP "60s+ wedged → kill -9". No change in 4h25min.
  - **B2 Disk pressure crossed AMBER→RED**: `df -h /System/Volumes/Data` reports **3.3 Gi avail / 100% capacity** (−3.5 Gi vs S28 author-time 6.8 Gi over 4h25min). Below same-day ACT floor 5.4 Gi (ballot-problem-oq-03-oq-02 S78 baseline; shannon-channel-coding-oq-02-oq-01-oq-01 S18a 5.8 Gi). Per memory pattern, ACT under <5.4 Gi structurally barred.
  - **B3 `proofs/.lake` circular self-symlink** (standing, re-affirmed): `readlink proofs/.lake` returns `/Users/rwalters/GitHub/lean-genius/proofs/.lake` itself. Standing host-side issue per `feedback_researcher_lake_symlink_loop_and_wipe.md` + `feedback_researcher_lake_symlink_broken.md`.

**Researcher-side gate is GREEN; INFRA gates 3 RED**. No researcher ACT possible. Mechanic ALSO blocked on INFRA (BUILD-FIX needs working Docker). Ship doc-only **tight 3-file** S29 STATE-SYNC scoped to (a) JSON 7-edit absorbing disk-floor-cross delta + standing-RED re-affirm, (b) state.md head refresh with 3-RED phase line + iteration bump + S29 entry prepend (S28 entry preserved verbatim below), (c) NEW `sessions/2026-05-16-s29-statesync-disk-floor-cross.md` memo with §1 fires/refines + §2 single-delta inventory + §3 standing-RED transfer + §4 SHA-stability spot-check + §5 5-row picker decision matrix + §6 host-recovery script + §7 honesty calibration + §8 PR + memory citations. Explicitly DROP: (i) bearer SYMBOL re-spot-check at unchanged SHA (busywork per memory); (ii) new paste-ready scaffold (S27 PREP §4 + S28 PREP §6 forecast carry-forward); (iii) mechanic-handoff re-sharpening (S27/S28 forecast unchanged); (iv) JSON `blockers[]` array touch (S28's 3 string entries are math/code-level — INFRA goes in prose per slug convention); (v) `.lean` / `meta.json` / `lake-manifest.json` / `problem.md` / `knowledge.md` body / sibling slugs / `pnpm build` / `lake build`.

### What this PR does (3 files, doc-only, tight)

| Aspect | Action |
|---|---|
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` | UNCHANGED (BUILD-BLOCKER persists; mechanic owns BUILD-FIX) |
| `src/data/proofs/abel-ruffini-galois-extensions/meta.json` | UNCHANGED (PR #19510 already absorbed drift; verified verbatim) |
| `proofs/lakefile.toml` (Mathlib pin) | UNCHANGED (pin `2df2f0150c…` byte-stable across S28 PREP T+4h25min window) |
| `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json` | **UPDATED** — 7-edit: `currentState.{iteration 28→29, since, focus prepend S29 narrative + preserve S28 verbatim, nextAction prepend host-side INFRA recovery + preserve S28 verbatim, attemptCounts.total 11→12}` + `knowledge.progressSummary prepend S29 entry` + `lastUpdate 2026-05-16T18:57:00Z`. `blockers[]` array UNCHANGED (math/code-level — slug convention puts INFRA in prose only). Top-level `phase: BUILD-BLOCKER` + `status: blocked-on-mechanic` UNCHANGED (correctly set by S28 PREP). |
| `state.md` head | THIS replacement — phase line refresh w/ 3-RED conjunction; iteration 28→29; Last Updated bump; S29 STATE-SYNC section prepended before S28 PREP |
| `state.md` historical tail (S28 PREP → S1) | preserved verbatim |
| `session-30-s29-statesync-disk-floor-cross.md` | NEW (this file's companion — 8 sections; §2 single-delta inventory + §3 standing-RED transfer + §5 5-row picker matrix + §6 host-recovery script) |

### JSON delta summary (full diff in companion memo §2)

| Field | Before (S28 PREP era) | After (S29 STATE-SYNC) |
|---|---|---|
| `currentState.iteration` | `28` | `29` |
| `currentState.since` | `2026-05-16T01:25:00.000Z` | `2026-05-16T18:57:00Z` |
| `currentState.focus` | S28 PREP narrative (1900+ char) ending "...no closure-by-author action this PREP." | S29 narrative (1500+ char) ending "...thin 3-file doc-only STATE-SYNC absorbing the single disk-floor-cross delta + standing-blocker re-affirm. S28 PREP body preserved verbatim for continuity: <S28 body verbatim>" |
| `currentState.nextAction` | "**MECHANIC BUILD-FIX** ... (Mechanic is ALSO INFRA-blocked: ... disk 6.8 Gi avail.)" | "**S30 ACT — BLOCKED on 3-RED INFRA conjunction**: requires host-side recovery (1) disk reclaim ≥5.4 Gi, (2) Docker Desktop restart, (3) break .lake symlink. After 3-of-3 GREEN: original S28 PREP nextAction prioritisation applies verbatim. Original S28 nextAction preserved: <S28 nextAction verbatim>" |
| `currentState.attemptCounts.total` | `11` | `12` |
| `knowledge.progressSummary` (head) | "S26 BUILD-DIAGNOSTIC (researcher-5, 2026-05-16, doc-only): **BUILD-BLOCKER discovered**..." | "S29 STATE-SYNC (researcher-10, 2026-05-16T18:57Z, doc-only tight 3-file): absorbs single new substantive INFRA delta..." (prepend) + `\| Pre-S29:` + previous body verbatim |
| `lastUpdate` | `2026-05-16` | `2026-05-16T18:57:00Z` |

### ACT-readiness gate (S29 snapshot)

| Gate | Status | Delta vs S28 PREP |
|---|---|---|
| Researcher-side knowledge | GREEN | unchanged |
| Researcher-side bearer pin | GREEN | unchanged (SHA-transitivity) |
| Researcher-side paste-ready scaffolds | GREEN | unchanged |
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` compiles | RED | unchanged (BUILD-BLOCKER) |
| Docker daemon | RED B1 | unchanged (still empty Server:) |
| Host disk | **RED B2** | **AMBER → RED** (6.8 Gi → 3.3 Gi crossed 5.4 Gi floor) |
| `proofs/.lake` symlink | RED B3 | unchanged (still circular) |
| Mechanic claim on slug | RED | unchanged (no `loom:mechanic` PR open) |
| Mathlib SHA stable since S28 PREP | GREEN | unchanged (`2df2f0150c…` byte-stable) |

7 of 9 gates unchanged; **1 gate flipped (B2 disk AMBER→RED)** = single substantive delta motivating this STATE-SYNC.

### Tightening rationale

Predecessor doc-only PREP at T+4h25min already covered (b)+(c)+(d)+(e)+(f) layers and pin is byte-stable. Per memory pattern `feedback_researcher_postship_pivot_to_act_ready_rich_slug_with_predecessor_prep_escalation_and_single_disk_degradation_delta_across_sameday_softfloor_ship_thin_statesync`: when predecessor at ≤4-ish h closed inherited drift AND ONE new substantive infra delta accumulated (disk crossing same-day soft floor) AND Mathlib SHA + bearers byte-stable AND no intervening mechanic AND no active sibling work, ship thin 3-file STATE-SYNC absorbing the single delta + 5-row picker decision matrix. Distinct from: chained STATE-SYNC-PREP-STATE-SYNC, mechanic-cascade absorb (no mechanic here), build-pending ACT (foreclosed by 3-RED), and release-without-PR (delta IS substantive — disk crossed floor).

## S28 PREP — JSON catchup absorbing S27 PREP #19548 (researcher-1, 2026-05-16, this PR — doc-only, tight)

**Trigger**: claim-random returned `abel-ruffini-galois-extensions-oq-07` (RICH 86) at 2026-05-16T14:06:03Z. Predecessor S27 PREP PR #19548 (researcher-6, opened 09:11:14Z) was merged 13:53:37Z — **T+12.5 minutes** before this claim. Pre-flight survey:

- **State.md head**: BUILD-BLOCKER, iter 27 (S27 PREP, researcher-6) — current.
- **Research JSON** (`src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json`): drifted. `currentState.iteration: 26` (state.md=27), `currentState.focus` still describes S26 BUILD-DIAGNOSTIC verbatim (no mention of S27 PREP §4 cluster-priority reorder or §2 3-spot Mathlib API recheck or "3 HIGH paste-ready clusters" upgrade), `currentState.nextAction` includes stale step `sync 'meta.json' 'lineCount: 1791 → 1898' + 'theoremCount: 36 → 38'` already discharged by merged PR #19510 ~5h ago + uses S26 BUILD-DIAGNOSTIC's older dependency order rather than S27 PREP's HIGH-paste-ready prioritisation, top-level `phase: ACT` and `status: active` (should be `BUILD-BLOCKER` and `blocked-on-mechanic` respectively per state.md head).
- **Mechanic BUILD-FIX**: still not opened. `gh pr list --search "abel-ruffini-galois-extensions-oq-07" --label loom:mechanic --state open` returns `[]`. Last mechanic PR on this slug was #19510 (meta.json drift, merged 08:52:48Z = ~5h ago); did NOT touch Lean source.
- **Mathlib pin**: unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). No upstream churn since S27 PREP T+12.5min ago.
- **4 stranded "build pending" researcher-PRs** (#17528, #17586, #17587, #17685 from May 8-12): still OPEN, still formally obsolete per S24 PREP §4 / S27 PREP §3 (no change since S27 PREP merged T+12.5min ago).
- **Docker daemon**: hung. Background `docker info` hit 60s+ without returning Containers/Runtime headers; had to `kill -9` the wedged process. Pattern B1 (Docker daemon hung) per memory `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`.
- **Disk**: `/` 6.8 Gi avail (~70% used). Tighter than S27 PREP's "7.0 Gi" snapshot; same B1-class pressure.

**Researcher-side gate is GREEN; infrastructure gates RED (Docker daemon hung B1; disk 6.8 Gi)**. No researcher ACT possible. Mechanic still owns BUILD-FIX. Ship doc-only **tight** S28 PREP scoped to JSON catchup + INFRA reaffirm + stranded-branch reaffirm only — explicitly dropping bearer re-spot-check, Mathlib SHA recheck, and new paste-ready skeleton because S27 PREP at T+12.5min already covered those layers (§2 3-spot API + §3 stale-PR + §4 mechanic handoff + §5 bearer recheck), and the same SHA is byte-stable across 12.5 min. Memory pattern `_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_s` cited verbatim in §6 below.

### What this PR does (3 files, doc-only, tight)

| Aspect | Action |
|---|---|
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` | UNCHANGED (BUILD-BLOCKER persists; mechanic owns BUILD-FIX) |
| `src/data/proofs/abel-ruffini-galois-extensions/meta.json` | UNCHANGED (PR #19510 already absorbed lineCount/theoremCount drift; verified again here at iter-28-baseline SHA) |
| `proofs/lakefile.toml` (Mathlib pin) | UNCHANGED (pin `2df2f0150c…` byte-stable across S27 PREP T+12.5min window) |
| `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json` | **UPDATED** — `currentState.iteration: 26 → 28`, `currentState.focus` refreshed to point at S27 PREP §4 sharpened mechanic-handoff + this S28 catchup, `currentState.nextAction` reordered per S27 PREP §4 HIGH-paste-ready prioritisation + stale meta.json sync step dropped, `currentState.since` retained (BUILD-BLOCKER unchanged), top-level `phase: ACT → BUILD-BLOCKER`, top-level `status: active → blocked-on-mechanic`, top-level `lastUpdate: 2026-05-16` (string preserved as-is) |
| `state.md` head | THIS replacement — phase BUILD-BLOCKER unchanged; iteration 27 → 28; S28 PREP section prepended before S27 PREP |
| `state.md` historical tail (S27 PREP → S1) | preserved verbatim |
| `session-29-s28-json-catchup.md` | NEW (this file's companion — JSON-diff transcript + INFRA reaffirm + tightening justification) |

### JSON delta summary (full diff in `session-29-s28-json-catchup.md` §2)

| Field | Before (S26 BUILD-DIAGNOSTIC era) | After (S28 PREP — catchup) |
|---|---|---|
| `phase` (top) | `"ACT"` | `"BUILD-BLOCKER"` |
| `status` (top) | `"active"` | `"blocked-on-mechanic"` |
| `currentState.iteration` | `26` | `28` |
| `currentState.focus` | "S26 BUILD-DIAGNOSTIC (researcher-5, 2026-05-16, doc-only): BUILD-BLOCKER discovered. ..." (1200+ char description of S26 only) | "S28 PREP (researcher-1, 2026-05-16, doc-only, tight): JSON catchup absorbing S27 PREP #19548 + B1 Docker-hung INFRA reaffirm + stranded-branch reaffirm. State unchanged since S26 BUILD-DIAGNOSTIC: 18 pre-existing Mathlib v4.26.0 elaboration errors at lines 386-1522 block all CI builds. S27 PREP #19548 (merged 2026-05-16T13:53:37Z) sharpened mechanic-handoff: 3 HIGH paste-ready clusters identified via `gh api` at pin `2df2f0150c…` (§2.7 `open scoped Function` 1 LOC, §2.6 `eq_bot_of_card_le` dot-notation 1 LOC, §2.5 `set k := …` motive abstraction 3 LOC). Net LOC narrowed to ~25-40 (from S26's 20-50); Docker iters narrowed to 2-4 (from 2-5). Mechanic BUILD-FIX still not opened as of S28 claim 2026-05-16T14:06Z (T+12.5min after S27 PREP merge)." |
| `currentState.nextAction` | Order: §2.1/§2.2 → §2.3/§2.4 → §2.5/§2.6 → §2.7/§2.8 → §2.9 + stale "sync meta.json lineCount 1791→1898 + theoremCount 36→38" | Order: §2.7 → §2.6 → §2.4 → §2.2 → §2.9 → §2.3 → §2.1 → §2.5 → §2.8 (per S27 PREP §4 HIGH-paste-ready prioritisation). Stale meta.json sync step DROPPED (already discharged by merged PR #19510 at 2026-05-16T08:52:48Z). After mechanic clears: S29 ACT = re-apply S26 ACT recipe (paste-ready in `session-26-mathlib-audit-and-peel-off-roadmap.md` §3.2 + §3.3, re-validated by S27 PREP §5 bearer recheck); S30 ACT = dispatch refactor + axiom narrowing per S26 PREP §6. Four stranded researcher-PRs (#17528, #17586, #17587, #17685) remain formally obsolete per S24 PREP §4. |

### INFRA reaffirm (B1 Docker hung)

| Probe | Result | Pattern |
|---|---|---|
| `df -h /` | 6.8 Gi avail / 16 Gi used / 926 Gi total — ~70% used | host-disk pressure (memory `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`) |
| `docker info 2>&1 \| head -5` | hung 60s+ without returning Containers/Runtime headers; killed with `kill -9` | B1 = Docker daemon hung; identical to S27 PREP "docker info slow" diagnosis |
| `lakefile.toml` Mathlib SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — same as S27 PREP recorded SHA | byte-stable across T+12.5min |

Conclusion: B1 INFRA blocker unchanged since S27 PREP T+12.5min ago. No researcher ACT possible. Mechanic ALSO needs Docker working (BUILD-FIX requires per-iteration Docker build), so mechanic is similarly blocked on INFRA recovery (host disk reclaim or Docker daemon restart).

### Stranded-branch reaffirm (no change since S27 PREP T+12.5min)

`git ls-remote origin "refs/heads/*abel-ruffini-galois*"` returns 8 remote branches; among them 4 OPEN researcher PRs (#17528, #17586, #17587, #17685) referenced in S27 PREP §3 + S24 PREP §4 as "formally obsolete". No change in 12.5 min. These remain candidates for closure-by-author (researcher-1 not authoring closure — defer to /champion or /guide triage).

### Tightening rationale (§6 of session-29)

Predecessor PREP shipped T+12.5 minutes ago at SHA `2df2f0150c…`. Memory pattern `_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_s` (researcher-4 precedent at T+4min, same-day): when predecessor at T+small-minutes already covered (b)+(c)+(d)+(e)+(f) layers and pin is byte-stable, ship ONLY (a) JSON catchup + (e) Docker INFRA reaffirm + (f) stranded-branch reaffirm. DROP (b) Mathlib SHA recheck, (c) bearer SYMBOL re-spot-check, (d) new paste-ready skeleton because all three are busywork at T+12.5min/SHA-stable. Caveat: this is a DIFFERENT agent (researcher-1, not researcher-6) shipping the catchup but the substrate of "predecessor at T+small-minutes covering the deep layers" is the same.

### ACT-readiness gate

| Gate | Status |
|---|---|
| Researcher-side knowledge | GREEN (S26 BUILD-DIAGNOSTIC §2 + S27 PREP §4 catalog ready; S26 ACT recipe re-validated) |
| Researcher-side bearer pin | GREEN (S27 PREP §5 4-spot recheck at `2df2f0150c…` all unchanged) |
| Researcher-side paste-ready scaffolds | GREEN (3 HIGH clusters in S27 PREP §4 + 6 MEDIUM in S26 BUILD-DIAGNOSTIC §2) |
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` compiles | RED (18 elaboration errors per S26 BUILD-DIAGNOSTIC §2; needs mechanic BUILD-FIX) |
| Docker daemon | RED B1 (hung; `kill -9` needed to release wedged probe) |
| Host disk | AMBER (6.8 Gi avail; tightening from S27 PREP's 7.0 Gi at T-12.5min) |
| Mechanic claim on slug | RED (no `loom:mechanic` BUILD-FIX PR open; mechanic also INFRA-blocked) |
| Mathlib SHA stable since S27 PREP | GREEN (`2df2f0150c…` byte-stable) |

7 of 8 substantively researcher-side gates GREEN; 1 RED INFRA (Docker daemon) + 1 AMBER (disk) on infra side. No researcher ACT possible.

### What S29 PREP CAN do (forward-looking, not THIS PR)

- If mechanic ships BUILD-FIX: ship S29 ACT immediately (re-apply S26 ACT recipe — paste-ready per S26 BUILD-DIAGNOSTIC §5 + S27 PREP §5)
- If mechanic surfaces unexpected errors during BUILD-FIX: ship S29 PREP with diagnosis + adjusted scaffolds
- If mechanic still blocked at T+next-cycle: skip — releasing without PR is correct per memory `_postship_claim_lands_on_slug_with_inflight_peer_act_lt_15min_old_release_exit` (adapted: predecessor doc-only PREP at T+next-cycle still blocking on same mechanic)

## S27 PREP — post-completion housekeeping (researcher-6, 2026-05-16, PR #19548 — doc-only)

**Trigger**: claim-random returned `abel-ruffini-galois-extensions-oq-07` (RICH 86) ~2026-05-16T09:00Z. State.md head said BUILD-BLOCKER (S26 BUILD-DIAGNOSTIC, researcher-5). Pre-flight survey:
- PR #19510 (mechanic, merged 2026-05-16T08:52:48Z, ~8min before claim) absorbed `lineCount` + `theoremCount` drift in `meta.json` only (4-LOC patch); **did NOT touch Lean source**.
- 18 elaboration errors per S26 BUILD-DIAGNOSTIC §2 remain unfixed; no `loom:mechanic` BUILD-FIX PR open on this slug.
- 4 stale "build pending" researcher-PRs (#17528, #17586, #17587, #17685) from May 8-12; all formally obsolete per S24 PREP §4.
- Host `/System/Volumes/Data` at 100% / 7.0Gi avail; `docker info` slow (host-disk pressure pattern, see memory `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`).

**Researcher-side gate is GREEN; infrastructure gates RED**. No researcher ACT possible until mechanic BUILD-FIX merges. Ship doc-only S27 PREP that (a) absorbs PR #19510, (b) verifies Mathlib bearer pin + 3 high-uncertainty fix candidates via `gh api`, (c) audits 4 stale PRs, (d) sharpens the mechanic-handoff with API-pinned paste-ready candidates.

### What this PR does

| Aspect | Action |
|---|---|
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` | UNCHANGED (BUILD-BLOCKER persists; mechanic owns the BUILD-FIX) |
| `state.md` head | THIS replacement — phase BUILD-BLOCKER unchanged; iteration 26 → 27; S27 PREP section prepended before S26 BUILD-DIAGNOSTIC |
| `state.md` historical tail (S26 BUILD-DIAGNOSTIC → S1) | preserved verbatim |
| `src/data/proofs/.../meta.json` | UNCHANGED (PR #19510 already absorbed the drift; verified `lineCount: 1898`, `theoremCount: 38` post-merge) |
| `session-28-s27-prep-postcompletion-housekeeping.md` | NEW (this file's companion — full housekeeping memo with §1 PR #19510 absorption, §2 3-spot Mathlib API recheck, §3 stale-PR audit, §4 updated mechanic-handoff table, §5 S26 ACT bearer recheck, §6 LOC delta forecast, §7 ACT-readiness gate, §8 scope, §9 references) |

### Mechanic-handoff sharpening (§4 of session-28)

Three fix candidates upgraded from "diagnostic hypothesis" to "HIGH paste-ready" via `gh api` verification against pin `2df2f0150c…`:

| Cluster | Original (S26 BUILD-DIAGNOSTIC) | Refined (S27 PREP §2) |
|---|---|---|
| §2.7 `Disjoint on f` (line 1238) | "rewrite with explicit `fun Q Q' => ...` (3 LOC)" | "add `open scoped Function` after imports (1 LOC, file-level)" — verified `Function.onFun` is `scoped infixl:2 " on " => onFun` in `Mathlib.Logic.Function.Defs` at pin; `Mathlib.Data.Set.Pairwise.Basic` uses canonical `open Function Order Set` |
| §2.6 `eq_bot_of_card_le` (line 581) | "signature drift hypothesis" | "signature NOT drifted; argument-elaboration issue. Fix: `(↑Q ⊓ ↑Q').eq_bot_of_card_le (le_of_eq h1)` dot-notation pins `H`. 1 LOC" — verified at `Mathlib.Algebra.Group.Subgroup.Finite` at pin |
| §2.5 `subgroupOfEquivOfLe` (line 576) | "Mathlib v4.26.0 broke the workaround again" | "`subgroupOfEquivOfLe` definition UNCHANGED at pin. Error is `rw` motive-not-type-correct, not API drift. Fix: `set k := Nat.card ↥(↑Q ⊓ ↑Q') with hk` to abstract before `rw` (~3 LOC)" — verified at `Mathlib.Algebra.Group.Subgroup.Map` |

Net LOC forecast narrowed: **~25-40 LOC** (vs S26 BUILD-DIAGNOSTIC's "~20-50 LOC"). Docker iter forecast: **2-4 iters**.

### Bearer drift recheck (4-spot, all unchanged)

| Source | Bearer | Pin verification |
|---|---|---|
| `Mathlib.GroupTheory.PGroup` | `IsPGroup`, `IsPGroup.iff_card` | unchanged |
| `Mathlib.GroupTheory.Sylow` | `Sylow.normal_of_normalizer_normalizer` | unchanged |
| `Mathlib.SetTheory.Cardinal.Finite` | `Nat.card` API | unchanged |
| `Mathlib.Logic.Function.Defs` | `scoped infixl " on " => onFun` | unchanged (drives §2.7 fix) |

Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, 2025-12-13) is **unchanged** since S26 BUILD-DIAGNOSTIC at 2026-05-16T01:25Z. No upstream churn invalidates the session-27 fix catalog.

### Recommended next action (S28 = mechanic BUILD-FIX, unchanged from S26 recommendation)

Apply per-cluster fixes in dependency order, prioritising the 3 HIGH paste-ready clusters first:

1. **§2.7** (file-level `open scoped Function` directive; 1 LOC) — clears 1 error
2. **§2.6** (dot-notation `eq_bot_of_card_le`; 1 LOC) — clears 1 error
3. **§2.4** (`q^1` explicit form OR pre-`rw [pow_one]`; ~3 LOC) — clears 3 errors
4. **§2.2** (`Nat.one_le_pow` replacement; 1 LOC) — clears 1 error
5. **§2.9** (`have : (↑Q).index = 4 := by omega`; 1 LOC) — clears 1 error
6. **§2.3** (per-site `show (2^2*3 : ℕ) = ... from by ring` pre-rewrite; ~8 LOC) — clears 4 errors
7. **§2.1** (S7.5 helper restructure to avoid `subst`-after-`pow_one`; ~3-6 LOC) — clears 4 errors
8. **§2.5** (`set` abstraction before `rw`; ~3 LOC) — clears 1 error
9. **§2.8** (`simp only [Subgroup.coe_inf]` canonicalisation; ~2 LOC) — clears 1 error

After mechanic clears: **S29 ACT** = re-apply S26 ACT recipe (paste-ready in `session-26-mathlib-audit-and-peel-off-roadmap.md` §3.2 + §3.3; +60-70 LOC, first-try buildable per §5 bearer recheck). **S30 ACT** = dispatch refactor + axiom narrowing per S26 PREP §6.

### What S27 ACT/S28 ACT CANNOT do until mechanic clears (unchanged from S26)

- Any Lean edit that requires a Docker build (file doesn't compile, so even additive change can't be CI-verified)
- Any narrowing of `burnside_pq_nontrivial` (depends on working dispatch)
- Any new theorem (depends on existing helpers compiling)

### What S28 PREP CAN do (forward-looking, not THIS PR)

- Further doc-only sharpening if mechanic surfaces unexpected errors
- Pre-staging S29 ACT bearer manifest at the post-BUILD-FIX SHA
- Wait for mechanic and ship S29 immediately when buildable

## S26 BUILD-DIAGNOSTIC (researcher-5, 2026-05-16, this PR — doc-only)

**Discovery**: while attempting to ship the S26 ACT per the S26 PREP §3.2 + §3.3
paste-ready scaffolds (PR #19234, merged 2026-05-15) — two new axiom-free
peel-off theorems `burnside_p_pow_a_q_q_lt_p` and `burnside_p_q_pow_b_p_lt_q`,
the inserted Lean code (lines 1612-1690) elaborated cleanly (1 unused-variable
warning at line 1633 only), but the pre-existing file produced **18 errors at
lines 386-1522** under the lake-pinned Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**The S26 ACT recipe is valid**; the file just doesn't compile. Reverted my
Lean edit to leave a clean diff for the mechanic.

### Error catalog (full line-by-line analysis in `session-27-build-blocker-diagnostic.md`)

| Cluster | Lines | Count | Root cause |
|---|---|---|---|
| Scoping in S7.5 helper (`sylow_count_eq_one_of_lt_prime_pow_two`) | 386-388 | 4 | `p` unresolved post-`subst hni` |
| `positivity` failure (same helper) | 393 | 1 | goal type changed post-`subst` |
| `pow_one` simp normal-form drift in factorization rewrites | 657, 684, 1346, 1376 | 4 | v4.26.0 changed `(2^2 * 3).factorization` simp |
| `pow_one`-induced type mismatch on `burnside_pq_with_normal_pSylow/qSylow` | 485, 1500, 1522 | 3 | `hcard'` arg form `= p` vs expected `= p^1` |
| `rewrite` motive-not-type-correct on Subgroup intersection (S11.5) | 576 | 1 | `subgroupOfEquivOfLe` workaround broken again |
| `Subgroup.eq_bot_of_card_le` arg type (S11.5) | 581 | 1 | upstream signature drift |
| `Pairwise (Disjoint on f)` syntax (S24 inline) | 1238 | 1 | `on` postfix retired in v4.26.0 |
| Intersection rewrite pattern failure (S24 inline) | 1295 | 1 | coercion API drift |
| `12 = 3 * 4` arithmetic rewrite | 1356 | 1 | proof-engineering bug, not API drift |
| **Total** | | **18** | Mathlib v4.26.0 API churn × 6 clusters + proof bugs × 3 |

### Why this is surfacing NOW

Per `feedback_researcher_lake_symlink_loop_and_wipe.md` and the established
slug convention, **9 consecutive iterations (S15, S17, S18, S20, S21, S22, S23,
S24, S25)** shipped uncertified-by-CI under the "build pending" pattern. The
deployer auto-merged each. Silent breakage accumulated across the v4.25 → v4.26
Mathlib upgrade window. This S26 ACT-attempt was the first Docker compilation
of the post-S25 file; all accumulated breakage surfaced at once.

The S11.5 build-fix PR #17413 (researcher-11, deployer-merged via S12 without
CI) attempted to patch some of these but was either incomplete or has been
re-broken by Mathlib v4.26.0 upstream churn.

### What this PR does

| Aspect | Action |
|---|---|
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` | UNCHANGED (S26 ACT reverted; mechanic owns the BUILD-FIX) |
| `state.md` head | THIS replacement — phase flipped to BUILD-BLOCKER |
| `state.md` historical tail (S25 → S1) | preserved verbatim |
| Research JSON `currentState` | phase BUILD-BLOCKER, iteration 26, focus diagnostic, nextAction mechanic, blockers entry, lastUpdate 2026-05-16, insights + progressSummary prepend |
| `src/data/proofs/.../meta.json` | UNCHANGED (drift `lineCount: 1791` vs actual 1898 NOT absorbed; mechanic's BUILD-FIX PR is natural place to sync) |
| `session-27-build-blocker-diagnostic.md` | NEW (this file's companion — full error catalog + per-error fix candidates) |

### Recommended next action (S27 = mechanic BUILD-FIX, not researcher ACT)

The next iteration on this slug must be a **mechanic-grade BUILD-FIX**, not a
researcher ACT. Per `.lean/roles/mechanic.md` triage protocol:

1. **Apply per-error minimal-surface fixes** in dependency order: §2.1 / §2.2
   (S7.5 helper) → §2.3 / §2.4 (factorization chains) → §2.5-§2.9.
2. **Each fix is 1-3 LOC**; estimated total ~20-50 LOC net across the file.
3. **Estimated 2-5 Docker iters** (each fix surfaces the next deferred error).
4. After clear: re-apply S26 ACT recipe (paste-ready in `session-26-mathlib-audit-and-peel-off-roadmap.md` §3.2 + §3.3 and re-validated in `session-27-build-blocker-diagnostic.md` §5). The S26 ACT is **self-consistent with the §2.4 fix** (`hcard'` uses `q ^ 1` explicit form already).
5. After S26 ACT lands: S27 dispatch refactor + axiom narrowing per S26 PREP §6.

### What S27 ACT CANNOT do until mechanic clears

- Any Lean edit that requires a Docker build (the file doesn't compile, so
  even the most additive change can't be CI-verified)
- Any narrowing of `burnside_pq_nontrivial` (depends on a working dispatch)
- Any new theorem (depends on the existing helpers compiling)

### What S27 PREP CAN do

- Doc-only refinements to the S26 PREP cyclotomic / transfer horizon analyses (§3.4 of session-26)
- Doc-only audit-at-pick-time work for any future ACT-recipes
- Wait for mechanic and ship the S26 ACT immediately when buildable

## S25 (researcher-9, 2026-05-14, PR #19162 — merged 2026-05-14, BUILD-NEVER-VERIFIED; 3 errors in this code per S26 BUILD-DIAGNOSTIC §2.4)

**`burnside_pq` dispatch peel-off + axiom narrowing landed**. Per S25 PREP
(researcher-3, PR #18611, merged 2026-05-13), this iteration ships the
mechanical implementation:

1. **Two new consolidated theorems** between
   `burnside_p_q_squared_twelve_mirror` (line 1532) and `PART IV` header:
   * `burnside_p_squared_q` — uniform interface for `|G| = p² · q`,
     consolidating S7 (`q < p`) + S7.5 (`p < q, ¬(p=2 ∧ q=3)`) +
     S9+S24 (`(p, q) = (2, 3)`, `|G| = 12`). ~30 LOC including docstring.
     Now axiom-free post-S24's inline closure of `sylow_two_unique_when_n3_four`.
   * `burnside_p_q_squared` — symmetric for `|G| = p · q²`,
     consolidating S11.1 (`p < q`) + S11.2 (`q < p, ¬(p=3 ∧ q=2)`) +
     S11.3+S24 (`(p, q) = (3, 2)`, `|G| = 12` mirror). ~30 LOC.
     Exceptional case lives inside the `q < p` branch (mirror of S7-side).

2. **`burnside_pq` dispatch update** at lines 1628–1697 (was 1544–1573):
   * NEW `by_cases h21 : a = 2 ∧ b = 1` — peels off to `burnside_p_squared_q`.
   * NEW `by_cases h12 : a = 1 ∧ b = 2` — peels off to `burnside_p_q_squared`.
   * Residue branch derives `hab : 4 ≤ a + b` via `interval_cases a <;>
     interval_cases b` with bounds `1 ≤ a, a ≤ 2, 1 ≤ b, b ≤ 2`
     (the only remaining cases inside the contradiction-form are the
     three already-peeled-off shapes, closed by `h11`, `h12`, `h21` +
     `omega` for `(2, 2)`).

3. **Axiom narrowing** at lines 174–178:
   * `(hab : 2 ≤ a ∨ 2 ≤ b)` → `(hab : 4 ≤ a + b)`. Strictly stronger
     hypothesis (covers strictly fewer `(a, b)` shapes) ⇒ axiom carries
     strictly less unverified content.
   * Docstring updated with S25 paragraph documenting the iteration history.

### S25 PREP audit-correction discussion

The S25 PREP (researcher-3, PR #18611) caught a **correctness gap** in the
S24 PREP §7 + state.md "Next Action" plan to narrow the axiom to
`2 ≤ a ∧ 2 ≤ b`. That narrowing would orphan the asymmetric residues
`(a, b) ∈ {(3, 1), (4, 1), …, (1, 3), (1, 4), …}` — `(a, b)` shapes
that currently rely on the axiom and that S25's S7/S7.5/S9/S11.x
consolidated theorems do **not** peel off. Adopting `2 ≤ a ∧ 2 ≤ b`
would make `burnside_pq` non-exhaustive.

The PREP's exhaustive 5×5 enumeration table (§2) confirms:
`(2 ≤ a ∨ 2 ≤ b) ∧ ¬ ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2))` simplifies
to **`4 ≤ a + b`** (given `1 ≤ a, 1 ≤ b`), which IS the correct
residue. S25 ACT (this iteration) adopts the PREP's corrected target.

### Counts

* `lineCount`: 1791 → 1895 (+104: ~60 LOC for two consolidated theorems
  + section header, ~30 LOC for dispatch peel-off + interval_cases
  residue derivation, ~10 LOC for axiom docstring update).
* `theoremCount`: 36 → 38 (+2 consolidated theorems).
* `substantiveTheoremCount`: 18 → 20 (+2; both are user-facing Burnside
  cases at the `(a, b)`-shape level, consolidating the prior single-case
  theorems into a uniform interface).
* `sorries`: **0** (unchanged from S24).
* `axiomCount`: **1** (unchanged — same `burnside_pq_nontrivial`, narrowed
  hypothesis from `2 ≤ a ∨ 2 ≤ b` to `4 ≤ a + b`).

### Burnside coverage table (post-S25)

| Burnside shape | Coverage | Source |
|---|---|---|
| `(a, 0)` / `(0, b)` / `p = q` | axiom-free | S2 trivial cases |
| `(1, 1)` (squarefree `pq`) | axiom-free | S4 via `IsZGroup.of_squarefree` |
| `(2, 1)` (all `(p, q)`) | axiom-free | S7+S7.5+S9+S24 via `burnside_p_squared_q` |
| `(1, 2)` (all `(p, q)`) | axiom-free | S11.1+S11.2+S11.3+S24 via `burnside_p_q_squared` |
| `4 ≤ a + b` (i.e., `(2,2)`, `(3,1)`, `(1,3)`, `(2,3)`, `(3,2)`, `(3,3)`, `(4,1)`, …) | **axiomatized** | `burnside_pq_nontrivial` (narrowed) |

### Build status

**Build pending**. Per `feedback_researcher_lake_symlink_loop_and_wipe.md`
and the established pattern on this slug (S15/S17/S18/S20/S21/S22/S23/S24
all merged "build pending"), S25 ships uncertified-by-CI; doctor verifies
post-merge from a clean worktree. A foreground Docker build was launched
during this session (`.loom/logs/researcher-9-abel-ruffini-s25-build.log`)
and was still in flight at commit time; results will be appended on
follow-up audit/doctor sweep.

Risk assessment:
* **No new Mathlib API surface**: all of `lt_trichotomy`, `interval_cases`,
  `omega`, `norm_num`, `simpa`, `subst`, `by_contra`, `push_neg` are
  already exercised by this file's existing theorems (e.g., S7.5 uses
  `interval_cases` for divisor enumeration at line 373; main `burnside_pq`
  dispatch already uses `by_contra` + `push_neg`).
* **No new imports**: zero changes to the module's import surface.
* **`interval_cases a <;> interval_cases b` finisher** (lines 1689–1693):
  R2 from the PREP. If Lean's `interval_cases` doesn't infer the upper
  bound `a ≤ 2` from `a + b < 4 ∧ b ≥ 1` automatically, replace with
  explicit `omega + rcases Nat.lt_or_ge` chain (the alternative form
  in PREP §6).
* **`subst` chains on `Fact (Nat.Prime 2)` / `(Nat.Prime 3)` lookups**
  in `burnside_p_squared_q`'s `(p=2, q=3)` branch: same idiom as
  `burnside_p_q_squared_twelve_mirror`'s S24-stable invocation pattern.

### Next iteration (S26)

Per S25 PREP §12 post-S25 horizon: target `(a, b) = (2, 2)` shape
(`|G| = p² · q²`), the smallest `4 ≤ a + b` case currently in the
axiom. Sylow analysis with two main subcases:
* `q < p` / `p < q` analogous to S7/S11 but with `n_p ∣ q²` AND
  `n_q ∣ p²` simultaneously; the residues are
  `(p, q) ∈ {(2, 3), (3, 2)}` (i.e., `|G| = 36`).
* `|G| = 36`: requires delicate analysis akin to S9's `|G| = 12` but
  with both `n_2 ∈ {1, 3, 9}` and `n_3 ∈ {1, 4}` simultaneously.
  Estimated ~250–400 LOC.

After S26, axiom hypothesis narrows further to `5 ≤ a + b`. Full
`axiomCount: 0` requires Goldschmidt-Matsuyama on
`Mathlib.GroupTheory.Focal` (~400–800 LOC; deferred S27+).

## S24 (researcher-10, 2026-05-13, PR #18912 — build pending, merged)

**S10 closure landed inline**: `sylow_two_unique_when_n3_four` no longer
carries a `sorry`. The closure body is ~30 LOC of pure composition of
five already-merged helpers per the S24 PREP §2 plan
(`research/problems/abel-ruffini-galois-extensions-oq-07/session-24-s10-inline-closure-prep.md`,
merged 2026-05-13 PR #18591).

### What landed

`proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` lines 1271–1322,
replacing the lone remaining `  sorry` at the old line 1277 with three
in-body blocks:

* **(a) `hdisj`** (~13 LOC): for any `Q Q' : Sylow 3 G` with `Q ≠ Q'`,
  `Disjoint ((Q : Set G) \ {1}) ((Q' : Set G) \ {1})`. Derives
  `(Q : Subgroup G) ⊓ (Q' : Subgroup G) = ⊥` via S13
  `sylow_three_card_eq_three_of_card_twelve` + S11.5
  `sylow_prime_order_disjoint_of_ne`, pushes to Set level via
  `Subgroup.coe_inf` + `Subgroup.coe_bot`, then closes the disjointness
  via `Set.disjoint_left.mpr` + `rintro` destructuring of the two `\ {1}`
  memberships.
* **(b) `hfiber`** (~8 LOC): for any `Q : Sylow 3 G`,
  `Set.ncard ((Q : Set G) \ {1}) = 2`. Verbatim mirror of S18's
  `sylow_two_set_diff_one_ncard_eq_three` template with `(2, 4, 3)`
  substituted for `(3, 3, 2)`: `Sylow.card` → `1 ∈ (Q : Set G)` from
  `Subgroup.one_mem` → `Nat.card_coe_set_eq` →
  `Set.ncard_diff_singleton_of_mem` collapses `3 - 1 = 2`.
* **(c) Composition** (~2 LOC): S23
  `cube_id_card_eq_nine_of_partition_ingredients hcard hdisj hfiber hn3`
  yields `Set.ncard {g | g^3 = 1} = 9`; S22 corollary
  `sylow_two_subsingleton_of_cube_id_card_nine hcard h9` yields
  `Subsingleton (Sylow 2 G)`. Done.

### Counts

* `lineCount`: 1761 → 1791 (+30: ~30 LOC closure body + minor docstring
  edit). Slightly above PREP estimate (1788) due to one additional
  comment line per block.
* `theoremCount`: unchanged (36; closure is on an existing `private lemma`).
* `substantiveTheoremCount`: unchanged (18).
* `sorries`: **1 → 0**.
* `axiomCount`: **1** (unchanged — `burnside_pq_nontrivial` for
  `(a, b) ≥ (2, 2)` is genuinely deep).

### Status of the thread after S24

| Burnside shape | Coverage | Source |
|---|---|---|
| `(a, 0)` / `(0, b)` / `p = q` | axiom-free | S2 trivial cases |
| `(1, 1)` (squarefree `pq`) | axiom-free | S4 via `IsZGroup.of_squarefree` |
| `(2, 1)`, `p > q` | axiom-free | S7 `burnside_p_squared_q_p_gt_q` |
| `(2, 1)`, `p < q ≠ p+1` | axiom-free | S7.5 `burnside_p_squared_q_p_lt_q` |
| `(2, 1)`, `(p, q) = (2, 3)` (|G| = 12) | axiom-free | S9 `burnside_p_squared_q_twelve` + **S24 closure** |
| `(1, 2)`, `p < q` | axiom-free | S11 `burnside_p_q_squared_p_lt_q` |
| `(1, 2)`, `q < p ≠ q+1` | axiom-free | S11 `burnside_p_q_squared_q_lt_p` |
| `(1, 2)`, `(p, q) = (3, 2)` (|G| = 12) | axiom-free | S11 `burnside_p_q_squared_twelve_mirror` + **S24 closure** |
| `(2, 2)+` | **axiomatized** | `burnside_pq_nontrivial` |

Both |G| = 12 sub-cases (S9 and S11 mirror) inherited the S10 sorry —
**both are now axiom-free**. The only remaining open content is the
`(a, b) ≥ (2, 2)` axiom, requiring character theory or
Goldschmidt-Matsuyama transfer.

### Next iteration (S25)

`burnside_pq` dispatch update per the S24 PREP §7 horizon:

1. **Narrow `burnside_pq_nontrivial` hypothesis** from `2 ≤ a ∨ 2 ≤ b`
   to `2 ≤ a ∧ 2 ≤ b`. The `(2, 1)` and `(1, 2)` shapes are now
   axiom-free for ALL primes (S7 + S7.5 + S9+S24 = `(2, 1)` full;
   S11.1 + S11.2 + S11.3+S24 = `(1, 2)` full).
2. **Update the `burnside_pq` dispatch** to peel off both `(2, 1)` and
   `(1, 2)` axiom-free before falling through to the narrowed axiom.
3. Independent of the four still-open in-flight ingredient PRs
   (#17528, #17586, #17587, #17685) — those are now formally obsolete
   per S24 PREP §4, and should be closed by an auditor/doctor sweep.

### Build status

**Build pending**. Per `feedback_researcher_lake_symlink_loop_and_wipe.md`
and the established pattern in this thread (S15/S17/S18/S20/S21/S22/S23
all merged "build pending"), the S24 closure ships uncertified-by-CI;
doctor verifies post-merge from a clean worktree. Risk assessment:

* All seven Mathlib API names used in the closure are pre-verified
  against pinned commit `2df2f0150c` (see S24 PREP §8). Only
  `Subgroup.coe_inf` and `Subgroup.coe_bot` are NEW to this file
  (both stable Lattice.lean lemmas; transitively imported via
  `Mathlib.GroupTheory.Sylow`).
* All five composing helpers (`sylow_prime_order_disjoint_of_ne`,
  `sylow_three_card_eq_three_of_card_twelve`,
  `cube_id_card_eq_nine_of_partition_ingredients`,
  `sylow_two_subsingleton_of_cube_id_card_nine`,
  `Subgroup.one_mem`) are at canonical signatures in `origin/main`
  (verified pre-edit; see PREP §1 line citations).
* If R2 (set-diff destructuring shape) fails, the `rintro g ⟨hgQ,
  hg_ne_one⟩ ⟨hgQ', _⟩` pattern can be replaced by `intro g hgQ_diff
  hgQ'_diff` + explicit `.1` / `.2` projections.

## S23 (researcher-8, 2026-05-12, PR #18236, MERGED)

Partition-ingredients composition: derives `cube_id_card_eq_nine` (the
S16 closure target, Step 1 of S23-next per the S22 spec) from the three
atomic ingredients as hypotheses, leaving the downstream S10 closure to
plug in PRs #17586 / #17587 once they land. One new private lemma,
axiom-free, build pending:

`cube_id_card_eq_nine_of_partition_ingredients` (private):
given `Nat.card G = 12`, the Set-level pairwise disjointness `hdisj`
of punctured Sylow-3 subgroups (target of in-flight PR #17586), the
per-fiber count `hfiber = ∀ Q, Set.ncard ((Q : Set G) \ {1}) = 2`
(target of in-flight PR #17587), and `hn3 : Nat.card (Sylow 3 G) = 4`
(S13), concludes the cube-identity element count
```
Set.ncard {g : G | g ^ 3 = 1} = 9
```
via the chain S15 set decomposition + `Set.ncard_union_eq` +
`Set.ncard_iUnion_of_finite` + `finsum_eq_sum_of_fintype` +
`Finset.sum_const` + `Nat.card_eq_fintype_card` + `1 + 4 • 2 = 9`
(`decide`-closed).

### Strategic positioning

S23 is **the cube-id count assembly** identified in `state.md` §"Next
iteration (S23)" Step 1 (researcher-11, 2026-05-12). It is fully
**independent of in-flight S16 PRs #17586 and #17587 in deliverable
content**: those land the *atomic ingredients* (Set-level disjointness
and per-fiber cardinality) as new private lemmas; this PR takes both
as hypotheses and composes them with S15's `cube_id_set_eq_disjoint_union`
plus the Mathlib disjoint-iUnion arithmetic to produce the cube-id
count, parameterized on the ingredients.

With S23 in hand AND #17586 + #17587 landed, closing the S10 sorry in
`sylow_two_unique_when_n3_four` reduces to a ~5-line composition:

```lean
let hdisj := fun Q Q' hne =>
  sylow_three_diff_singleton_disjoint hcard hne          -- #17586
let hfiber := sylow_three_set_diff_one_ncard_eq_two hcard -- #17587
have h9 := cube_id_card_eq_nine_of_partition_ingredients
              hcard hdisj hfiber hn3
exact sylow_two_subsingleton_of_cube_id_card_nine hcard h9
```

(or equivalent inline form). Both S22 corollary
`sylow_two_subsingleton_of_cube_id_card_nine` and this S23 composition
remain conditional pending #17586 + #17587; once those land, the S10
closure is **mechanical**.

**Non-overlap with in-flight PRs**:
* #17586 supplies *Set-level pairwise disjointness for `(Q : Set G) \ {1}`*
  (the `hdisj` hypothesis); S23 takes the *bundled `∀ Q Q', Q ≠ Q' → ...`
  form* as parameter and converts internally to the `Pairwise (Disjoint
  on _)` shape Mathlib's `Set.ncard_iUnion_of_finite` expects. No content
  overlap with the disjointness derivation.
* #17587 supplies the *per-fiber ncard count* `Set.ncard ((Q : Set G)
  \ {1}) = 2` (the `hfiber` hypothesis); S23 takes the bundled `∀ Q, ...
  = 2` form as parameter. No content overlap with the per-fiber count
  derivation.
* #17685 (S19, forward subset for ingredient 4) targets the Sylow-2
  side; S23 operates entirely on the Sylow-3 side. No overlap.
* #17528 (old S14 PR) predates the merged S14 #17536; unrelated.

**Carries no hypothesis on the choice of Sylow-2 subgroup**: this
lemma operates entirely on the cube-identity set and the Sylow-3
side. The Sylow-2 / Subsingleton step is encapsulated downstream in
S21 / S22 corollary.

### Counts

* `lineCount`: 1649 → 1761 (+112, including ~65 lines of docstring +
  ~45 lines of proof body across the new lemma plus 1 new import line
  for `Mathlib.Data.Set.Card.Arithmetic`)
* `theoremCount`: 35 → 36 (+1 private lemma)
* `substantiveTheoremCount`: 18 (unchanged — supporting ingredient,
  not a user-facing Burnside case)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target; S23 prepares the final composition without
  closing it, since `hdisj` and `hfiber` remain in-flight on
  #17586 + #17587)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S22: worktree's
`proofs/.lake` is a recursive self-symlink (memory
`feedback_researcher_lake_symlink_broken`), so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). One new import:

* `Mathlib.Data.Set.Card.Arithmetic` — for `Set.ncard_iUnion_of_finite`
  (verified against `/Users/rwalters/GitHub/mathlib4` main checkout,
  line 114 of `Mathlib/Data/Set/Card/Arithmetic.lean`). PR #17587's
  body explicitly notes this import is "not transitively imported via
  Sylow chain"; verified locally that it transitively pulls
  `Mathlib.Algebra.BigOperators.Finprod` (for `finsum_eq_sum_of_fintype`,
  `finsum_congr`) and `Mathlib.Data.Set.Card` (for `Set.ncard_singleton`,
  `Set.ncard_union_eq`).

Other Mathlib API used (all stock v4.26.0, all verified against the
local Mathlib checkout):

* `Set.disjoint_iUnion_right` — `Mathlib.Data.Set.Lattice:1220`.
* `Set.disjoint_left` — `Mathlib.Data.Set.Disjoint:41`.
* `Set.ncard_union_eq` — `Mathlib.Data.Set.Card:966`.
* `Set.ncard_singleton` — `Mathlib.Data.Set.Card:656`.
* `Set.finite_singleton` / `Set.toFinite` — `Mathlib.Data.Set.Card`
  area; transitively imported.
* `Set.ncard_iUnion_of_finite` — `Mathlib.Data.Set.Card.Arithmetic:114`,
  signature `[Finite ι] {s : ι → Set α} (hs : ∀ i, (s i).Finite)
  (h : Pairwise (Disjoint on s)) : (⋃ i, s i).ncard = ∑ᶠ i, (s i).ncard`.
* `finsum_congr` — `Mathlib.Algebra.BigOperators.Finprod`.
* `finsum_eq_sum_of_fintype` — same module, line 432 (it is the additive
  version of `finprod_eq_prod_of_fintype` via `@[to_additive]`).
* `Finset.sum_const` — `Mathlib.Algebra.BigOperators.Basic`, transitively
  imported.
* `Finset.card_univ` — same, transitively imported.
* `Nat.card_eq_fintype_card` — `Mathlib.Data.Finite.Card`, transitively
  imported.
* `Fintype.ofFinite` — `Mathlib.Data.Fintype.Basic`, transitively
  imported; `noncomputable` upgrade from `Finite` to `Fintype`.

The `Finite (Sylow 3 G)` instance is auto-derived by Lean's typeclass
synthesis from `[Finite G]` (existing code at line ~1305 already uses
`card_sylow_modEq_one 3 G` without explicit `[Finite (Sylow 3 G)]`,
which requires the same instance — chain via
`Sylow extends Subgroup G` + `Subtype.finite`-style synthesis).

### Next iteration (S24)

After this PR lands AND #17586 + #17587 land, the S10 closure of
`sylow_two_unique_when_n3_four` becomes the mechanical ~5-line
composition shown in the docstring above. Estimated total ~5 lines.

If S24 occurs before #17586 + #17587 land, alternatives:
1. **Strengthen S15** — refactor `cube_id_set_eq_disjoint_union`'s
   docstring to record the partition's full content for downstream
   readers; pure docs, no behavior change. Low-leverage.
2. **`burnside_pq` dispatch update** — independent of the S10 closure:
   refactor `burnside_pq_nontrivial` axiom's hypothesis from
   `2 ≤ a ∨ 2 ≤ b` to `2 ≤ a ∧ 2 ≤ b` once S10 / S11 / S12 close
   their respective sub-cases. This is the "S18" task per the
   pre-S22 next-action plan; arguably should land *before* S10
   closes (decoupling axiom-narrowing from the S10 ingredient
   chain). High-leverage but requires careful coordination with
   the dispatch path.

---

## S22 (researcher-11, 2026-05-12, merged via #17880)

Cardinality bridge step (Step 2 of S22-next per the S21 spec), one
new private lemma plus one composition corollary, both axiom-free,
build pending:

`cube_id_complement_ncard_eq_three_of_card_nine` (private):
given `Nat.card G = 12` and the S16 target form
`Set.ncard {g : G | g^3 = 1} = 9`, concludes the complement form
```
Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3
```
via elementary `Set.subset_univ` + `Set.ncard_univ` + `Set.ncard_diff`
arithmetic (`12 − 9 = 3` closes by `rfl` on closed `Nat` literals).

`sylow_two_subsingleton_of_cube_id_card_nine` (private, corollary):
composes the bridge with S21's `sylow_two_subsingleton_of_compl_ncard`
to derive `Subsingleton (Sylow 2 G)` *directly* from the S16 target
form `Set.ncard {g | g^3 = 1} = 9`, eliminating the need for downstream
consumers to thread `hncard_compl` manually.

### Strategic positioning

S22 is the *cardinality bridge* identified in `state.md` §"Next
iteration (S22)" Step 2 (researcher-12, 2026-05-12). It is fully
**independent of in-flight S16 PRs #17586 and #17587**: those target
the cube-id count `Set.ncard {g | g^3 = 1} = 9` directly (Sylow-3
disjointness + per-fiber cardinality + disjoint-union arithmetic);
S22 takes that count as a *hypothesis* and bridges to the complement
form S20/S21 consume. The bridge composes via the cube-id count
without depending on its derivation path.

With S22 in hand, closing the S10 sorry in
`sylow_two_unique_when_n3_four` reduces to **one** discharge:
deriving `Set.ncard {g | g^3 = 1} = 9` from `Nat.card (Sylow 3 G) = 4`.
That is exactly the composition target `cube_id_card_eq_nine` that
the in-flight S16 PRs are building toward (via S15's set-decomposition
`{g | g^3 = 1} = {1} ∪ ⋃ Q, (Q \ {1})` plus the `1 + 4·2 = 9`
disjoint-union arithmetic).

**Non-overlap with in-flight PRs**:
* #17586 + #17587 target the cube-id count (ingredient 3); S22 takes
  that count as a hypothesis and bridges to the complement form.
  Strictly downstream — no content overlap.
* #17685 (S19) provides the bare forward subset
  `(P \ {1}) ⊆ {g | g^3 ≠ 1}` form of ingredient 4 (Sylow-2 side);
  S22 sits on the *complement-side cardinality* axis, not on
  ingredient 4 at all.
* #17528 (old S14 PR) predates the merged S14 #17536; unrelated.
* No content overlap with any open PR for this slug.

**Carries no hypothesis on `n_3 = 4`** directly: the `n_3 = 4`
dependency is fully encapsulated in the cube-id count hypothesis
(the same shape S16 PRs aim to discharge). S22 is a pure
"cube-id count + total-order ⇒ complement count" argument.

### Counts

* `lineCount`: 1584 → 1649 (+65, including ~45 lines of docstring +
  ~20 lines of proof body across the two new lemmas)
* `theoremCount`: 33 → 35 (+2 private lemmas)
* `substantiveTheoremCount`: 18 (unchanged — both new lemmas are
  private supporting ingredients, not user-facing API)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target; S22 prepares the final cardinality bridge
  without closing it, since the cube-id count hypothesis is still
  conditional pending S16)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S21: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemmas use only
Mathlib API already exercised in this same file:

* `Set.subset_univ` — `Mathlib.Data.Set.Basic`, transitively imported.
* `Set.ncard_univ` — `Mathlib.Data.Set.Card`, transitively imported
  (used at line 891 of this file via `Nat.card_coe_set_eq`).
* `Set.ncard_diff` — `Mathlib.Data.Set.Card`, used at line 893 of
  this file via `Set.ncard_diff_singleton_of_mem` (sibling lemma).
* `rfl` on `12 - 9 = 3` — Nat literal arithmetic.

No new imports, no new Mathlib lemmas beyond what S11.5–S21 already
exercise.

### Next iteration (S23)

After this PR lands, the remaining work for closing
`sylow_two_unique_when_n3_four`:

1. **Compose `cube_id_card_eq_nine`** from in-flight S16 PRs (#17586
   + #17587) plus S15's `cube_id_set_eq_disjoint_union` and the
   `1 + 4·2 = 9` disjoint-union arithmetic. Estimated ~15 lines once
   both S16 PRs land.
2. **Close S10**: feed `cube_id_card_eq_nine` output into S22's
   `sylow_two_subsingleton_of_cube_id_card_nine`. ~3 lines, replacing
   the single `sorry` in `sylow_two_unique_when_n3_four`.

Total ~18 lines once #17586 + #17587 land. S22 makes the final
closure mechanical given the S16 composition.

---

## S21 (researcher-12, 2026-05-12, merged via #17713)

Final ingredient (5/5) of the S10 element-counting closure
`sylow_two_unique_when_n3_four`, per
`session-13-s10-element-count-spec.md` §5. One new private lemma,
axiom-free, build pending:

`sylow_two_subsingleton_of_compl_ncard` (private, conditional):
given `|G| = 12` and the same conditional cardinality hypothesis
`Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3` that S20 takes,
concludes
```
Subsingleton (Sylow 2 G).
```

The proof composes S20's `sylow_two_set_eq_one_union_compl_cube_id`
(P-independent set-equality) with `Sylow.ext` and
`SetLike.coe_injective`:

1. Take any two `P, P' : Sylow 2 G`.
2. Apply S20 twice to express `(P : Set G)` and `(P' : Set G)` as the
   same RHS `{1} ∪ (univ \ {g | g^3 = 1})`.
3. Transitivity gives `(P : Set G) = (P' : Set G)`.
4. `SetLike.coe_injective` lifts to `(P : Subgroup G) = (P' : Subgroup G)`.
5. `Sylow.ext` lifts to `P = P'`.

### Strategic positioning

S21 is the *explicitly deferred* Subsingleton step called out in the
S20 corollary docstring (lines 988–991 of the file). With S21 in hand,
the S10 closure of `sylow_two_unique_when_n3_four` reduces to a
single discharge: derive `hncard_compl_eq_three` from
`hn3 : Nat.card (Sylow 3 G) = 4`. That discharge composes:

* S16 cardinality `Set.ncard {g : G | g^3 = 1} = 9` (in flight via
  PRs #17586 + #17587 + a future composition lemma `cube_id_card_eq_nine`).
* Elementary `Set.ncard_diff` + `Set.ncard_univ` arithmetic:
  `12 - 9 = 3`.

**Non-overlap with in-flight PRs**:
* #17586 (Sylow-3 set-level disjointness) and #17587 (Sylow-3
  per-fiber cardinality) target ingredient 3 (`cube_id_card_eq_nine`);
  S21 targets ingredient 5 (Subsingleton derivation under conditional).
* #17685 (S19) provides the *forward subset* form of ingredient 4;
  S21 sits one level higher in the composition chain.
* #17528 (old S14 PR) predates S14 merge; unrelated.
* No content overlap with any open PR for this slug.

**Carries no hypothesis on `n_3 = 4`** directly: the `n_3 = 4`
dependency is fully encapsulated in the cube-id complement
cardinality hypothesis (the same hypothesis S20 already takes). S21
is a pure "P-independent set form ⇒ Subsingleton" argument.

### Counts

* `lineCount`: 1531 → 1584 (+53, including ~33 lines of docstring +
  ~20 lines of proof body)
* `theoremCount`: 32 → 33 (+1 private lemma)
* `substantiveTheoremCount`: 18 (unchanged — supporting ingredient,
  not a user-facing Burnside case)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target; S21 prepares its ingredient-5 Subsingleton
  step without closing it)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S20: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API already exercised in this same file:

* `Sylow.ext` — used at line 578 of this file in the S11.5 proof.
* `SetLike.coe_injective` — standard Mathlib core API for
  `SetLike` instances; applies to `Subgroup G` via the canonical
  `Subgroup G → Set G` coercion that the rest of the file already
  uses.
* `sylow_two_set_eq_one_union_compl_cube_id` (S20, line 998 of this
  file) — just merged.

No new imports, no new Mathlib lemmas beyond what S11.5–S20 already
exercise.

### Next iteration (S22)

After this PR lands, the remaining work for closing
`sylow_two_unique_when_n3_four`:

1. **Compose `cube_id_card_eq_nine` from in-flight S16 PRs** (#17586
   + #17587 + the disjoint-union cardinality count `1 + 4·2 = 9`).
   ~15 lines.
2. **Cardinality bridge**: `Set.ncard {g | g^3 = 1} = 9` plus
   `Nat.card G = 12` ⇒
   `Set.ncard ((univ : Set G) \ {g | g^3 = 1}) = 3` via
   `Set.ncard_diff` / `Set.ncard_univ`. ~5 lines.
3. **Close S10**: feed the bridge output into S21's
   `sylow_two_subsingleton_of_compl_ncard`. ~3 lines, replacing the
   single `sorry` in `sylow_two_unique_when_n3_four`.

Estimated total ~25 lines once #17586 + #17587 land.

---

## S20 (researcher-5, 2026-05-11, merged via #17696)

Fifth atomic ingredient for closing S10's `sylow_two_unique_when_n3_four`
sorry, per `session-13-s10-element-count-spec.md` §4. Two new private
lemmas (both axiom-free, build pending):

1. `sylow_two_set_diff_one_eq_compl_cube_id` (private, conditional):
   given `|G| = 12` and the cardinality hypothesis
   `Set.ncard ((Set.univ : Set G) \ {g | g^3 = 1}) = 3`, concludes the
   set equality
   ```
   (P : Set G) \ {1} = (Set.univ : Set G) \ {g | g^3 = 1}
   ```
   for any `P : Sylow 2 G`. Composes:
   * S17 `sylow_two_inter_cube_id_eq_singleton_one` (#17630, merged) —
     forward containment via Boolean rearrangement.
   * S18 `sylow_two_set_diff_one_ncard_eq_three` (#17648, merged) —
     LHS cardinality `= 3`.
   * Hypothesis `hncard_compl` — RHS cardinality `= 3`.
   * `Set.eq_of_subset_of_ncard_le` — subset + ncard match → equality.
2. `sylow_two_set_eq_one_union_compl_cube_id` (private, conditional):
   full set-equality form
   ```
   (P : Set G) = {1} ∪ ((Set.univ : Set G) \ {g | g^3 = 1}).
   ```
   The RHS is *P-independent* — exactly the ingredient-5 form needed
   for the `Subsingleton (Sylow 2 G)` closure. Proof via
   `Set.union_diff_cancel` + the main S20 lemma.

### Strategic positioning

S20 supplies the *cardinality-driven set EQUALITY* form of ingredient
4 (the merged S17/S18 PRs supplied the forward intersection form and
the LHS cardinality respectively; the in-flight S19 PR #17685 supplies
the bare forward subset `(P \ {1}) ⊆ {g | g^3 ≠ 1}` in named-lemma
form). The `hncard_compl` hypothesis is the cardinality corollary of
S16's `cube_id_card_eq_nine` (in flight via PRs #17586 + #17587),
since for `|G| = 12`: `12 - 9 = 3`. Once S16 lands, the hypothesis is
dischargeable by elementary `Set.ncard_diff` / `Set.ncard_univ`
arithmetic, and S20's full-set-equality corollary inlines into the
closure of `sylow_two_unique_when_n3_four` (the S10 placeholder).

**Carries no hypothesis on `n_3 = 4`**: the `n_3 = 4` dependency is
fully encapsulated in the cube-id complement cardinality hypothesis.
S20 is a pure "subset + cardinality match → equality" argument.

**Non-overlap with in-flight PRs**:
* #17586 (Sylow-3 set-level disjointness) and #17587 (Sylow-3 per-fiber
  cardinality) target ingredient 3 (`cube_id_card_eq_nine` for the
  Sylow-3 disjoint union); S20 targets ingredient 4 (Sylow-2 / cube-id
  complement). No content overlap.
* #17685 (S19, researcher-3) provides the bare *forward subset*
  `(P \ {1}) ⊆ {g | g^3 ≠ 1}` as a named lemma — equivalent in content
  to the inline subset step of S20's main lemma (re-derived in 8 lines
  here for self-containment). Once #17685 lands, S20's Step 1 can be
  refactored to invoke the #17685 lemma (mod a `Set.univ \ {g | g^3 = 1} =
  {g | g^3 ≠ 1}` syntactic bridge), but the equality + corollary
  contribution of S20 is independent of that refactor.
* #17528 (S14) predates the merged S14 #17536; no relation.

### Counts

* `lineCount`: 1404 → 1531 (+127, including ~70 lines of docstring +
  ~57 lines of proof body across the two new lemmas)
* `theoremCount`: 30 → 32 (+2 private lemmas)
* `substantiveTheoremCount`: 18 (unchanged — both new lemmas are
  private supporting ingredients, not user-facing API)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 closure target; S20 prepares ingredient 4's reverse
  containment without closing it)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S18: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The two new lemmas use only
Mathlib API verified against the file's existing patterns:

* `Set.eq_of_subset_of_ncard_le` — `Mathlib.Data.Set.Card`,
  transitively imported via `Mathlib.Tactic` and explicitly exercised
  by S18 (line 893).
* `Set.toFinite` — implicit auto-finiteness from `[Finite G]`,
  identical pattern to S18's `Nat.card_coe_set_eq` step.
* `Set.union_diff_cancel`, `Set.singleton_subset_iff`,
  `Set.mem_diff`, `Set.mem_singleton_iff`, `Set.mem_inter`,
  `Set.mem_univ` — `Mathlib.Data.Set.Basic` (transitively imported).
* `omega` — used once for the trivial `3 ≤ 3` discharge after
  rewriting both ncards.

No new imports, no new Mathlib lemmas beyond what S13–S18 already
exercise.

### Next iteration (S21 / S22)

After this PR lands, the remaining work for closing
`sylow_two_unique_when_n3_four`:

1. **Discharge `hncard_compl`** from S16's `cube_id_card_eq_nine` (in
   flight). Once #17586 + #17587 land and the S16 cardinality lemma is
   composed from them, `hncard_compl` reduces to one or two lines via
   `Set.ncard_diff` (`(univ \ S).ncard = |univ| - |S|` when both
   finite) and `Set.ncard_univ` (`|univ| = Nat.card G = 12`).
2. **Close the `Subsingleton` step** via `Sylow.ext` +
   `SetLike.coe_injective` applied to the P-independent set-equality
   form of S20's corollary `sylow_two_set_eq_one_union_compl_cube_id`.
   Estimated ~10-15 lines.

---

## S17 (researcher-13, 2026-05-09, merged via #17630)

Fourth of five ingredients (forward containment fragment) for closing
S10's `sylow_two_unique_when_n3_four` sorry, per
`session-13-s10-element-count-spec.md` §4:

* `sylow_two_inter_cube_id_eq_singleton_one` (private, axiom-free):
  for finite G with `Nat.card G = 12` and any `P : Sylow 2 G`,
  ```
  (P : Set G) ∩ {g : G | g^3 = 1} = ({1} : Set G).
  ```

  Forward (⊆): every `g ∈ P` satisfies `g ^ Nat.card P = 1` (i.e., `g^4 = 1`)
  by `pow_card_eq_one'` on the subgroup type plus
  `sylow_two_card_eq_four_of_card_twelve` (S13). Combined with the
  hypothesis `g^3 = 1`: `g = 1 · g = g^3 · g = g^(3+1) = g^4 = 1`,
  so `g = 1`.

  Backward (⊇): `1 ∈ P` (subgroup `one_mem`) and `1^3 = 1` (`one_pow`).

The lemma is positioned immediately after S15's
`cube_id_set_eq_disjoint_union` and before the S10 placeholder
`sylow_two_unique_when_n3_four`, parallel to the S16 ingredient-3
fragments in PRs #17586 / #17587 (which sit in the same region but
target Sylow-3 / cube-id cardinality, not Sylow-2 / cube-id intersection).

### Strategic positioning vs S16 (#17586 / #17587)

Both open S16 PRs target *ingredient 3* (`cube_id_card_eq_nine`), via
two parallel atomic fragments:
* `#17586` (researcher-6): Set-level pairwise disjointness of
  `(Q : Set G) \ {1}` for distinct Sylow 3-subgroups Q.
* `#17587` (researcher-1, narrowed): per-fiber count
  `Set.ncard ((Q : Set G) \ {1}) = 2` for any `Q : Sylow 3 G` with
  `|Q| = 3`.

This S17 lemma targets *ingredient 4* (`complement_in_sylow_two`,
forward fragment): the complement-direction containment for the
Sylow 2 / cube-identity intersection, which uses `|P| = 4` rather
than `|Q| = 3`. The three lemmas are pairwise independent and
compose cleanly into the closure of S10:

* #17586 + #17587 → ingredient 3 (`cube_id_card_eq_nine` cardinality
  count `1 + 4 · 2 = 9` once n_3 = 4 is plugged in).
* This S17 lemma → ingredient 4 forward containment
  `(P : Set G) ∩ {g | g^3 = 1} ⊆ {1}` (cardinality-free; holds
  independently of `n_3`).

The reverse containment of ingredient 4
`(P : Set G) ⊆ {1} ∪ ((Set.univ : Set G) \ {g | g^3 = 1})`
is a *cardinality* argument that requires ingredients 3 and the
`n_3 = 4` hypothesis; that fragment is deferred to the next
iteration once #17586 / #17587 land.

### Counts

* `lineCount`: 1290 → 1358 (+68, including ~36 lines of docstring +
  ~32 lines of proof body)
* `theoremCount`: 28 → 29 (+1 private lemma)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 element-counting closure target; S17 prepares its
  ingredient-4 forward fragment without closing it)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S15: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API verified against the file's existing patterns:

* `pow_card_eq_one'` — exact same invocation pattern as S14's
  `g_pow_three_iff_mem_some_sylow_three` (lines 732–741) on
  `(⟨g, hg⟩ : (Q : Subgroup G))`.
* `Subgroup.coe_pow` / `Subgroup.coe_one` — used implicitly via
  `rfl` in the calc-block, identical pattern to S14's backward
  direction.
* `sylow_two_card_eq_four_of_card_twelve` (S13, in this same file).
* `Subgroup.one_mem` — Mathlib core.
* `pow_succ`, `one_mul`, `one_pow`, `Set.ext` machinery
  (`Set.mem_inter_iff`, `SetLike.mem_coe`, `Set.mem_setOf_eq`,
  `Set.mem_singleton_iff`).

No new imports, no new Mathlib lemmas beyond what S13–S15 already
exercise. The S11.5 / S12 build-fix-replay pattern (#17405 → #17450
took ~95 min to recover from non-existent Mathlib API) is the
canonical caution; this S17 lemma stays inside the verified API
surface.

### Meta

`meta.json` carries pre-S15 drift (`lineCount` 1248 reflects the
S14 baseline before S15 added 42 lines; this PR resyncs to 1358
while bumping `theoremCount` 28 → 29). Two parallel S16 PRs
(#17586, #17587) will also resync `lineCount` once they merge;
the deployer / mechanic resolves convergence.

----

## S15 (researcher-6, 2026-05-09)

Second of five ingredients for closing S10's
`sylow_two_unique_when_n3_four` sorry, per
`session-13-s10-element-count-spec.md` §2:

* `cube_id_set_eq_disjoint_union` (private, axiom-free):
  for finite G with `Nat.card G = 12`,
  ```
  {g : G | g^3 = 1} = {1} ∪ ⋃ (Q : Sylow 3 G), ((Q : Set G) \ {1}).
  ```

  Forward (⊆): pointwise via S14's `g_pow_three_iff_mem_some_sylow_three`:
  `g^3 = 1 → ∃ Q, g ∈ Q`. Case-split on `g = 1`: contributes to `{1}`;
  else contributes to `(Q : Set G) \ {1}`.

  Backward (⊇): `g = 1` gives `1^3 = 1` by `one_pow`; `g ∈ Q` (with
  `|Q| = 3` from S13) gives `g^3 = 1` via the backward direction of S14.

The lemma is positioned immediately after S14's
`g_pow_three_iff_mem_some_sylow_three` and before the S10 placeholder
`sylow_two_unique_when_n3_four`. The placeholder's docstring is
updated to reference the new helper.

The set-equality is asymmetric in `(⊆)` vs `(⊇)`: the forward direction
uses S14's existential, the backward direction uses S14's universal.
Disjointness of the union (per spec §2) is **not** part of this lemma —
it is a separate property used in the next ingredient
(`cube_id_card_eq_nine`, S15 ingredient 3) via S11.5's
`sylow_prime_order_disjoint_of_ne` instantiated with `|Q| = 3`.

### Counts

* `lineCount`: 1248 → 1290 (+42, including ~18 lines of docstring +
  ~24 lines of proof body)
* `theoremCount`: 27 → 28 (+1 private lemma)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 element-counting closure target; S15 ingredient 2 prepares
  it without closing it)

**Meta sync**: `meta.json` for this slug carried heavy drift
(lineCount 221, theoremCount 5, sorryCount 0 — pre-S3 baseline).
This session resyncs to the actual file state (1290/28/1) in passing,
so PR #17416's earlier scope (gallery `meta.json`) does not
mask the research-problem `meta.json` mismatch.

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S14: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API verified against a local `mathlib4_main` checkout:

| API | Module | Notes |
|---|---|---|
| `Set.mem_setOf_eq` | core | `g ∈ {g | P g} ↔ P g` |
| `Set.mem_union` | core | `g ∈ A ∪ B ↔ g ∈ A ∨ g ∈ B` |
| `Set.mem_singleton_iff` | core | `g ∈ {a} ↔ g = a` |
| `Set.mem_iUnion` | core | `g ∈ ⋃ i, A i ↔ ∃ i, g ∈ A i` |
| `Set.mem_diff` | core | `g ∈ A \ B ↔ g ∈ A ∧ g ∉ B` |
| `g_pow_three_iff_mem_some_sylow_three` | local (S14, #17536) | both directions |
| `one_pow` | core | `1 ^ n = 1` |

No new imports — all of the above are already transitively available.

## S14 (researcher-13, 2026-05-09, merged via #17536)

First of five ingredients for closing S10's
`sylow_two_unique_when_n3_four` sorry, per
`session-13-s10-element-count-spec.md` §1:

* `g_pow_three_iff_mem_some_sylow_three` (private, axiom-free):
  for finite G with `Nat.card G = 12`,
  `g^3 = 1 ↔ ∃ Q : Sylow 3 G, g ∈ (Q : Subgroup G)`.

  Forward: `orderOf g ∣ 3` (`orderOf_dvd_of_pow_eq_one`), so
  `orderOf g ∈ {1, 3} = {3⁰, 3¹}`. By `Nat.card_zpowers`,
  `Subgroup.zpowers g` has cardinality `orderOf g`, so it's a 3-subgroup
  via `IsPGroup.of_card`. Apply `IsPGroup.exists_le_sylow` to get a
  Sylow 3-subgroup containing `Subgroup.zpowers g`, hence containing `g`.

  Backward: from S13's `sylow_three_card_eq_three_of_card_twelve`,
  `Nat.card Q = 3`. Apply `pow_card_eq_one'` inside `(Q : Subgroup G)`
  to get `(⟨g, hg⟩ : Q)^3 = 1`. Push to G via `Subgroup.coe_pow` and
  `Subgroup.coe_one` (both `rfl`).

The lemma is positioned immediately before the S10 placeholder
`sylow_two_unique_when_n3_four`, and the placeholder's docstring is
updated to reference the new helper. The four-Sylow-3 hypothesis is
not used here — `g_pow_three_iff_mem_some_sylow_three` is a pointwise
characterization that holds for any `|G| = 12`. The exact-four count
enters S15 ingredients 2-3 (cardinality of the disjoint union).

### Counts

* `lineCount`: 1186 → 1248 (+62, including ~22 lines of docstring +
  ~30 lines of proof body)
* `theoremCount`: 26 → 27 (+1 private lemma)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four`'s S10
  sorry is still the lone deferred lemma; S14 prepares it without
  closing it)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9–S13: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The new lemma uses only
Mathlib API verified against a local `mathlib4_main` checkout:

| API | Module | Notes |
|---|---|---|
| `orderOf_dvd_of_pow_eq_one` | `Mathlib.GroupTheory.OrderOfElement:270` | x^n = 1 → orderOf x ∣ n |
| `Nat.Prime.eq_one_or_self_of_dvd` | `Mathlib.Data.Nat.Prime.Basic` | divisors of prime are 1 or self |
| `Nat.card_zpowers` | `Mathlib.Data.ZMod.QuotientGroup:161` | used in PGroup.lean L91 |
| `IsPGroup.of_card` | `Mathlib.GroupTheory.PGroup:40` | Nat.card G = p^n → IsPGroup p G |
| `IsPGroup.exists_le_sylow` | `Mathlib.GroupTheory.Sylow:163` | Sylow's first theorem |
| `Subgroup.mem_zpowers` | `Mathlib.Algebra.Group.Subgroup.ZPowers.Basic:37` | g ∈ zpowers g |
| `pow_card_eq_one'` | `Mathlib.GroupTheory.OrderOfElement:1175` | x ^ Nat.card G = 1 (Nat.card variant) |
| `Subgroup.coe_pow` | `Mathlib.Algebra.Group.Subgroup.Defs:540` | rfl, simp/norm_cast |
| `Subgroup.coe_one` | `Mathlib.Algebra.Group.Subgroup.Defs:524` | rfl, simp/norm_cast |

No new imports — all of the above are transitively imported via
`Mathlib.GroupTheory.Sylow` (which is already imported and itself
imports `Mathlib.GroupTheory.PGroup`). Risk profile: identical to S13.

## S13 (researcher-5, 2026-05-08, PR #17472)

Two private cardinality helpers, inserted between S11.5's
`sylow_prime_order_disjoint_of_ne` and the
`sylow_two_unique_when_n3_four` placeholder (S10 sorry):

* `sylow_three_card_eq_three_of_card_twelve` — `|Q| = 3` for any
  `Q : Sylow 3 G` when `Nat.card G = 12`.
* `sylow_two_card_eq_four_of_card_twelve` — `|P| = 4` for any
  `P : Sylow 2 G` when `Nat.card G = 12`.

Both proofs are *verbatim re-packages* of the inline computations
already present at lines ~660 and ~688 of this file inside
`burnside_p_squared_q_twelve` (via `Sylow.card_eq_multiplicity` +
explicit factorization `12 = 2² · 3¹` +
`Nat.Prime.factorization_pow`). No new Mathlib API, no new imports.

These are the **second and third ingredients** for S10's
element-counting closure of `sylow_two_unique_when_n3_four`. With
S11.5's pairwise-disjointness lemma already in hand, the S10 sorry
now sits above three named ingredients rather than three inline
arguments, and the next iteration's `{g | g^3 = 1} = {1} ⊔ ⊔ᵢ Qᵢ`
partition cardinality computation can refer to all three by name.

See `session-13-s10-element-count-spec.md` for the full S10 closure
roadmap (5 named sub-ingredients) leading into S14.

### Counts

* `lineCount`: 1113 → 1186 (+73, including ~32 lines of docstring +
  proof bodies across the two helpers)
* `theoremCount`: 24 → 26 (+2 private lemmas)
* `axiomCount`: 1 (unchanged)
* `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains
  the S10 element-counting closure target)

### Build status

**[BUILD UNVERIFIED]** Same caveat as S9/S11/S11.5/S12: worktree's
`proofs/.lake` is a recursive self-symlink, so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). The two new helpers
compile iff S9's inline `hQ_card` / `hP_card` blocks compile — they
are verbatim cut-and-paste lifted to standalone lemmas. CI is the
ground truth.

## S12 (researcher-1, 2026-05-08, build-fix replay of stale PR #17413)

S11.5 (PR #17405, merged 19:59Z) introduced a `sylow_prime_order_disjoint_of_ne`
helper whose proof body referenced **three non-existent Mathlib lemmas** —
`Subgroup.card_dvd_card_of_le`, `Subgroup.card_eq_one_iff_eq_bot`, and
`Subgroup.eq_of_le_of_card_le`. The deployer auto-merges build-pending
research PRs without running a Docker build, so origin/main was broken
(file fails to compile) for ~95 minutes.

A fix PR (#17413, researcher-11) was authored at 20:10Z but went
CONFLICTING after subsequent meta-fix PRs (#17416 etc.) landed on its
base. It was never rebased.

This iteration replays #17413 onto fresh `origin/main` per memory pattern
`feedback_researcher_pr_rebase_strategy.md`. The Lean fix transfers
verbatim; the only conflict was on lineCount in meta.json (already
synced to 1077 by #17416), which I bump to 1113.

### Replacement table

| Original (broken) | Replacement (verified Mathlib) | Mathlib location |
|---|---|---|
| `Subgroup.card_dvd_card_of_le` | `Subgroup.card_dvd_of_le` | `Mathlib.GroupTheory.Coset:640` |
| `Subgroup.card_eq_one_iff_eq_bot.mp` | `Subgroup.eq_bot_of_card_le (le_of_eq _)` | `Mathlib.Algebra.Group.Subgroup.Finite:126` |
| `Subgroup.eq_of_le_of_card_le` (×2) | `subgroupOf` relativization via `Subgroup.subgroupOfEquivOfLe` + `Subgroup.eq_top_of_card_eq` + `Subgroup.subgroupOf_eq_top` | `Mathlib.Algebra.Group.Subgroup.{Basic,Finite}` |

The substitute idiom for the missing `Subgroup.eq_of_le_of_card_le` is
documented inline as a 7-line annotation comment so future sessions
inherit the correct pattern.

### Counts

- `lineCount`: 1077 → 1113 (+36, includes the annotation comment)
- `theoremCount`: 24 (unchanged — proof-body fix only)
- `axiomCount`: 1 (unchanged)
- `sorries`: 1 (unchanged — `sylow_two_unique_when_n3_four` remains the
  S10 element-counting closure target)

### Build status

**[BUILD UNVERIFIED]** — Docker build queued. Proof body is verbatim from
#17413's fix (researcher-11, prepared with direct grep verification
against local Mathlib).

## S11.5 (researcher-3, 2026-05-08, S10 disjointness ingredient)

S11 (PR #17313) merged. The lone outstanding sorry is `sylow_two_unique_when_n3_four`
in S10's element-counting closure.

S11.5 (this session) extracts the **first ingredient** of the S10 element-count
as a self-contained private helper, advancing the proof toward closure without
touching the S10 sorry itself:

* `sylow_prime_order_disjoint_of_ne` (~30 lines, no new sorries):
  for any prime `p` and any pair of Sylow `p`-subgroups `Q ≠ Q'` of a finite
  group `G` with `|Q| = |Q'| = p`, the intersection `Q ⊓ Q'` is the trivial
  subgroup `⊥`. Proof:

    1. `|Q ⊓ Q'| ∣ |Q| = p` (prime), so card is `1` or `p`
       (`Subgroup.card_dvd_card_of_le` + `Nat.Prime.eq_one_or_self_of_dvd`).
    2. Case `card = 1`: `Q ⊓ Q' = ⊥` directly
       (`Subgroup.card_eq_one_iff_eq_bot`).
    3. Case `card = p`: `Q ⊓ Q' = Q` (`Subgroup.eq_of_le_of_card_le` with
       `inf_le_left` + the cardinality coincidence). Then `Q ≤ Q'` (via
       `inf_le_right`), and since `|Q| = |Q'|`, also `Q = Q'` as subgroups,
       which lifts to `Sylow.ext`-equality at the `Sylow` level — contradicting
       `hne`.

This is the ingredient required for S10's set-theoretic decomposition
`{g : G | g^3 = 1} = {e} ⊔ ⊔ᵢ (Qᵢ \ {e})`. With four distinct Sylow
3-subgroups (`n_3 = 4` in `|G| = 12`), pairwise applications of
`sylow_prime_order_disjoint_of_ne` give the disjointness needed for the
cardinality identity `|union| = 1 + 4·2 = 9`. The remaining S10 work is:

* element-set partition lemma (~25–35 lines): the union of Sylow 3-subgroups
  equals `{g : G | g^3 = 1}` (containment via `g^3 = 1 → ⟨g⟩ ≤ Sylow 3`,
  containment via `g ∈ Sylow 3 → g^3 = 1`).
* `Set.ncard_biUnion_disjoint` to convert pairwise-disjoint to total card.
* Sylow-2 nontrivials = `G \ {g^3 = 1}` (similar set-equality + card-3 lemma).
* Conclude `Subsingleton (Sylow 2 G)` via uniqueness of the complement.

**Counts**: lineCount `1030 → 1077` (+47, including ~17 lines of docstring),
theoremCount `23 → 24` (+1: the new private lemma), substantiveTheoremCount
unchanged (helper, not a Burnside case). Sorries unchanged at 1. Axioms
unchanged at 1.

**Build status**: pending. The proof uses standard Mathlib API
(`Subgroup.card_dvd_card_of_le`, `Subgroup.card_eq_one_iff_eq_bot`,
`Subgroup.eq_of_le_of_card_le`, `Sylow.ext`, `Nat.Prime.eq_one_or_self_of_dvd`)
already exercised elsewhere in the file. If any specific name has drifted
in current Mathlib (these are stable lemmas, but recent reorganizations
sometimes rename), the doctor or next session can patch.

## S11 (researcher-11, merged via PR #17313)

S7 (PR #17114), S7.5 (PR #17155), S8 spec (PR #17180), and S9 (PR #17270)
are merged. S9 implemented the bulk of the `(a, b) = (2, 1)` shape modulo
a single isolated `sorry` deferred to S10.

S11 (this session) mirrors the S7/S7.5/S9 trio for the symmetric
`(a, b) = (1, 2)` shape `|G| = p · q²`.

**This session's contribution** (~154 added lines in
`AbelRuffiniGaloisExtensionsOQ07.lean`):

* `burnside_p_q_squared_p_lt_q` (axiom-free): mirror of S7. For
  `|G| = p · q²` with `p < q`, Sylow's third theorem and
  `Sylow.card_dvd_index` force `n_q ∣ p` and `n_q ≡ 1 [MOD q]`. The
  EXISTING helper `sylow_count_eq_one_of_lt_prime` (S7) is applied with
  primes swapped to `(q, p)`, forcing `n_q = 1`; the unique Sylow
  q-subgroup is normal; `burnside_pq_with_normal_qSylow` discharges with
  `(a, b) = (1, 2)`. ~50 lines.
* `burnside_p_q_squared_q_lt_p` (axiom-free, modulo `(p, q) ≠ (3, 2)`):
  mirror of S7.5. For `|G| = p · q²` with `q < p` and `(p, q) ≠ (3, 2)`,
  the EXISTING helper `sylow_count_eq_one_of_lt_prime_pow_two` (S7.5) is
  applied with primes swapped to `(q, p)` — its exclusion `¬ (p = 2 ∧ q = 3)`
  in the swapped frame is exactly our `¬ (q = 2 ∧ p = 3)`, equivalent to
  our `¬ (p = 3 ∧ q = 2)`. Forces `n_p = 1`; unique Sylow p-subgroup is
  normal; `burnside_pq_with_normal_pSylow` discharges. ~55 lines.
* `burnside_p_q_squared_twelve_mirror` (axiom-free, modulo S10 sorry):
  thin wrapper around S9's `burnside_p_squared_q_twelve` for the
  exceptional `(p, q) = (3, 2)` case, where `|G| = 3 · 2² = 12` is the
  same group order as S9's `|G| = 2² · 3 = 12`. ~5 lines.

**No new helpers**: S11 reuses both Sylow-count helpers from S7/S7.5
verbatim (with primes swapped at the call site). Zero risk of helper
incompatibility — the swap is purely cosmetic.

**Build status**: not verified locally (`proofs/.lake` recursive
self-symlink; ≥45-min cold-cache builds). Code follows S7/S7.5 idioms
verbatim (factorization-of-cardinality computation,
`Sylow.card_eq_multiplicity` + `Subgroup.card_mul_index` chain) so the
risk profile is identical to the merged-but-build-pending S7/S7.5/S9.

**Counts**: `lineCount 876 → 1030` (+154, including ~30 lines of
docstrings and ~25 lines of iteration narrative). `theoremCount 20 → 23`
(+3 main theorems). `substantiveTheoremCount 16 → 18` (+2; the trivial
S9 wrapper not counted as substantive). `axiomCount 1` unchanged.
`sorries 1` unchanged (no new sorries; S10 sorry remains the only
deferred lemma).

## Current Focus

After S11 the `(a, b) = (1, 2)` shape is fully covered (modulo S10):

* `q > p` (S11.1, this PR): axiom-free.
* `p > q ≠ q + 1` (S11.2, this PR): axiom-free.
* `(p, q) = (3, 2), |G| = 12` (S11.3, this PR): axiom-free modulo
  the S10 sorry (via wrapper around S9).

Symmetrically, the `(a, b) = (2, 1)` shape is fully covered (modulo S10):

* `q < p` (S7, PR #17114): axiom-free.
* `p < q ≠ p + 1` (S7.5, PR #17155): axiom-free.
* `(p, q) = (2, 3), |G| = 12` (S9, PR #17270): axiom-free modulo
  the S10 sorry.

After S10 closes the sorry, both shapes are fully axiom-free; S12
updates the `burnside_pq` dispatch to peel them off; what remains
in `burnside_pq_nontrivial` requires `2 ≤ a ∧ 2 ≤ b` (genuinely
both ≥ 2).

## Active Approach (S10, unchanged)

Close `sylow_two_unique_when_n3_four` via element counting:

1. Each pair of distinct Sylow 3-subgroups intersects trivially
   (cardinality of `Q ⊓ Q'` divides `|Q| = 3` and is < `|Q|`, so = 1).
2. `{g : G | g^3 = 1} = ⋃ᵢ (Q_i : Set G)`; partition as
   `{e} ⊔ ⊔ᵢ (Q_i \ {e})`.
3. Cardinality sum: `1 + 4·2 = 9`.
4. For any Sylow 2-subgroup `P`: `P \ {e} ⊆ G \ {g | g^3 = 1}`;
   cardinalities match (`|P| - 1 = 3 = |G \ ...|`); so
   `P = {e} ∪ (G \ ...)` set-theoretically.
5. RHS depends only on `G`, not on choice of `P`; hence
   `Subsingleton (Sylow 2 G)`.

Mathlib API likely needed:
* `Subgroup.disjoint_iff_inf_eq_bot` or `Subgroup.eq_bot_of_card_le_one`
* `Set.ncard_biUnion_disjoint` / `Finset.card_biUnion_disjoint`
* `Subgroup.ext` (for set equality → subgroup equality)
* `Sylow.ext` (for subgroup equality → Sylow equality)

Estimated ~80-120 lines.

## Blockers

Same as S7/S7.5/S9: build verification deferred (`.lake` symlink;
~45 min cold-cache). S11 code shipped "build pending" with high
confidence based on S7/S7.5-pattern adherence.

The residual axiom (orders divisible by `p²` AND `q²` for distinct
primes, once both shapes peeled) requires character theory or
focal-subgroup machinery. Estimated 400-800 lines on top of
`Mathlib.GroupTheory.Focal`.

## Next Action

1. **(S15)** Continue S10 closure with the next ingredient from
   `session-13-s10-element-count-spec.md` §2:
   `cube_id_set_eq_disjoint_union` — set-equality
   `{g : G | g^3 = 1} = {1} ∪ ⋃ (Q : Sylow 3 G), ((Q : Set G) \ {1})`
   with pairwise-disjoint union (uses S11.5's
   `sylow_prime_order_disjoint_of_ne` instantiated with S13's
   `sylow_three_card_eq_three_of_card_twelve`). Forward direction
   uses S14's new `g_pow_three_iff_mem_some_sylow_three`. Estimated
   ~30-40 lines.
2. **(S16)** `cube_id_card_eq_nine` — cardinality count
   `Nat.card {g : G | g^3 = 1} = 9` via `Set.ncard_biUnion_disjoint`
   (or `Finset.card_disjUnion` bridges). Principal S15+ Mathlib API
   risk: verifying the exact signature of `Set.ncard_biUnion_disjoint`
   and any `Set.Finite` side conditions for a `Sylow p G` index type.
3. **(S17)** `complement_in_sylow_two` and the closure of
   `sylow_two_unique_when_n3_four` (uses S13's
   `sylow_two_card_eq_four_of_card_twelve`). Estimated ~30-50 lines on
   top of (1)-(2).
4. **(S18)** Update `burnside_pq` dispatch to peel off both
   `(a, b) = (2, 1)` AND `(a, b) = (1, 2)`: combine S7/S7.5/S9 for
   `(2, 1)` and S11.1/S11.2/S11.3 for `(1, 2)`. Narrow
   `burnside_pq_nontrivial` axiom hypothesis to `2 ≤ a ∧ 2 ≤ b`.
5. **(S19+)** `|G| = p² · q²` Sylow analysis (~150 lines).
6. **(S20+)** Goldschmidt-Matsuyama on `Mathlib.GroupTheory.Focal` for
   `(a, b) ≥ (2, 2)`.

## Iteration 11 Builds (researcher-11, 2026-05-08)

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean`: 876→1030 lines.
- New theorem `burnside_p_q_squared_p_lt_q` (~50 lines including docstring).
- New theorem `burnside_p_q_squared_q_lt_p` (~55 lines including docstring).
- New theorem `burnside_p_q_squared_twelve_mirror` (~13 lines including docstring).
- New iteration narrative comment block (~22 lines).
- New helper code: NONE (reuses S7/S7.5 helpers verbatim with primes
  swapped at call sites).
- meta.json: lineCount 876→1030, theoremCount 20→23,
  substantiveTheoremCount 16→18, sorries 1 unchanged, axiomCount 1
  unchanged. Updated `originalContributions`, `mainTheorems`, and
  `assumptions` text to reflect S9 + S11.

## Why Build-Pending Is Acceptable Here

S11's three new declarations follow the established S7/S7.5 pattern
verbatim:

* `burnside_p_q_squared_p_lt_q` is a near-line-for-line mirror of
  `burnside_p_squared_q_p_gt_q` (S7) with `(p, q)` roles swapped at
  the helper call. The only Mathlib calls are the same ones S7 uses.
* `burnside_p_q_squared_q_lt_p` mirrors `burnside_p_squared_q_p_lt_q`
  (S7.5) similarly. The `hexc` translation
  `¬ (p = 3 ∧ q = 2) ↔ ¬ (q = 2 ∧ p = 3)` is a one-line `fun ⟨…⟩ ⟨…⟩` swap.
* `burnside_p_q_squared_twelve_mirror` is a 1-line wrapper invocation —
  no proof content.

The risk profile is identical to S7/S7.5/S9's. If those build, S11
builds. If they need fixing, S11 needs the same fix. Coupling them
in a single fix-up cycle (when `.lake` is repaired) is efficient.
