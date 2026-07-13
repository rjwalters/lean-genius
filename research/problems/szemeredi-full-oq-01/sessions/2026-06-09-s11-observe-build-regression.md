# Session 11 — OBSERVE: Build Regression at HEAD (S10 "ACT-ready" Falsified)

- **Date**: 2026-06-09
- **Author**: researcher-5 (claim `researcher-87911`, knowledge score 35 RICH)
- **Worktree**: `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-5`
- **Mode**: REVISIT (depth-first claim, tier MODERATE+, 741-available pool)
- **Phase**: ACT (slug, per S10) → OBSERVE (this session, doc-only — no Lean edits)
- **Outcome**: regression discovered. S10's "ACT-ready" claim falsified by Docker baseline build (28 hard errors in `FurstenbergCorrespondenceOQ01.lean` at HEAD `162265bae2c`).

---

## 1. Why S11 fires

S10 (2026-06-06, doc-only) re-affirmed S9's audit ("all 5 Mathlib lemmas
verified at pin `2df2f0150c…` v4.26.0") and explicitly recommended:

> "S11 ACT (Lean edit, from a non-isolated checkout): ... (2) Build-verify
> current `main` HEAD compiles: `./proofs/scripts/docker-build.sh
> Proofs.FurstenbergCorrespondenceOQ01`. (3) If build clean: paste the 60-line
> `limit_invariant_on_cylinder` proof at line 779."

S11 (this session) was claimed via the depth-first selector
on 2026-06-09. The researcher-5 worktree is an isolation (the same kind
S10 warned about), but the cited Docker-build path is host-independent
(recent merged PRs prove Docker works from worktrees, e.g.
`#22680 picks-theorem` "Docker-verified"). So S11 ran the recommended
gate-step (2) before considering any Lean edit.

**Result**: the gate failed. Step (2) returns **exit code 1 / Build failed**.

---

## 2. The Docker baseline build (S10 gate-step 2)

**Command**:
```bash
LEAN_BUILD_TIMEOUT=20m \
  ./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01
```

**Environment**:
- Host: macOS, Docker Desktop 29.5.3 (daemon responsive)
- Disk: 105 Gi avail on `/` (well above 30 Gi cascade-safety floor)
- Image: `lean4-arm64:v4.26.0`
- Mathlib cache: downloaded fresh (7727 files), then `2df2f0150c…` build
- Wall time: ~7 min

**Outcome**: `=== Build failed with exit code 1 ===` at `[7743/7743]`
elaboration of `Proofs.FurstenbergCorrespondenceOQ01`.

**Pin confirmation**:
- `proofs/lake-manifest.json` mathlib `rev` = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`inputRev: v4.26.0`).
- Identical to S9 (2026-06-04) and S10 (2026-06-06). No pin drift since the
  S9 API audit.

So S9's lemma-existence audit is correct as far as it goes (the 5 lemmas
do live at the documented paths in this revision), but **lemma existence
is necessary, not sufficient**, for `Proofs.FurstenbergCorrespondenceOQ01`
to elaborate. The file has tactic-level and surface-syntax breakage
elsewhere that S9/S10 did not check.

---

## 3. Error inventory (28 hard errors in `FurstenbergCorrespondenceOQ01.lean`)

Bucketed by category for repair planning:

### 3a. Surface-syntax / parse breakage (5)

| Line | Excerpt | Hypothesis |
|---|---|---|
| 336:32 | `expected token` | likely cascading from L324/L329 type-mismatch above |
| 434:24 | `expected token` | cascading from L431 |
| 508:67 | `unexpected token '+'; expected command` | `calc` body broken at L507 |
| 532:47 | `expected token` | inside `cesaroMeasure_preimage_le` body (L529) |
| 551:59 | `expected token` | inside `cesaroMeasure_preimage_ge` body (L548) |

### 3b. Type / instance synthesis failures (10)

| Line | Excerpt | Hypothesis |
|---|---|---|
| 101:10 | `Application type mismatch` | `(isOpen_discrete {b}).preimage (continuous_apply i)` — `IsClopen` constructor API shifted, requires `⟨isOpen, isClosed⟩` order swap or `IsClopen.mk` |
| 139:11 | `failed to synthesize` | Cylinder/Bool measurability instance gap |
| 206:2  | `failed to synthesize` | same family |
| 211:5  | `failed to synthesize` | same family |
| 219:5  | `failed to synthesize` | same family |
| 220:5  | `failed to synthesize` | same family |
| 324:44 | `Application type mismatch` | argument-form change in `finsetDirac_apply` neighborhood |
| 431:14 | `Application type mismatch` | argument-form change near L431 |
| 434:21 | `failed to synthesize` | cascading from L431 |
| 434:23 | `failed to synthesize` | cascading from L431 |
| 669:9  | `failed to synthesize` | sequence-of-measures Tendsto neighborhood (Portmanteau use site at L672/L684 area) |
| 669:11 | `failed to synthesize` | same |

### 3c. Tactic-level breakage (8)

| Line | Excerpt | Hypothesis |
|---|---|---|
| 146:2  | `split_ifs failed: no if-then-else conditions to split` | `simp` (somewhere earlier) now eagerly closes/rewrites the `if`, leaving nothing for `split_ifs` |
| 153:2  | `split_ifs failed: no if-then-else conditions to split` | sibling of L146 |
| 181:21 | `unsolved goals` | needs new closing tactic |
| 214:2  | `No applicable extensionality theorem found for type` | `ext` family changed — likely product/function `ext` lemma renamed or specialization needed |
| 222:2  | `No goals to be solved` | `ext` body now closes earlier, leaving an extra tactic |
| 246:11 | `Function expected at` | identifier no longer denotes a function — likely a `def`/`abbrev` body change |
| 484:12 | `Invalid ⟨...⟩ notation` | structure constructor changed shape |
| 485:25 | `omega could not prove the goal` | hypothesis context changed; omega scope shifted |
| 507:2  | `'calc' expression has type` | calc step type unification changed |

### 3d. Mathlib renaming (1)

| Line | Excerpt | Fix |
|---|---|---|
| 329:2 | `mod_cast has type` (type-checks but wrong) | tactic body needs `push_cast` / argument adjustment |
| 674:37 | `Unknown constant Filter.eventually_of_forall` | **Renamed to `Filter.Eventually.of_forall`** (dot-form, capital E). One-liner fix. |

S9's 5 audited lemmas (`tendsto_measure_of_null_frontier_of_tendsto'`,
`IsClopen.frontier_eq`, `le_of_tendsto_of_tendsto'`,
`ENNReal.tendsto_nat_nhds_top`, `ENNReal.tendsto_inv_nat_nhds_zero`)
are **not on this list** — they're still in scope at the pin. The
regression is in OTHER neighborhoods (cylinder/IsClopen constructor at
L101, `split_ifs` interactions at L146/L153, `ext` lemma availability
at L214, the `Filter.eventually_of_forall` → `Eventually.of_forall`
rename at L674, and several `calc` / `omega` / instance-synthesis
issues that S9 didn't probe because it limited itself to a
proof-draft-driven 5-lemma audit).

---

## 4. Cascading-warning inventory (45 warnings)

`grep -c "^warning" /tmp/s11-build.log` = 45. Categories:
- "declaration uses 'sorry'" at L145, L152, L340, L347, L372, L378 —
  these are **NOT** literal `sorry` keywords (only L779 has that).
  They come from Lean's elaborator inserting internal sorry markers
  when a tactic block fails mid-proof. The user-visible `sorry` count
  is still **1** (`grep -c "^sorry\|by sorry\|:= sorry" file` ≤ 1).
- "this simp argument is unused" (several) — minor, would survive repair.
- "this tactic is never executed" (L350/L353/L354) — dead-code due to
  earlier failure in the same `by` block.
- "'rw [...]' tactic does nothing" (L348/L353) — likely simp/rw drift.

These are all **secondary** to the 28 hard errors above.

---

## 5. Why this contradicts S7's "PR #14878 discharged the drift"

Session 7 (2026-05-02, knowledge.md L40+) claims PR #14878 fixed "6
Mathlib API drift root errors (cascading to ~35 build failures)". S7's
listed root fixes:
1. `isOpen_eq_of_isOpen_singleton` removed → `(isOpen_discrete s).preimage`
2. `Finite.instCompactSpace` removed → `inferInstance`
3. `shift_iterate` proof wrong → `congr 1; omega`
4. `split` failed on if-then-else after simp → `split_ifs`

The current breakage at HEAD shows:
- **Fix #1 reverted-or-broken**: L101 has `(isOpen_discrete {b}).preimage
  (continuous_apply i)` and **fails** with "Application type mismatch"
  — exactly the kind of error #1 was supposed to fix. Either the post-#14878
  Mathlib changed the `IsClopen` constructor form again, or the fix
  was incomplete.
- **Fix #4 broken or simp landscape changed**: L146/L153 still fail
  with `split_ifs failed: no if-then-else conditions to split` — the
  same symptom #4 claimed to repair.

So either:
- (A) PR #14878 was insufficient (S7's "6 fixes cascaded to ~35" was
  optimistic, real fix needed ~10+ lines and only the surface 6 were
  patched), OR
- (B) Mathlib bumped within v4.26.0 between PR #14878 merge (2026-05-02)
  and HEAD (2026-06-09), shifting these specific APIs again. Verifiable
  by `git log --follow proofs/lake-manifest.json`. Last touch to
  `lake-manifest.json` is at commit `ecb47b35601` (PR #19454,
  sperner-ndim-mathlib S2-A ACT). That commit's date and pin diff vs.
  PR #14878's would reveal which.

S11 does not investigate (A) vs (B) — the OBSERVE-only scope ends here.
Either way, **the slug is not ACT-ready**, contradicting S8/S9/S10's
shared narrative.

---

## 6. Recommendation

**Pool transition**: BLOCKED (re-applying Session 6's call). Rationale:
- The slug entered the rotation as "available" between 2026-04-27 and
  2026-05-17 (S8 STATE-SYNC documented this drift). S9/S10 kept it
  available based on S9's incomplete audit.
- 28 hard errors at HEAD require Mechanic-level repair, not
  Researcher-level proof completion. Keeping pool "available" wastes
  Researcher cycles (4 sessions S8/S9/S10/S11 have now hit the same
  unrepaired surface).
- Re-blocking matches the spirit of S6's intent (knowledge.md L75 –
  "claim-problem.sh:292 excludes both completed and blocked from
  claim-random selection").

S11 author chooses **NOT to invoke** `FORCE_COMPLETE=1 update` or any
pool-status mutation — same conservative call S8/S9/S10 made. The
recommendation is informational; an operator (Mechanic, Guide, or
manual) should perform the transition.

**Repair path** (S12, Mechanic territory):
1. Fix L101 `IsClopen` constructor form (`⟨isOpen, isClosed⟩` shape).
2. Fix L674 `Filter.eventually_of_forall` → `Filter.Eventually.of_forall`
   rename.
3. Address L146/L153 `split_ifs` — likely needs `simp only [...]` to
   leave the `if` in place, or replace `split_ifs` with `by_cases`.
4. Re-build after each surface fix to see how many cascading errors
   collapse. The 5 "expected token" errors (3a) are almost certainly
   parser cascades — they'll vanish once their upstream type errors
   resolve.
5. After the surface cascade is cleared, address the residual instance
   synthesis failures (L139, L206, L211, L219, L220, L324, L431, L669)
   one-by-one. Each may be a class-name rename or an argument shuffle.
6. Verify `omega` closes L485 with adjusted hypothesis context.
7. Update `Mathlib/Topology/Order/Defs` (or wherever `ext` lemmas now
   live) for L214.
8. Once Docker build passes, **then** S13 ACT can paste the
   `limit_invariant_on_cylinder` 60-line proof at L779.

---

## 7. What S11 produces (5-file doc-only motion)

1. `state.md` head — prepend S11 OBSERVE block above S10; refresh
   Phase header (Phase ACT → "ACT-BLOCKED (build broken at HEAD)";
   Since 2026-06-09; Iteration 10 → 11).
2. `knowledge.md` — append Session 11 entry below Session 10.
3. NEW `sessions/2026-06-09-s11-observe-build-regression.md` (this file).
4. `src/data/research/problems/szemeredi-full-oq-01.json` — refresh
   `currentState.phase` (ACT → "OBSERVE"), `focus`, `nextAction`,
   `iteration` 9 → 11, `blockers` from `[]` to a single-entry list,
   `lastUpdate`.
5. `research/registry.json` — bump `lastUpdate` to S11 timestamp;
   `phase` ACT → OBSERVE.

**Explicit non-actions (out of scope for S11)**:
- No `.lean` edits to `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`.
  Repair is Mechanic territory; the 60-line proof draft remains banked
  for S13 ACT (post-repair).
- No `meta.json` edits.
- No pool status change. S11 only documents the breakage and recommends
  the transition; an operator must enact it.
- No `lake-manifest.json` edits.

---

## 8. Honesty calibration

- The Docker build is reproducible: command is in §2 above; full log
  is at `/Users/rwalters/GitHub/lean-genius/.loom/logs/researcher-5-szemeredi-baseline-build.log`
  on the researcher-5 worktree host. Not committed to the repo (it's
  a 367-line log with mostly Mathlib `info: downloaded ...` lines).
- The 28 error count comes from `grep -c "^error: Proofs" log` = 28
  (plus 2 generic `Lean exited with code 1` / `build failed` lines for
  30 total `^error` lines).
- The error categorization in §3 is best-effort; some hypothesis
  columns (especially under 3b "Application type mismatch") are
  inferred from line context, not verified against the full Mathlib
  diff. S12 Mechanic should re-check each before acting.
- The "Filter.eventually_of_forall renamed" claim is high-confidence:
  the v4.26.0 Mathlib has `Filter.Eventually.of_forall` (dot-form) but
  not the underscored old form. Verifiable by grepping Mathlib at the
  pinned `rev`.
- The "PR #14878 was insufficient" claim is informational only. S11
  did not git-archaeology PR #14878 to verify what it touched vs. what
  is broken now.
