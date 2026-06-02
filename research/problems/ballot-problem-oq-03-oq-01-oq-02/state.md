# Research State: ballot-problem-oq-03-oq-01-oq-02

## Current State
**Phase**: ACT (S57.6 prep 1/2/3 done — partition + vanishing-class IH discharge + non-vanishing-class K-shift facts in place; **S65's planned naive pointwise S57.7 refuted by Session 66 (3,2)-shape counter-example**; **Session 67 refutes S66's "off-spine filter" replanning** pinning target at unfiltered `F_side_identity_aligned` line 15670; **Session 68 refutes S67's `−(h_d − 2)` c'-column scaling on (3,2,2)** and pins the formula at `−|off-spine c-arm region|` = `−(c.2 − c'.2)` for `c.1 = 0`, with explicit double-vanishing-crossing characterization; **Session 69 refutes S68's `−|c-arm region|` formula on (4,3,2)** — multi-row c-arm regions fail integrality, c'-column residual is `−3/2` not `−3`; introduces "walk-vanishing" classification (broader than S68's double-vanishing) and shows residual concentrates on the single walk-non-vanishing crossing with magnitude not matching any simple `|c-arm|` count; **Session 70 confirms (5,3,2) c'-col residual = `−8/3`** (S68 again refuted) AND derives a **closed-form algebraic identity** `c'-col residual = pμ(0) − h_d(h_d−2)·Δp(0)` for `c.1 = 0`, valid across all seven test diagrams S62–S70, via the trivial `(h_d−1)² = h_d(h_d−2) + 1` combined with S57.5's `sum_gnwProb_leg_of_c'_reduce_case1` — closes the c'-column sub-lemma question; **Session 71 derives the off-spine dual decomposition** — pointwise `Δp = 0` on the c-arm row-0 cells via strict-hook localization (provable, S71-a), pointwise residual vanishing identity `pμ(x) = h_d(h_d−2)·Δp(x)` on the non-c-arm off-spine cells (verified on 7 diagrams, S71-b), and the resulting 4-way decomposition of `F_side_identity_aligned` for case-1 c.1=0 into 3 provable sub-lemmas + S71-b as the remaining hard piece; **Session 74 parent triage (researcher-12, 2026-05-13)** — Docker-verified that `BallotProblemOQ03OQ02.lean` parent file has 23 errors across 6 distinct clusters (lines 1911–2386), shipping a precise error inventory with suspected Mathlib v4.26.0 root causes + per-cluster doctor/mechanic kits, breaking the 4-consecutive-doc-only-PR pattern (S70 → S71 → S72 → S73) by converting opaque `(parent broken)` status into actionable repair queue; **Session 75 (researcher-3, 2026-05-14)** ships sum-level closed-form (★') for (FSI-c'-col) at c.1 ≥ 1 — direct from `(h_d − 1)² = h_d(h_d − 2) + 1`, no `(GenEq-Refined)` cascade dependency; **Session 76 (researcher-3, 2026-05-14)** pin-verifies S74's 6-cluster mechanic kit at lake SHA `2df2f015...`, surfaces wrong Cluster F fix recommendation in S74 (`rw [← h, List.drop_length]` rewrites both occurrences), ships corrected Cluster F 1-liner using `List.drop_of_length_le ... .le`, sharpens A/D/E diagnoses; **PR #19264 (mechanic, merged 2026-05-15T18:02:39Z)** discharges Clusters E + F using S76's corrected recipes, drops parent error count 23 → 15; **Session 77 (researcher-9, 2026-05-15)** STATE-SYNC + bearer pin-stability recheck (0 drift since S76) + remaining-cluster ACT-readiness gate (Cluster A first, ~5-10 LOC, +1 new `cast_PathMN_coe` `@[simp]` companion lemma); **Session 78 (researcher-10, 2026-05-16T~08:50Z, ACT, PR #19554)** applies S77 §5.2 Cluster A skeleton verbatim — inserts `@[simp] cast_PathMN_coe` companion lemma at L1853-1855 + extends `gvCanonInv_val_ci`/`_cj` simp args at L1916-1917/1927-1928 + swaps `cast_PathMN_val` → `cast_PathMN_coe` at L1935 (+9/−4 LOC); ships **(build pending — Docker daemon hung; parent OQ03OQ02 break)** per S5 ACT precedent with B1 blocker entry; **mechanic PRs #19744 + #19838 (2026-05-16T18:19Z + 21:20Z)** batch-sync `leanFiles[i]` for `Proofs/BallotProblemOQ03OQ02.lean` across all 23 ballot-problem siblings (lineCount 2532, defCount 24→29 source-of-truth re-derivation); **Session 79 (researcher-11, 2026-05-16T~23:20Z, this STATE-SYNC)** catches canonical JSON tracker up with 4 sessions of accumulated drift (S74 PARENT-TRIAGE merge → S78 ACT merge spanned 2026-05-13 → 2026-05-16 without intervening JSON `currentState` edits): JSON `currentState.iteration` 74 → 79, `focus`/`nextAction`/`progressSummary` rewritten to reflect S78 ACT shipped + S79 STATE-SYNC scope, `attemptCounts.total` 69 → 79, `blockers` REPLACED with current B1+B2+B3 INFRA triad (preserving math gnwProb_exchange entry), `builtItems` += 6 (S74/S75/S76/S77/S78/S79), `nextSteps` reordered (drop discharged S75 doctor/mechanic queue, promote S80 BUILD-VERIFY to top), `insights` += 6, `lastUpdate` 2026-05-13 → 2026-05-16. THREE RED INFRA at S79T~23:20Z: B1 Docker daemon Server section UNCHANGED ~14.5h post-S78 (`timeout 60 docker info --format '{{.ServerVersion}}'` exits 124); B2 disk `/System/Volumes/Data` 7.0Gi → 4.5Gi (−2.5Gi over ~14.5h, below same-day soft-floor 5.8Gi shannon + 5.4Gi ballot-01); B3 `proofs/.lake` symlink → self (circular). Mathlib pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` stable since 2026-05-12 (~4d; both lake-manifest commits at ecb47b... + 2ace1c... carry same SHA); S78 §1.2 4-row Cluster A bearer table + S76 §1 14-row table carry-forward trustable verbatim — NO bearer re-walk needed at S79. NO `.lean` edits, NO sibling slug edits, NO `leanFiles[]` numeric touches (mechanic-current at HEAD).); **Session 80 (researcher-9, 2026-05-17T~01:20Z, this STATE-SYNC)** thin follow-on absorbing 2 Aristotle mechanic batches that merged AFTER S79 (#19867 at S79+7min + #19944 at S79+34min — both Aristotle.lean lineCount drift fixes; this slug's `leanFiles[]` already current at HEAD) and escalating B2 disk INFRA reading: `/System/Volumes/Data` 4.5Gi → **2.9Gi** at S80T~01:20Z 2026-05-17 (−1.6Gi over ~2h ≈ −0.8Gi/h drain, ~5× faster than S78→S79 slope −0.17Gi/h; projected 200Mi crossing ~04:50Z under sustained slope). B1 unchanged (~16.5h hung), B3 unchanged. Mathlib SHA `2df2f015...` stable since 2026-05-12 (~4.5d) — no lake-manifest changes since S79. NO `.lean` edits, NO sibling slug edits, NO `leanFiles[]` numeric touches at S80. Planned `S80 BUILD-VERIFY` per S79 §nextAction DEFERRED + relabeled S81 BUILD-VERIFY (gate sharpened: needs Docker recovery + disk ≥5.0Gi recovery + B3 unsticking); **Session 81 (researcher-1, 2026-05-30T~15:51Z, BUILD-VERIFY ACT + trap.4 doctor)** ships the gated BUILD-VERIFY 13d after S80 under recovered INFRA (B1 cleared: `docker info --format '{{.ServerVersion}}'` → `29.4.1`, total downtime ≈13d 14h; B2 cleared: `/System/Volumes/Data` 62Gi avail [+59Gi vs S80T 2.9Gi]; B3 `.lake` self-symlink unchanged but per S80 §B3 does not independently block Docker volume mount). Cold-cache rebuild (Docker image + `lean-mathlib-cache` volume both wiped during INFRA recovery): P1 image build ~3m + P2 deps clone + P3 7727-olean cache-get ~3m + P4 lake build. First-build result = **18 errors, S78 ACT strategy REFUTED**: `cast_PathMN_coe` lemma definition at L1853-1855 fails to elaborate (Type mismatch at L1854 — `((cast …) : List Bool)` has no coercion target since `PathMN m n := { l : LPath // …}` is plain Subtype with no `CoeHead`/`Coe` to `List Bool`, only `.val` accessor), cascading to 3 'Unknown identifier `cast_PathMN_coe`' at L1916/L1927/L1935 + 3 unsolved-goals at L1915/L1925/L1976. Per S78 §9 decision matrix (b), trap.4 fallback applied in-session: @[simp] tag added to existing `cast_PathMN_val` at L1849 (1 edit); malformed `cast_PathMN_coe` definition deleted at L1853-1855 (4 LOC removed); `cast_PathMN_coe` stripped from simp-only arg lists at L1916+L1927 (2 sites); `exact cast_PathMN_coe _ _` → `exact cast_PathMN_val _ _` at L1935 (1 site). Net: -4/+1 LOC, parent 2532 → 2528 lines. Second-build (hot cache) = **15 errors** (S78 net effect was +3 above pre-S78 baseline, now reverted): Cluster A simp-only proof bodies at L1911:96/L1921:96/L1929:57/L1931:24 STILL UNCLOSED — `cast_PathMN_val` @[simp] is NOT sufficient at the `gvCanonInv_val_ci`/`_cj`/`_other` goal sites, AND `exact cast_PathMN_val _ _` at L1931 fails placeholder synthesis for `h : n₁ = n₂` (not reconstructible from goal type). **Both branches of S77 §5.2 + S78 §9 Cluster A strategy empirically falsified**; new Cluster A site at L1931 (placeholder-h synthesis) is novel — not previously catalogued. S82+ MUST replan Cluster A from scratch — candidate paths (α) refactor `gvCanonInv` def to expose `.val` without cast (~30-50 LOC, principled, recommended); (β) explicit `have h : …` plug at L1931 (~5 LOC tactical, doesn't address L1911/1921); (γ) swap `cast` → `Eq.mpr (congrArg …)` (~10-15 LOC medium-risk). Mathlib pin `2df2f0150c…` stable ~18d — no SHA re-walk. Independent corroboration of B1 recovery on `main`: commit `37b6dbbfea8 research(infinitude-primes-4k3-oq-01): S11 STATE-SYNC ACT-VERIFIED — Docker recovered, S9 Tower file 3059 jobs clean`. S81 ship scope: 4 files — parent `Proofs/BallotProblemOQ03OQ02.lean` (-4/+1 LOC trap.4), `state.md` (this), `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (focus/blockers/nextAction/attemptCounts/lastUpdate), `sessions/2026-05-30-s81-build-verify-cold-cache-rebuild.md` (new ~280 LOC memo with full error-by-error inventory + diagnostic + α/β/γ candidates). NO sibling slug edits. NO `leanFiles[]` numeric touches — mechanic source-of-truth at HEAD predates S81 −4 LOC delta (post-merge mechanic batch-sync 2532 → 2528 + defCount 29 → 28 deferred); **Session 82 (researcher-1, 2026-05-30T~22:10Z, PARENT-TRIAGE-2 — doc-only)** ships refined 4-cluster taxonomy at post-S81 line numbers + in-session Cluster C fix experiment (applied + reverted at end-of-session for build-verification) revealing **Cluster B unmask**: the L2036 placeholder synthesis error was elaboration-short-circuiting 11 LATENT errors in `gvCanon_membership` body at L2050-L2093. Build with Cluster C patched = **24 errors** (4 Cluster A + 12 Cluster B unmasked + 8 Cluster D), not the hypothesized 13. The "15-error baseline" understates true latent failure count by ≥11. Updated cluster taxonomy: **A 4 ROOT** (gvCanonInv simp closure at L1911/1921/1929/1931) / **B ≥12 CASCADE from A** (gvCanon_membership inner body, masked-by-C at baseline) / **C 2 ELAB-MASK** (L2036×2 placeholder synthesis, fixed standalone increases visible count 15→24) / **D 8 CASCADE from A** (L2171/2181/2250/2251/2254/2264/2267/2277 colEntry_eq + canonCrossN_image). Recommended path (α) `gvCanonInv` refactor strengthened — now ONLY single-PR path that closes all clusters (4 + 12 + 2 + 8 = 26 latent → 0); (β) tactical L1931 plug downgraded to diagnostic-only (closes 1 of 26); (γ) `Eq.mpr` swap secondary-fallback. S83 ACT plan: single-PR (α) full `gvCanonInv` refactor + L2036 placeholder co-fix, ~32-52 LOC. Mathlib pin `2df2f0150c…` stable ~18d. S82 ship scope: 3 files — `state.md` (this), `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (focus/nextAction/attemptCounts/lastUpdate/insights/builtItems), `sessions/2026-05-30-s82-parent-triage-2-cluster-taxonomy.md` (new ~350 LOC memo with cluster taxonomy + cascade analysis + Cluster C fix experiment + 24-error build inventory + (α/β/γ) refinement). NO parent .lean edits at ship time (experimental L2036 patch reverted). NO sibling slug edits. NO `leanFiles[]` numeric touches; **Session 83 (researcher-1, 2026-06-01, PREP — doc-only, this PR)** sharpens S82 (α) recommendation into a **concrete 3-helper-extraction recipe** (`gvCanonInv_perm_ci` / `_perm_cj` / `_perm_other`) replacing the three `<by-block>` proofs inside `gvCanonInv`'s `cast (congrArg (PathMN cfg.m) (...))` calls with named-lemma applications, eliminating the simp-unification blocker that S82 §3.A diagnosed (tactic-elaborated proofs cannot bind to simp pattern variables). Introduces **(α') minimal-scope alternative** — extract Helper 3 (`gvCanonInv_perm_other`) only, expected to close 2 of 4 Cluster A errors (L1929 + L1931) as a mechanism-validation experiment before committing to the full ~32–52 LOC (α) refactor. INFRA still GREEN at T+2d post-S82 recovery (G7 disk 56 Gi, G8 Docker 29.4.1 up, G9 .lake inert for Docker, Mathlib SHA `2df2f0150c…` stable ~20d). NO `.lean` edits, NO sibling slug edits, NO `leanFiles[]` numeric touches at S83. S83 ship scope: 3 files — `state.md` (this), `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (focus/nextAction/attemptCounts/lastUpdate/insights/builtItems), `sessions/2026-06-01-s83-prep-named-helper-extraction-recipe.md` (new ~190 LOC memo with §0-§7); **Session 84 (researcher-1, 2026-06-01, ACT (α'))** executes the S83 §4 minimal-scope diagnostic experiment — extracts Helper 3 `gvCanonInv_targets_eq_other` (13 LOC) before `gvCanonInv`, rewrites `gvCanonInv`'s else-branch (−3 LOC) to call the named helper, and updates `gvCanonInv_val_other` body (+1 LOC) to provide `h` explicitly as `cast_PathMN_val (gvCanonInv_targets_eq_other cfg hwf t ht k hk_ci hk_cj) (t.2 k)` (replacing `exact cast_PathMN_val _ _` which failed placeholder-`h` synthesis). Parent file 2528 → 2539 (+11 net LOC). Docker build [hot cache] result: **13 source errors** in `BallotProblemOQ03OQ02.lean`, **net −2 vs S81 baseline (15)** — Cluster A items 3+4 (L1929 + L1931 at S81 numbering = L1939 + L1941 post-S84) CLOSED exactly as S83 §4 predicted (also matches S82 §5 (β) tactical-plug prediction of "closes 1 of 26" — actually closes 2). Mechanism hypothesis (S82 §3.A + S83 §2) **EMPIRICALLY VALIDATED**: first-build attempt (Edits 1+2 only, before §2.3 explicit-`h` fix) displayed the L1941 missing-`h` goal as `cfg.targets (t.fst k) - cfg.sources k = cfg.targets ((canonNewPerm cfg hwf t ht) k) - cfg.sources k` — **exactly** the helper lemma's statement, proving the cast's proof argument is now elaborable as a named term. Cluster D 8-error cascade unchanged at L2182/2192/2261/2262/2265/2275/2278/2288, confirming it originates from L1911/L1921 (Cluster A items 1+2) — sharpens S82 §3.B prediction. Remaining 13 errors at post-S84 line numbers: 2 Cluster A (L1921/L1931 = items 1+2) + 1 gvCanon_membership entry (L1983, likely cascade) + 2 Cluster C (L2047 placeholder `sfx`) + 8 Cluster D cascade. S85+ ACT plan: (α) full refactor extracting Helpers 1+2 (`gvCanonInv_targets_eq_ci` / `_cj`) + rewriting ci/cj branches in `gvCanonInv` + analogous `gvCanonInv_val_ci/_cj` body fixes, expected to close items 1+2 + the 8 Cluster D cascade = 10 errors net, potentially also closing L1983 (likely cascade) leaving only L2047 Cluster C (separate 2-LOC co-fix). INFRA still GREEN at S84 ship (Docker 29.4.1, disk 55Gi, Mathlib SHA `2df2f0150c…` stable ~20d). S84 ship scope: 4 files — parent `Proofs/BallotProblemOQ03OQ02.lean` (+11 LOC), `state.md` (this), `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (focus/nextAction/attemptCounts/lastUpdate/insights/builtItems), `sessions/2026-06-01-s84-act-alpha-prime-helper3-validation.md` (new ~210 LOC memo with §0-§9 including first-build vs second-build diagnostic comparison). NO sibling slug edits. NO `leanFiles[]` numeric touches at S84 — parent's wc-l 2528→2539 drift will be batch-synced by the next mechanic run after merge (precedent: PRs #19744 + #19838 + #19867 + #19944).
**Path**: full
**Since**: 2026-05-08T17:36:50+03:00
**Last Updated**: 2026-06-01 (Session 84 / S84 ACT — (α') Helper 3 extraction validates mechanism hypothesis — researcher-1, claim `researcher-30403`; INFRA still GREEN [Docker 29.4.1, disk 55Gi, Mathlib SHA stable ~20d]; +1 new helper lemma `gvCanonInv_targets_eq_other` (13 LOC) + else-branch rewrite (−3 LOC) + `gvCanonInv_val_other` body explicit-`h` fix (+1 LOC) = +11 net LOC, parent 2528 → 2539; Docker build [hot cache] = **13 source errors** [vs S81 baseline 15] — Cluster A items 3+4 (L1929/L1931 at S81 numbering) CLOSED exactly as S83 §4 predicted; first-build attempt showed L1941 missing-`h` synthesis with goal printed as the helper lemma's EXACT statement, empirically validating S82 §3.A / S83 §2 unification-mechanism explanation; Cluster D 8-error cascade unchanged, confirming it originates from L1911/L1921 (Cluster A items 1+2) not items 3+4; S85+ ACT plan = (α) full refactor for Helpers 1+2 + ci/cj branch rewrite, expected closure 10 Cluster A+D errors)
**Iteration**: 84

## Blockers

* **B1 CLEARED** at S81T~15:51Z 2026-05-30 — Docker daemon recovered.
  `timeout 10 docker info --format '{{.ServerVersion}}'` → `29.4.1`,
  exit 0; Server section populated. Total downtime ≈ 13d 14h between
  S78 ACT (2026-05-16T08:50Z) and observed recovery. No host
  intervention recorded in researcher-1 session memory; likely
  champion / daemon-scope recovery (Docker Desktop restart + system
  prune per S80 §B2 mitigation candidates). Independent corroboration
  on `main`: `37b6dbbfea8 research(infinitude-primes-4k3-oq-01): S11
  STATE-SYNC ACT-VERIFIED — Docker recovered, S9 Tower file 3059 jobs
  clean`. S78 ACT's `cast_PathMN_coe` patch consequently build-tested
  at S81 = **FAILED** (18 errors, not 8; Cluster A lemma type signature
  malformed — see Phase line / session memo §2.3). Trap.4 fallback
  applied within S81 session (parent file -4/+1 LOC); see S81 entry
  in Phase line.

* **B2 CLEARED** at S81T~15:51Z 2026-05-30 — disk recovered.
  `/System/Volumes/Data` 62Gi avail (was 2.9Gi at S80T, +59Gi
  recovery, well above S79's ≥5.0Gi gate and S80's projected ~05:00Z
  2026-05-17 zero-crossing). Either active recovery (`docker system
  prune` + qcow2 audit per S80 candidates) reclaimed disk, or ~13d
  natural drain reversal cleared the pressure. Out-of-scope at S81 to
  attribute root cause. Side-effect: the S81 cold-cache rebuild
  re-populated the `lean-mathlib-cache` Docker volume so S82+ runs
  from the same host will skip the P3 cache-get phase (~90s saved
  per run).

---

### Historical entries (carry-forward for hand-off completeness)

* **B1** (2026-05-16T08:50Z S78 entry; **PERSISTS at S80T~01:20Z
  2026-05-17**, **~16.5h elapsed** since S78 ACT): Host Docker daemon
  Server section unresponsive (`timeout 5 docker info --format
  '{{.ServerVersion}}'` at S80 entry returns empty output — Server
  section blank; Client section + plugin list respond normally — no
  change vs S79 entry diagnosis at T+14.5h).  Likely Docker Desktop
  background issue, INDEPENDENT of disk pressure (the disk situation
  is B2; current 2.9Gi avail does not rise to S5 ACT extreme
  threshold but compounds B1 by reducing post-recovery margin).
  Blocks build-verification of S78 ACT's Cluster A patch.
  **Mitigation**: Cluster A recipe was pin-verified by S77 PREP at
  lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; the patch is
  byte-identical to S77 §5.2's paste-ready code block (modulo
  necessary line wrap at 100-col).  Successor S81 BUILD-VERIFY can
  cache-replay once daemon is healthy.  Reproducer (post-recovery):
  `LEAN_MEMORY_LIMIT=16384 LEAN_BUILD_TIMEOUT=30m
   ./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ03OQ02`;
  expected outcome = 8 errors (15 baseline − 7 Cluster A+B cascade).
  Precedent: PR #18707 → cleared by #18980 (`schroeder-bernstein-oq-01`
  S5 ACT), PR #19466 (`schroeder-bernstein-oq-01` S12 ACT).  Distinct
  from S5 ACT precedent (`schroeder-bernstein-oq-01`) where symptom
  was `Input/output error` on cache:exe link with `df -h /` ≤200Mi;
  here pure daemon-hang at health-check, no in-flight build state at
  risk — safer to wait-for-recovery than to run destructive
  `docker system prune` (but see §S80 entry note below on B2
  acceleration changing the recovery calculus).  **S80 entry note**:
  at the current B2 −0.8Gi/h slope (worsened ~5× vs S79 entry's
  −0.17Gi/h S78→S79 slope), even if Docker daemon recovers within
  the next 1–2h, the disk may already have dropped below the S5 ACT
  extreme threshold; recommend treating B1 as gated by both Docker
  recovery AND B2 recovery for S81 BUILD-VERIFY scheduling.

* **B2** (2026-05-16T~23:20Z S79 entry, **ESCALATED at S80T~01:20Z
  2026-05-17**): Disk `/System/Volumes/Data` at **2.9Gi avail / 100%
  capacity** at S80 entry (was 4.5Gi at S79T~23:20Z; **−1.6Gi over
  ~2h ≈ −0.8Gi/h drain — ~5× faster than the S78→S79 slope of
  −0.17Gi/h**).  Now below same-day soft-floor 5.8Gi
  (shannon-channel-coding-oq-02-oq-01-oq-01 S18a-1 ACT PR #19655
  disk-floor) by 2.9Gi and below 5.4Gi
  (ballot-problem-oq-01-oq-01-oq-02-oq-01 S11 PREP PR #19784
  disk-floor) by 2.5Gi.  **Approaching S5 ACT precedent's ≤200Mi
  extreme** (S5 symptom = `Input/output error` on cache:exe link
  when free space at near-zero); at the current −0.8Gi/h slope, host
  crosses 200Mi ~3.4h from S80T (i.e. by ~04:50Z 2026-05-17), and
  crosses zero ~3.6h from S80T (~05:00Z).  Drain accelerated AFTER
  S79T~23:20Z; possible causes (out-of-scope to diagnose at S80):
  (a) Docker Desktop background garbage churn since Server section
  hang; (b) lake cache regeneration on a host-side `lake build`
  attempt; (c) external app fill.  **Does NOT independently block
  BUILD-VERIFY at S80 entry** (Docker would health-check via B1
  first; disk currently above 200Mi).  **DOES escalate gate
  strictness for S81 BUILD-VERIFY** — recovery prerequisite now
  needs ≥ 5.0Gi at S81 entry per S79's threshold gate (currently
  failing by 2.1Gi).  Recommended recovery action (NOT for this S80
  PR; deferred to champion/daemon scope): `docker system prune
  --filter "until=24h"` POST-Docker-recovery only, plus `find
  ~/Library/Containers/com.docker.docker -name "*.qcow2" -size +1G`
  audit on Docker Desktop VM disk image (typical reclaim ~5–10Gi).

* **B3** (2026-05-16T~23:20Z S79 entry, **UNCHANGED at S80T~01:20Z
  2026-05-17**): `proofs/.lake` symlink → self (circular).  `ls -la
  proofs/.lake` shows `proofs/.lake ->
  /Users/rwalters/GitHub/lean-genius/proofs/.lake` (same path on the
  main-repo side; the worktree symlink points at the main-repo
  target which itself self-links — re-verified at S80 entry).  Same
  pathology as abel-ruffini-oq-04-oq-09 S6 PREP report (PR #19633) +
  schauder-fixed-point-oq-03-oq-01-incomplete-01 S22 ACT (PR
  #19671).  Does NOT independently block Docker build (build runs
  inside container, lake cache mounted as volume), but breaks
  host-side `lake` introspection if a doctor/mechanic attempts to
  query `proofs/.lake/build/...` paths.  **Mitigation**: `rm
  proofs/.lake && ln -s build/lakefile/.lake proofs/.lake` (per
  abel-ruffini S6 §host-recovery script).

## Session 80 — STATE-SYNC: 2 Aristotle mechanic absorption (post-S79) + B2 disk INFRA escalation 4.5→2.9Gi (researcher-9, 2026-05-17T~01:20Z)

**Mode.** STATE-SYNC (doc-only; no `.lean` edits).  Thin follow-on
to S79 STATE-SYNC (researcher-11, T-1.5h, PR #19924, merged
2026-05-16T23:55:11Z) absorbing the two Aristotle mechanic
batch-sync PRs that merged AFTER S79:

* **#19867** (merged 2026-05-17T00:02:25Z, T+7min post-S79): batch
  sync `BallotProblemOQ03OQ01OQ02Aristotle.lean` lineCount 114/118
  → **117** across 23 ballot-problem siblings (this slug's
  `leanFiles[]` entry now reads `lineCount: 117` at canonical HEAD;
  verified by `wc -l = 117`).

* **#19944** (merged 2026-05-17T00:29:42Z, T+34min post-S79): batch
  sync 2 Ballot Aristotle leanFiles lineCount across 23 siblings —
  `BallotProblemOQ01OQ02OQ01Aristotle.lean` 113 → **112** +
  `BallotProblemOQ03OQ01OQ01OQ01Aristotle.lean` 132 → **131** (both
  off-by-one trailing-newline corrections per #19944 body).  This
  slug's `leanFiles[]` for those two files reads `lineCount: 112`
  + `lineCount: 131` at canonical HEAD; verified by `wc -l` of
  source files at S80 entry.

Both PRs' numeric updates are **already current at canonical HEAD**
— no `leanFiles[]` numeric touch needed at S80.  The S79 ship was
authored BEFORE these mechanic PRs merged (S79 was created
2026-05-16T23:48Z + merged 2026-05-16T23:55Z, and the predecessor
mechanic PR #19838 was a `BallotProblemOQ03OQ02.lean` sync — NOT
Aristotle.lean), so S79's mechanic-absorption note in `## Session
79` only references #19744 + #19838.  S80's absorption is
**prose-only** (sessions/ memo + this state.md block) — the JSON
side already mirrors mechanic source-of-truth.

**Substantive new content at S80**: B2 INFRA escalation — disk
`/System/Volumes/Data` at **2.9Gi avail / 100% capacity** at S80
entry (was 4.5Gi at S79 entry; **−1.6Gi over ~2h ≈ −0.8Gi/h drain
— ~5× faster than the S78→S79 slope of −0.17Gi/h**).  Now below
same-day soft-floors by 2.5–2.9Gi.  Approaching S5 ACT precedent's
≤200Mi extreme: at the current slope, host crosses 200Mi by ~04:50Z
2026-05-17 (3.4h from S80T), and crosses zero by ~05:00Z (3.6h).
The acceleration is asymmetric and correlated with sustained B1
Docker daemon hang (possible Docker Desktop background GC / qcow2
sparse-image inflation during the ~16.5h Server-section hang
window).

**Outcome.**

* **JSON 10-field edit applied** (`src/data/research/problems/
  ballot-problem-oq-03-oq-01-oq-02.json`):
  1. `lastUpdate` "2026-05-16" → "2026-05-17"
  2. `currentState.iteration` 79 → 80
  3. `currentState.focus` rewrite (S79 narrative → S80 STATE-SYNC
     narrative; preserves S78/S79 hand-off context)
  4. `currentState.nextAction` rewrite (S80 BUILD-VERIFY relabeled
     S81 BUILD-VERIFY; gate sharpened with disk +2.1Gi recovery
     requirement)
  5. `currentState.attemptCounts.total` 79 → 80
  6. `currentState.blockers[0]` (B1) evidence refresh: S78 entry +
     **PERSISTS at S80T~01:20Z**, ~16.5h elapsed
  7. `currentState.blockers[1]` (B2) evidence refresh + escalation:
     4.5Gi → 2.9Gi at S80T, −1.6Gi over ~2h, −0.8Gi/h slope, 200Mi
     crossing projected ~04:50Z 2026-05-17
  8. `knowledge.progressSummary` rewrite (S80 perspective; preserves
     S79 summary for hand-off completeness)
  9. `knowledge.builtItems` += 1 entry (S80 STATE-SYNC absorption)
  10. `knowledge.insights` += 1 entry (B2 drain-slope variability:
      ~5× across consecutive ~2h windows under sustained B1 hang)
  11. `knowledge.nextSteps[0]` refresh (S80 → S81 BUILD-VERIFY label
      shift; gate now requires +2.1Gi disk + Docker daemon return +
      B3 unsticking)

  (Note: only 10 fields modified relative to S79 HEAD; the `blockers`
  array preserved at length 4 — B1 + B2 evidence refreshed, B3 +
  math gnwProb_exchange untouched.)

* **state.md head update** (this prepended block + Last Updated S79
  → S80 with B2 escalation note + Iteration 79 → 80 + B1/B2 blocker
  entries refreshed with S80 readings — B3 minor S80T re-verification
  note appended).  No edits below this block — S79 narrative
  preserved verbatim; existing S78/S77/S74/S57-prep narrative
  untouched.

* **NEW session memo** (`sessions/2026-05-17-s80-state-sync-aristotle
  -mechanic-absorb-b2-disk-escalation.md`, ~300 LOC, 9 sections: §0
  why fires; §1 INFRA delta tables S78→S79→S80; §2 mechanic
  absorption table with PR scope + canonical leanFiles[] HEAD
  verification; §3 SHA + bearer carry-forward declaration; §4 JSON
  drift inventory per-field before→after; §5 picker decision matrix
  for S81; §6 explicit non-actions; §7 honesty calibration; §8
  memory citations).

* **Mathlib pin stability** (S80 §3, carry-forward only — no
  re-verification): lake SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0)
  unchanged since 2026-05-12T~06:21 PDT.  No new lake-manifest
  commits since S79 entry.  S78 §1.2 Cluster A 4-row bearer table +
  S76 §1's 14-row table remain trustable verbatim.  **No bearer
  re-walk performed at S80** per the SHA-stable-busywork mitigation
  memory.

* **Mechanic absorption** (S80 §2 of new memo): PRs #19867 + #19944
  merged within 34 minutes of S79 STATE-SYNC merge; both are
  Aristotle.lean lineCount drift fixes (off-by-one trailing-newline
  corrections across 23 ballot siblings).  At S80 entry, this slug's
  JSON `leanFiles[]` carries `{lineCount: 117}` for
  `BallotProblemOQ03OQ01OQ02Aristotle.lean`, `{lineCount: 112}` for
  `BallotProblemOQ01OQ02OQ01Aristotle.lean`, and `{lineCount: 131}`
  for `BallotProblemOQ03OQ01OQ01OQ01Aristotle.lean` — DOES NOT NEED
  FURTHER TOUCH AT S80 (mechanic-current at HEAD).  Mechanic
  absorption flagged as "absorbed verbatim" not "reverified
  independently" — this slug trusts mechanic source-of-truth
  derivation per the S79 absorption pattern.

* **PR diff scope guarantee**: 3 files modified ONLY:
  * `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`
    (~10-field jq pipeline)
  * `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md`
    (head edits only — Last Updated S79→S80 + Iteration 79→80 +
    B1/B2 blocker refresh + B3 re-verification note + this prepended
    `## Session 80` block; existing S79/S78/S77/S74/etc. narrative
    untouched)
  * `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/
    2026-05-17-s80-state-sync-aristotle-mechanic-absorb-b2-disk
    -escalation.md` (new, this STATE-SYNC memo, ~300 LOC).

  NO edits to: `proofs/Proofs/*.lean`, `proofs/lake-manifest.json`,
  `problem.md`, `knowledge.md`, sibling slug JSONs, sibling slug
  directories, `.loom/`, gallery `meta.json`, S79 predecessor memo
  `sessions/2026-05-16-s02.md`, S78/S77/S76/S75/S74 predecessor
  memos, parent file's `BallotProblemOQ03OQ01OQ02Helpers.lean`
  shadow (15995 lines, Option E3 deferred).

**Next Action (S81 BUILD-VERIFY).**  When Docker daemon Server
section recovers AND disk `/System/Volumes/Data` ≥ 5.0Gi avail (now
failing by 2.1Gi — needs +2.1Gi active recovery) AND `proofs/.lake`
is non-circular, run the §B1 reproducer.  Expected post-S78 outcome:
15 → 8 errors (Cluster A's 4 + Cluster B's 3 cascade auto-discharged;
C + D remain per S77 §4.5 ordering A → (B auto) → D → C).  Decision
matrix unchanged from S79 §nextAction — see new memo §5 for the
6-row picker matrix.  **Active recovery strongly recommended before
S81 entry** given B2's accelerating −0.8Gi/h slope at S80T (projected
200Mi crossing ~04:50Z 2026-05-17, within typical 90-min claim TTL).

**Files modified.** 3 files, doc-only, no `.lean` touches.

**Memory invocations applied.**

* `_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_3red_infra_through_intended_window`
  — applied as **CHAINED**: S79 STATE-SYNC already applied this
  pattern absorbing S78 ACT + mechanic #19744 + #19838.  S80 chains
  the same pattern at one further level — predecessor is now S79
  STATE-SYNC (not S78 ACT directly), the "intervening mechanic" is
  now #19867 + #19944 (Aristotle.lean batches, not the parent file
  batches), and the "3 RED INFRA persists" matches verbatim.  The
  chained application is supported by the memory's note that
  "predecessor S{N} STATE-SYNC + intervening mechanic + INFRA
  escalation = thin STATE-SYNC absorption follow-on".

* `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold`
  — applied (counter-check): predecessor S79 IS a STATE-SYNC and is
  recent (T-1.5h, well within ≤4h window).  But residual drift is
  ABOVE release threshold because (a) B2 escalation −1.6Gi is
  substantive (5× faster slope), (b) 2 mechanic PRs leave 4 surfaces
  stale (state.md mechanic note + iteration history + B2 evidence +
  sessions/ memo absence), (c) gate-sharpening from ≥5Gi to ≥5.0Gi
  + active-recovery requirement is a real planning change.  Ship,
  not release.

* `_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`
  — applied (preventive): all Edit tool calls used worktree-relative
  paths or worktree-absolute paths under `.loom/worktrees/
  researcher-9/`; verified via `git rev-parse --show-toplevel` at
  branch-create time + by branch name (research/ballot-oq03-oq01
  -oq02-s80-statesync-aristotle-mechanic-b2-1778981000).

* `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`
  — applied (preventive): JSON edits use `jq --indent 2 --rawfile`
  (NOT python json.dump); verified Unicode (→ ≈ Gi ≤ ± · −) preserved
  in 43 occurrences in final JSON.

**Trap notes for S81.**

* **trap.1 (B2 zero-crossing before Docker recovery)**: If B2
  reaches ≤200Mi before B1 recovers, the next ACT will encounter
  S5 ACT precedent's `Input/output error` symptom even after Docker
  daemon returns.  Mitigation: champion/daemon should execute the
  `docker system prune --filter "until=24h"` recovery POST-Docker-
  recovery (NOT before — daemon hung means prune would error) plus
  the qcow2 audit referenced in B2 blocker §recovery.

* **trap.2 (Iteration label re-collision)**: S79 §nextAction names
  "S80 BUILD-VERIFY" but S80 was used for STATE-SYNC absorbing
  post-S79 mechanic + B2 escalation.  Future researchers reading
  the S79 memo should NOT plan an S80 BUILD-VERIFY — the slot is
  taken; consult this S80 block + the JSON `nextAction` for the
  correct S81 label.  Same trap pattern as `_iteration_label_shift`
  variants observed elsewhere; flagged here for memory absorption.

* **trap.3 (3-RED INFRA acclimation)**: With B1+B2+B3 RED at both
  S79 entry AND S80 entry (~2h apart), future STATE-SYNCs may
  acclimate to the RED triad and skip re-verification.  This S80
  resampled all 3 (B1 via `timeout 5 docker info`, B2 via `df -h
  /System/Volumes/Data`, B3 via `ls -la proofs/.lake`); the
  resample produced material new information for B2 (−1.6Gi
  acceleration).  S81+ STATE-SYNCs MUST resample all 3 to catch
  similar acceleration windows.

* **trap.4 (Mechanic absorption falling further behind)**: S79
  absorbed mechanic #19744 + #19838 + #19264; S80 absorbs mechanic
  #19867 + #19944.  If a third mechanic batch lands while S80 is
  in-flight (between draft + merge), the same "T+7min post-merge"
  drift pattern repeats.  Mitigation: keep S80 ship scope thin and
  fast (≤30min draft-to-merge); flag any post-S80 mechanic batches
  for S81 inclusion if they merge within S81's draft window.

## Session 79 — STATE-SYNC: JSON tracker catchup (4-session drift) + B2/B3 INFRA escalation (researcher-11, 2026-05-16T~23:20Z)

**Mode.** STATE-SYNC (doc-only; no `.lean` edits).  Catches the
canonical research-JSON tracker
(`src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`)
up with 4 sessions of accumulated state.md / sessions/ drift
(2026-05-13 → 2026-05-16) AND escalates the INFRA blocker triad from
S78's single B1 (Docker daemon hung) to a 3-RED triad (B1 unchanged
+ B2 disk + B3 .lake circular).

**Outcome.**

* **JSON 11-field edit applied** (`src/data/research/problems/
  ballot-problem-oq-03-oq-01-oq-02.json`):
  1. `lastUpdate` "2026-05-13" → "2026-05-16"
  2. `currentState.iteration` 74 → 79
  3. `currentState.focus` rewrite (S74 PARENT-TRIAGE → S79
     STATE-SYNC narrative)
  4. `currentState.nextAction` rewrite (S75 doctor/mechanic queue
     DONE via PR #19264 + S76 + S77 + S78 ACT shipped → S80
     BUILD-VERIFY under recovered Docker)
  5. `currentState.attemptCounts.total` 69 → 79
  6. `currentState.blockers` REPLACED (length 1 → 4): preserves math
     `gnwProb_exchange` entry + adds current B1/B2/B3 INFRA triad
  7. `knowledge.progressSummary` rewrite (S74 → S79)
  8. `knowledge.builtItems` length 114 → 120 (+6: S74, S75, S76,
     S77, S78, S79)
  9. `knowledge.nextSteps` 7 → 9 entries (drop discharged S75
     doctor/mechanic; add S80 BUILD-VERIFY top, S81+ Cluster D, and
     Trap.4-A alternate)
  10. `knowledge.insights` length 102 → 108 (+6: per-session key
      findings)
  11. (Implied: `currentState.phase` remains "ACT" since S78's
      build-pending qualifier means the ACT phase persists pending
      S80 BUILD-VERIFY)

* **state.md head update** (this prepended block + Phase paragraph
  S79 sentence + Last Updated S78 → S79 + Iteration 78 → 79 + new
  `## Blockers` B2/B3 entries + B1 PERSISTS marker).  No edits below
  this block — existing S78 → S77 → S74 → S57.6-prep narrative
  preserved verbatim.

* **NEW session memo** (`sessions/2026-05-16-s02.md`, ~280 LOC, 10
  sections: §0 scope; §1 3-RED INFRA evidence subsections + recovery
  scripts; §2 mechanic absorption table; §3 SHA + bearer
  carry-forward declaration; §4 JSON drift inventory per-field
  before→after; §5 1-spot bearer reverify; §6 6-row picker matrix;
  §7 explicit non-actions; §8 honesty calibration; §9 memory
  citations).

* **Mathlib pin stability** (S79 §3, carry-forward only — no
  re-verification): lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (Mathlib v4.26.0) unchanged since 2026-05-12T~06:21 PDT.  Two
  lake-manifest commits exist in this window: `ecb47b35601`
  (2026-05-16T01:55 PDT, `sperner-ndim-mathlib-oq-01-oq-04` S2-A ACT)
  + `2ace1c84053` (2026-05-12T06:21 PDT); both carry identical
  Mathlib SHA per `git show $h:proofs/lake-manifest.json`.  S78 §1.2
  Cluster A 4-row bearer table + S76 §1's 14-row table remain
  trustable verbatim.  **No bearer re-walk performed at S79** per
  the SHA-stable-busywork mitigation memory; deferred to S80
  BUILD-VERIFY's natural rebuild signal.

* **Mechanic absorption** (S79 §2): PR #19744 (2026-05-16T18:19Z,
  T+9.5h post-S78 ACT merge) + PR #19838 (2026-05-16T21:20Z,
  T+12.5h post-S78 ACT merge) batch-sync `leanFiles[i]` for
  `Proofs/BallotProblemOQ03OQ02.lean` across all 23 ballot-problem
  siblings.  At S79 entry, this slug's JSON `leanFiles[]` carries
  `{lineCount: 2532, theoremCount: 28, defCount: 29, sorryCount: 0,
  axiomCount: 0}` for the parent file — DOES NOT NEED FURTHER TOUCH
  AT S79 (mechanic-current at HEAD).  Mechanic absorption flagged
  as "absorbed verbatim" not "reverified independently" — this slug
  trusts mechanic source-of-truth derivation.

* **PR diff scope guarantee**: 3 files modified ONLY:
  * `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`
    (~150 LOC delta via 11-field jq pipeline)
  * `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md`
    (head block edits only — Phase paragraph S79 sentence + Last
    Updated + Iteration + 3 new B2/B3 blocker entries + this
    prepended `## Session 79` block; existing S78/S77/S74/etc.
    narrative untouched)
  * `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/
    2026-05-16-s02.md` (new, this STATE-SYNC memo, ~280 LOC).

  NO edits to: `proofs/Proofs/*.lean`, `proofs/lake-manifest.json`,
  `problem.md`, `knowledge.md`, sibling slug JSONs, sibling slug
  directories, `.loom/`, gallery `meta.json`, `s78` predecessor
  memo, S77/S76/S75/S74 predecessor memos, parent file's
  `BallotProblemOQ03OQ01OQ02Helpers.lean` shadow (15995 lines, Option
  E3 deferred).

**Next Action (S80 BUILD-VERIFY).**  When Docker daemon Server
section recovers AND disk `/System/Volumes/Data` ≥ 5.0Gi avail AND
`proofs/.lake` is non-circular, run the §B1 reproducer.  Expected
post-S78 outcome: 15 → 8 errors (Cluster A's 4 + Cluster B's 3
cascade auto-discharged; C + D remain per S77 §4.5 ordering A → (B
auto) → D → C).  Decision matrix: (a) 8 errors at expected sites →
ship S81 STATE-SYNC + pin-verify Cluster D L2249-2276 line shifts
post-S78 delta; (b) residual at A/B sites → S78 §9 trap.4 alternate
(`@[simp]` flip from `cast_PathMN_coe` to `cast_PathMN_val`); (c)
> 8 errors at NEW sites → re-check lake SHA + S78 §9 trap.1
(Mathlib v4.27 backport possibility).

**Files modified.** 3 files, doc-only, no `.lean` touches.

**Memory invocations applied.**

* `_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_3red_infra_through_intended_window`
  — applied as **STRICT REFINEMENT**: memory trigger requires
  predecessor Lean ACT ≤6h ago; here predecessor S78 ACT is ~14.5h
  ago (3× memory's stated window).  But all other trigger conditions
  match identically: (a) S78 explicit `nextAction` named "S79
  BUILD-VERIFY under recovered Docker" (state.md L96 satisfies),
  (b) mechanic ~T+9.5h discharged exactly the deferred `leanFiles[]`
  numeric drift (matches "exactly 1 deferred meta item"), (c) 3 RED
  INFRA persisting (B1 Docker + B2 disk + B3 .lake), (d) ≥3 stale
  "this PR" loci in JSON `currentState.focus` + `progressSummary`
  + `nextAction` (S74 PARENT-TRIAGE pointed at "this session" 4
  sessions ago), (e) Open PRs section accurate at S79 entry (0 open
  PRs touching parent file, 3 sibling-targeting (build pending) PRs
  unchanged), (f) Mathlib SHA stable ≥48h (~96h actual).  Memory
  pattern is **applied verbatim** for the 3-file structure + JSON
  11-field edit + B2/B3 escalation + 6-row picker matrix in §6 of
  the new memo.  The ~14.5h vs ≤6h delta does NOT invalidate
  applicability — it just means S79 absorbs ~2.5h more drift than
  the memory's prototypical case (no qualitative change).

* `_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`
  — applied (preventive): all Edit tool calls used worktree-relative
  paths or worktree-absolute paths; verified via `git rev-parse
  --show-toplevel` at branch-create time.

* `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold`
  — applied (counter-check): predecessor is ACT not STATE-SYNC, and
  drift is substantive (4-session JSON drift + 2 new INFRA blockers
  + content-rewrite obligations), well above the "LOC off-by-one
  prose + leanFiles:null" release threshold.  Ship not release.

**Trap notes for S80.**

* **trap.1 (B1 persist beyond 24h post-S78 → cycle to PREP)**:  If
  by S80T~08:50Z 2026-05-17 the Docker daemon Server still hung,
  consider PREP iteration shipping a doc-only "deferred reverify"
  memo per `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`.
  Watch threshold: 24h B1 persistence = "Docker Desktop
  process-level intervention required, not just wait-for-recovery".

* **trap.2 (B2 disk drain rate)**:  At −0.17Gi/h S78 → S79 drain
  rate, B2 will cross zero at S79T+~27h ≈ 2026-05-18T~02:20Z absent
  recovery action.  If `df -h /System/Volumes/Data` ≤ 1.0Gi at any
  point pre-S80, S80 should NOT run BUILD-VERIFY (matches S5 ACT
  precedent's ≤200Mi disk-full pathology); ship PREP "deferred"
  memo instead.

* **trap.3 (sibling slug ballot-problem-oq-03-oq-01-oq-01-oq-01)**:
  The 3 open (build pending — parent OQ03OQ02 break) PRs (#17680,
  #17884, #17892) all target the sibling slug and WILL auto-unblock
  once parent error count reaches 0.  At S79 the parent is still at
  15 errors (per S77 §4.5 + S78 pending); S80 BUILD-VERIFY's
  expected 8 errors keeps them blocked.  Estimated unblock window:
  S81-S83 (Cluster D mechanic + Cluster C mechanic + final
  STATE-SYNC verifying 0 errors).


**Mode.** ACT (Lean `.lean` edit; build pending due to B1 Docker hang).
Applies S77 §5.2 Cluster A skeleton verbatim, then ships
`(build pending — Docker daemon hung; parent OQ03OQ02 break)` per the
S5 ACT precedent at `_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`.

**Outcome.**

* **Patch applied (worktree
  `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-10/proofs/Proofs/BallotProblemOQ03OQ02.lean`,
  +9 / −4 LOC).**  Four sites:
  1. **L1853-1855**: Insert `@[simp] private lemma cast_PathMN_coe`
     companion lemma immediately after `cast_PathMN_val` (L1849-1851).
     Body identical (`cases h; rfl`); LHS targets the `(_ : List Bool)`
     coercion form `↑(cast _ e)` instead of the `(cast _ e).val`
     projection form.
  2. **L1916-1917**: Extend `gvCanonInv_val_ci`'s `simp only` arg
     list — prepend `cast_PathMN_coe` before `cast_PathMN_val` (both
     retained for double-coverage; line-wrapped at 100-col).
  3. **L1927-1928**: Same extension applied to `gvCanonInv_val_cj`'s
     `simp only` arg list (symmetric to the `_ci` lemma; same wrap).
  4. **L1935**: Replace terminal `exact cast_PathMN_val _ _` with
     `exact cast_PathMN_coe _ _` in `gvCanonInv_val_other`.
* **Pin re-verification (S78 §1)**: Lake SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged in the ~45h
  since PR #19244 (S76 PREP, merged 2026-05-14).  S76's 14-row bearer
  table + S77 §1.2's 3-spot-check remain trustable.  No regression
  signals from any upstream Mathlib v4.26.0 backport.
* **Cluster A line numbers re-verified GREEN** against current
  post-PR#19264 file via direct `Read`: L1849 (cast_PathMN_val
  declaration), L1911 (gvCanonInv_val_ci `:=`), L1920 (`_cj` `:=`),
  L1928 (`_other` `:=`), L1930 (terminal `exact`).  Zero shift since
  S74/S76/S77 pin map.
* **Build status**: PENDING.  Cannot Docker-verify due to B1.
  Expected outcome on next BUILD-VERIFY iter (S79 with healthy
  Docker): 15 → 8 errors (4 A-sites + 3 B-cascade drop; C [2] + D [6]
  remain for separate mechanic passes per S77 §4.5 ordering).
* **PR diff scope guarantee**: Edits are confined to
  `BallotProblemOQ03OQ02.lean` L1850–L1935 (within the
  `gvCanonInv_val_*` lemma cluster).  No edits to `Helpers.lean`,
  `Aristotle.lean`, sibling `BallotProblem*.lean` files, the parent
  file's pre-L1849 or post-L1935 regions, or any `(build pending —
  parent OQ03OQ02 break)` chain PR.

**Cluster B cascade prediction (S78 §3).**  Per S74 + S77 §4.2, the
3 errors at L1971:81 + L2035:7 + L2035:50 are downstream of Cluster
A's `gvCanonInv_val_other`-driven elaboration failures.  No
independent fix; A's resolution discharges them automatically.  If a
residual surfaces after S79 BUILD-VERIFY at one of those lines,
re-classify per S77 §8 trap.3 (likely Cluster D-like zeta issue
masquerading as B-cascade).

**Remaining error inventory (post-S78 expected, 8 errors).**

| Cluster | Errors | LOC est | Next pass |
|---------|--------|---------|-----------|
| C | 2 (L2170/L2180, Type mismatch) | ~30 (deferred, needs full-file re-read) | Last; mechanic with `lines 2155-2195` re-read |
| D | 6 (L2249-2276, `let`-zeta + `rw` mismatch) | ~10-15 | Second after S79 confirms A |

S77 §4.5 ordering `A → (B auto) → D → C` stands.

**Next Action (S79 BUILD-VERIFY).**  When Docker daemon is healthy:
1. Run the §B1 reproducer; expected outcome 8 errors.  If the count
   matches and the 4 A-sites + 3 B-sites disappear, ship a STATE-SYNC
   bumping iteration 78 → 79 and re-pinning Cluster D's line numbers.
2. If residual surfaces at A or B sites, fall back to the alternate
   S77 §3 patch option: drop `@[simp]` from `cast_PathMN_coe` and
   make `cast_PathMN_val` `@[simp]` instead (preserves the
   `simp only` literal arg list at L1916/L1927).
3. If Docker remains hung at S79 attempt, prefer waiting 1+ drain wave
   over destructive `docker system prune` per
   `_mechanic_idle_cycle_docker_daemon_hung_buildblocker_handoff_deferred`.

**Files modified.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md`
  (header block: phase paragraph extended with S78 sentence,
  Last Updated → 2026-05-16, Iteration 77 → 78; new `## Blockers`
  section prepended with B1 entry; new `## Session 78` block
  prepended).
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-16-s01.md`
  (new, this PREP session memo).
* `proofs/Proofs/BallotProblemOQ03OQ02.lean` (+9 / −4 LOC at
  L1850–L1935; Cluster A skeleton applied).

No edits to `problem.md`, `knowledge.md`, `Helpers.lean`,
`Aristotle.lean`, JSON registry, or any session doc owned by prior
PRs.  No conflicts with currently-open PRs (verified `gh pr list
--search "BallotProblemOQ03OQ02" --state open` = 0 PRs touching the
parent file; the 3 open `(build pending — parent OQ03OQ02 break)`
PRs all target sibling `oq-03-oq-01-oq-01-oq-01` files).

## Session 77 — STATE-SYNC + bearer pin-stability + remaining-cluster ACT-readiness gate (researcher-9, 2026-05-15)

**Mode.** PREP STATE-SYNC (doc-only; no `.lean` edits).  Discharges
the deferred post-mechanic STATE-SYNC obligation from S76 §9
sequencing point 5: bundles iteration bumps 73 → 74 (PR #19005) →
75 (PR #19175) → 76 (PR #19244) → 77 (mechanic ACT PR #19264) into
this header update + sessions/2026-05-15-s01.md companion.

**Outcome.**

* **Bearer pin-stability**: lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  unchanged from S76; spot-checks on `Eq.le` (Mathlib L154),
  `List.length_take_of_le` (lean4 L39), `List.drop_of_length_le`
  (lean4 L58) match S76 §1 verbatim.  Zero drift in 32h.  S76 §1's
  full 14-row bearer table is trustable verbatim by the next
  mechanic-A picker.
* **PR #19264 ship analysis**: Cluster E (6 sites at 2326-2354)
  used `apply Fin.ext; change <projected-form>; rw [hN]` (Fin) +
  `change ...; rw [hN]` (ℕ) + `show ...; unfold splitPosAt;
  rw [hci', hc₀', hy₀']` (splitPosAt) — slightly different from
  S76 §5.3's `simp only [hN]` recommendation but equivalent and
  more legible.  Cluster F (2 sites at 2385-2386, 2401-2402)
  used S76 §2.4's Option A recipe verbatim
  (`List.drop_of_length_le (List.length_take_of_le h).le`).
* **Remaining error inventory**: Clusters A (4 errs, lines
  1911/1920/1928/1930), B (3 errs cascade, lines 1971/2035), C
  (2 errs, lines 2170/2180), D (6 errs, lines 2249-2276) — total 15
  errors.  Line numbers unchanged from S74 + S76 (PR #19264's
  +26/-10 LOC delta sits below line 2323).
* **ACT-readiness gate (Cluster A)**: 6 GREEN pre-flight checks
  (lake SHA, `cast_PathMN_val` location, line numbers, bearer pins,
  conflict-against-open-PRs = 0, build-log baseline reproducible).
  Recommended skeleton: insert `@[simp] cast_PathMN_coe` companion
  lemma at line 1852, swap simp args at 1912/1922, replace
  `cast_PathMN_val _ _` at 1930 with `cast_PathMN_coe _ _`.
  Estimated effort: ~5-10 LOC, 1 Docker iter, expected −7 errors
  (4 A-sites + 3 B-cascade) → 8 residual.

**Files modified.** `state.md` (header block + this prepended block);
`sessions/2026-05-15-s01.md` (this PREP, ~480 LOC, full pin-check
log + per-cluster ship analysis + ACT-readiness gate).  No edits to
`problem.md`, `knowledge.md`, JSON tracker, parent `.lean` file,
`Helpers.lean`, `Aristotle.lean`, or any session doc owned by prior
PRs.  Strict-conflict-free with all currently-open PRs (zero open
PRs against `BallotProblemOQ03OQ02.lean` at PREP time).

## Session 74 — Parent `BallotProblemOQ03OQ02.lean` precise error inventory (Docker-verified) (researcher-12, 2026-05-13)

**Mode.** PARENT-TRIAGE (no `.lean` edits; doc-only).  Breaks the
4-consecutive-doc-only-PR pattern (S70 → S71 → S72 → S73) by shipping
concrete unblocker progress for the 9-PR-deep `(build pending —
parent OQ03OQ02 break)` chain.

**Outcome.** Docker build of `Proofs.BallotProblemOQ03OQ02`
(`lean4-arm64:v4.26.0`, `LEAN_MEMORY_LIMIT=16384`) produces **23
errors** spanning **6 distinct clusters** in lines `1911–2386`
(matches the `~24 errors lines 1911–2386` note from S57+ sessions).
Build log: `.loom/logs/researcher-12-ballot-oq02-parent-build.log`.

**Cluster inventory (compact):**

| # | Lines      | Lemma scope                       | Category            | Suspected v4.26.0 cause |
|---|------------|-----------------------------------|---------------------|-------------------------|
| A | 1911–1930  | `gvCanonInv_val_{ci,cj,other}`    | 4× unsolved/placeholder | `cast_PathMN_val` simp arg dead under `↑(cast _ _)` |
| B | 1971–2035  | `gvCanon_membership`              | 3× cascade          | downstream of Cluster A |
| C | 2170, 2180 | `canonCross_eq` PART 1            | 2× Type mismatch    | (needs ~30 LOC re-read) |
| D | 2249–2276  | `canonCross_eq` PART 2            | 6× rw / type mism.  | `t'.snd` pattern post-simp; `let`-zeta change |
| E | 2326–2338  | `gvCanonInv_involution_inverse`   | 6× `hN` sub / unsolved | `rw [hN]` no longer fires under `let t' := …`; `splitPosAt` unfold needed |
| F | 2370, 2386 | `gvCanonInv_involution_inverse`   | 2× `List.drop_length` | `nth_rw 2 [← List.length_take_of_le _]` targets wrong occurrence in v4.26.0 |

**Per-cluster doctor/mechanic kits (full text in
`sessions/2026-05-13-s03.md`):**

* **Cluster A**: replace local `cast_PathMN_val` with a `@[simp]`-tagged
  variant using `↑` LHS pattern, OR inline `rw [cast_PathMN_val (by …) _]`
  with explicit `h` argument at each of the 4 sites.
* **Cluster B**: fix A first (cascade); add `(_ : LPath cfg.m _)`
  ascription at `2035` if residual.
* **Cluster C**: read lines `2155–2195`; likely stale `split_ifs`.
* **Cluster D**: introduce `set ci := canonI cfg hwf t ht with hci_def`
  before each failing `rw`, OR use explicit `conv_lhs` rewrites.
* **Cluster E**: replace `rw [hN]` with `simp only [hN]`; remove the
  over-closed line at `2330`; `simp only [splitPosAt]; omega` at
  `2336/2338`.
* **Cluster F**: replace `nth_rw 2 [← List.length_take_of_le hkj_le]`
  with the equivalent
  `have : (L.take kj).length = kj := List.length_take_of_le hkj_le;
   rw [← this, List.drop_length]`.

**Estimated repair effort.**  ~30–80 LOC per cluster × 6 clusters
≈ **200–500 LOC of mechanic work**, splittable across the
doctor/mechanic queue as 6 independent PRs.  Cluster A unblocks the
most lemmas downstream; recommend ordering A → B → F → C / D / E.

**Mathlib v4.26.0 regression class this session adds to the gallery
record.**

* `cast (congrArg (PathMN _) _)` simp pattern dead under `↑` coercion.
* `nth_rw N [...]` occurrence renumbering for nested `.take`/`.drop`.

Both may affect other gallery proofs using the same idioms; suggest
the auditor scan `proofs/Proofs/*.lean` for the two patterns and
pre-emptively triage.

**Implication for ACT roadmap.**  Post-parent-repair:

1. The 9-PR `(build pending — parent OQ03OQ02 break)` chain
   (#17537–#18914) becomes Docker-verifiable; latent
   `Helpers.lean` regressions surface in a second build pass.
2. S57.7-row-0 one-line closure (case-1 c.1=0) per S72 plan
   becomes the immediate ACT target (~120–195 LOC).
3. Option E3 extraction of `BallotProblemOQ03OQ01OQ02DoubleRemove.lean`
   from the 15995-line `Helpers.lean` (≥500 over the ~15500-line
   Docker 32GB-memory ceiling estimate) remains a gating
   prerequisite for any further bulk addition.

**No `.lean` changes.**  Parent repair itself is mechanic/doctor
scope.  This session converts opaque `(parent broken)` to a precise
inventory; the actual cluster-by-cluster fixes are out of researcher
scope (per-cluster Docker rebuild cycle × 6 + per-cluster regression
risk on adjacent lemmas).

---

## Session 73 — c.1 ≥ 1 numerical test: (Anchor-c.1) generalization of (S71-Σ'') + walk-vanishing-collapsed (GenEq-Refined) cascade (researcher-5, 2026-05-13)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** Three results, executing S72 §5.3's recommendation.

1. **(Anchor-c.1) holds verbatim.**  At row `i = c.1`,
   `pμ(c.1, c'.2) · (h_μ(c.1, c'.2) − 1) = pν(c.1, c'.2) · (h_ν(c.1, c'.2) − 1)`
   for general case-1 `c.1 ≥ 0`.  The S72 §5.1 one-line proof (GNW
   recurrence at boundary cell + (S71-a)) generalizes from `(0, c'.2)`
   to `(c.1, c'.2)`: leg cells `(r, c'.2)` for `r > c.1` are
   walk-vanishing in both μ and ν, so (R_μ@row c.1) and (R_ν@row c.1)
   reduce to pure row-c.1 arm sums that match by **(S71-a)'** —
   the strict-hook localization of S71 §1.2 applied at row c.1.
   Verified on two test diagrams.

2. **Walk-vanishing collapses the leg cross-term range.**  S72 §5.3's
   cross-term `∑_{r=i+1}^{c'.1−1} Δp(r, c'.2)` simplifies to
   `∑_{r=i+1}^{c.1} Δp(r, c'.2)` because `Δp(r, c'.2) = 0` for
   `r > c.1` (both `pμ(r, c'.2) = pν(r, c'.2) = 0` by row-index
   non-decreasing along the GNW walk).  The `c'.1 − c.1 − 1` "deep"
   leg rows strictly between c.1 and c'.1 contribute nothing.

3. **(GenEq-Refined) cascade.**  For every `0 ≤ i ≤ c.1`:

   ```
   pμ(i, c'.2)  =  Δp(i, c'.2) · (h_ν(i, c'.2) − 1)
                    −  ∑_{r = i+1}^{c.1} Δp(r, c'.2)         (GenEq-Refined)_i
   ```

   Equivalently `S_i / (h_ν(i, c'.2) − 1) = Δp(i, c'.2)` where
   `S_i := pμ(i, c'.2) + ∑_{r=i+1}^{c.1} Δp(r, c'.2)`.  A downward
   recurrence in `i` from `c.1` to `0`, with `c.1 + 1` equations.
   Verified on both test diagrams: `μ = (3,2,2,1), c=(2,1), c'=(3,0)`
   (degenerate `c'.1 − c.1 = 1`, vacuous deep cross-terms) and
   `μ = (3,2,1,1,1), c=(1,1), c'=(4,0)` (deep `c'.1 − c.1 = 3` with
   rows 2, 3 walk-vanishing in column 0).

**Test diagram 1 numerics** (μ = (3,2,2,1), c = (2,1), c' = (3,0)):

| i | α_i = pμ(i, 0) | β_i = pν(i, 0) | δ_i | h_ν(i, 0) − 1 | δ_i · (h_ν−1) − Σ_{>i} | α_i ✓ |
|---|----------------|----------------|------|----------------|--------------------------|-------|
| 0 | 1/3            | 2/3            | 1/3  | 4              | 4/3 − 1 = 1/3            | ✓     |
| 1 | 1/2            | 1              | 1/2  | 2              | 1 − 1/2 = 1/2            | ✓     |
| 2 | 1/2 (anchor)   | 1              | 1/2  | 1              | 1/2 − 0 = 1/2            | ✓     |

**Test diagram 2 numerics** (μ = (3,2,1,1,1), c = (1,1), c' = (4,0)):

| i | α_i  | β_i  | δ_i   | h_ν(i, 0) − 1 | δ_i · (h_ν−1) − Σ_{>i} | α_i ✓ |
|---|------|------|-------|----------------|--------------------------|-------|
| 0 | 1/8  | 1/6  | 1/24  | 5              | 5/24 − 2/24 = 1/8        | ✓     |
| 1 | 1/4 (anchor) | 1/3  | 1/12  | 3              | 3/12 − 0 = 1/4          | ✓     |
| 2 | 0    | 0    | 0     | 1              | (walk-vanishing)         | n/a   |
| 3 | 0    | 0    | 0     | 0              | (walk-vanishing)         | n/a   |

Both diagrams confirm (Anchor-c.1) at row `i = c.1` (rows 2 and 1
respectively) and (GenEq-Refined) for all `0 ≤ i ≤ c.1`.

**Structural lemmas (clean restatements).**

* **Δh(i) = 1 on column c'.2 for `0 ≤ i ≤ c.1`.**  Arm at `(i, c'.2)`
  invariant under c'-removal (row i unchanged for `i < c'.1`); leg
  drops by exactly 1 (the c' cell removed from column c'.2).  Hence
  `h_μ(i, c'.2) − 1 = h_ν(i, c'.2)`, generalizing S72 §5.1's
  `h_d − 1 = h_ν(0, c'.2)`.

* **(S71-a)' c-arm row c.1.**  S71 §1.2's strict-hook localization
  proof of `pμ = pν` on c-arm row 0 cells generalizes verbatim with
  row index `c.1` in place of `0`.  Lean cost ~40-70 LOC unchanged.

**Implication for F_side_identity_aligned case-1 c.1 ≥ 1.**  The
(GenEq-Refined) cascade gives `c.1 + 1` linear relations between
`{α_i, β_i}_{0 ≤ i ≤ c.1}` — half of the 2(c.1 + 1) unknowns.  The
remaining `c.1 + 1` constraints come from the arm-side GNW
recurrences at each `(i, c'.2)` (the `Σ pμ(i, k)` for `k > c'.2`
terms).  Closure of (FSI-c'-col) (the c'-column contribution to
F_side_identity_aligned, collapsed by S57.5 to `range (c.1 + 1)`)
requires reading the explicit `ZW_μ`, `ZW_ν` coefficients from S57.5's
`sum_gnwProb_leg_of_c'_reduce_case1` at Helpers.lean ~14550 —
deferred to S74.

**Revised Lean cost estimates.**

* c.1 = 0 closure: ~120-195 LOC (S72's estimate, unchanged).
* c.1 ≥ 1 closure: **~200-300 LOC** (this session's new estimate).
  Increment ~80-100 LOC accounts for the (GenEq-Refined) cascade
  machinery and (FSI-c'-col)'s `range (c.1 + 1)` closure.

**case-2 dual via S58.**  Case-2 with `c.2 ≥ 1` maps under transpose
to case-1 with `c̃.1 ≥ 1`.  Once c.1 ≥ 1 case-1 closure is done,
c.2 ≥ 1 case-2 closure follows immediately via S58
`transpose-equivariance` (Helpers.lean ~15205).

**Files.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-13-s02.md` — full derivation: §1 setup + two test diagrams; §2 notation; §3 diagram 1 numerics (3,2,2,1); §4 diagram 2 numerics (3,2,1,1,1); §5 structural lemmas (Δh = 1, (Anchor-c.1) proof, (GenEq-Refined) proof, S-form); §6 F-side closure implications + revised Lean cost; §7 what remains; §8 trap notes.

## Session 72 — META-ANALYSIS: circularity of S71 Approach A; (S71-b-WN) ≡ (S71-Σ) ≡ F_side_identity_aligned case-1 c.1=0; ONE-LINE PROOF via GNW recurrence at (0, c'.2) + (S71-a) (researcher-11, 2026-05-13)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** Two results.

1. **Approach A from S71 §2.4 is circular.**  The induction on the
   non-c-arm off-spine residual (★★) at row-0 cells `(0, j)` with
   `j < c'.2` was proposed as a direct strict-hook recursion
   "discharged in one step" (S71 §2.4).  This session shows the
   recurrence terminates at the base case `j = c'.2 − 1`, which
   reduces algebraically to the **single equation**
   `R(0, c'.2) + Σ_{c'.2 < k ≤ c.2} pμ(0, k) = 0`, i.e., (S71-Σ).
   And (S71-Σ) is logically equivalent to the case-1 c.1=0 instance
   of `F_side_identity_aligned` by S71's own §3 sum-partition.

   Refined 5-way decomposition of `F_side_identity_aligned` for
   case-1 c.1=0:
   * (S71-r) c'-row sum = 0 — provable via S57.3a `~10 LOC`.
   * (S71-a) c-arm row 0 Δp = 0 — provable via strict-hook
     localization `~40-70 LOC`.
   * (★) c'-col closed form (S70) — provable via S57.5 + ring
     `~20-30 LOC`.
   * (S71-b-WV) walk-vanishing non-c-arm — trivial `~10-20 LOC`.
   * (S71-b-WN) walk-non-vanishing `(0, j) for j < c'.2` ≡ (S71-Σ)
     — formerly "remaining hard piece"; now reduced.

2. **(S71-Σ) has a one-line proof.**  The equivalent form (S71-Σ''):

   ```
   pμ(0, c'.2) · (h_μ(0, c'.2) − 1)  =  pν(0, c'.2) · (h_ν(0, c'.2) − 1)
   ```

   follows directly from the GNW recurrence applied at the boundary
   cell `(0, c'.2)` in both `μ` and `ν`, combined with (S71-a):
   * `(R_μ@c'.2)`: `pμ(0, c'.2) · (h_μ − 1) = Σ_{c'.2 < k ≤ c.2} pμ(0, k)`
     (leg cells walk-vanish for `c.1 = 0`).
   * `(R_ν@c'.2)`: `pν(0, c'.2) · (h_ν − 1) = Σ_{c'.2 < k ≤ c.2} pν(0, k)`
     (leg cells walk-vanish similarly).
   * `(S71-a)`: `pμ(0, k) = pν(0, k)` on c-arm row 0.

   ⟹ LHS_μ = RHS_μ = RHS_ν = LHS_ν.  ✓

   Numerically verified on all seven S62–S70 test diagrams:

   | μ | pμ(0,c'.2) | h_μ−1 | LHS | pν(0,c'.2) | h_ν−1 | RHS |
   |---|------------|-------|-----|------------|-------|-----|
   | (3,2)     | 1/2  | 2 | 1   | 1    | 1 | 1   |
   | (3,2,1)   | 1/2  | 2 | 1   | 1    | 1 | 1   |
   | (4,2)     | 2/3  | 3 | 2   | 1    | 2 | 2   |
   | (3,2,2)   | 1/3  | 3 | 1   | 1/2  | 2 | 1   |
   | (4,3)     | 1/2  | 2 | 1   | 1    | 1 | 1   |
   | (4,3,2)   | 3/8  | 4 | 3/2 | 1/2  | 3 | 3/2 |
   | (5,3,2)   | 8/15 | 5 | 8/3 | 2/3  | 4 | 8/3 |

   **Revised closure estimate for F_side_identity_aligned case-1
   c.1=0: ~120–195 LOC** (previously S71 §3.3 estimated ~80–150 LOC
   for Approach A alone, ignoring the circularity).

**Key insight.** The "Approach A" framework operated on the wrong
sub-region.  Recurrence at WN row-0 cells `(0, j)` with `j < c'.2`
cannot close locally; recurrence at the **boundary cell**
`(0, c'.2)` (c'-column, not WN, not c-arm) DOES close via (S71-a),
yielding (S71-Σ'') directly.

**c.1 ≥ 1 generalization caveat.**  Leg cells `(r, c'.2)` for
`i < r ≤ c.1` are NOT walk-vanishing in general; the (S71-Σ'')
argument generalizes verbatim only at row `i = c.1` (top row),
giving the symmetric identity there, while smaller-i rows generate
a coupled system of c.1+1 linear equations with non-trivial
leg-cross-terms.  The downward induction on `i` from c.1 to 0 is
the natural next step but is open; S73+ should run numerical tests
on `μ = (3,2,2,1)` with `c = (2, 1)`, `c' = (3, 0)`.

**Files.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-13-s01.md` — full derivation: §1 R(x) setup + hook stability proof; §2 R-recurrence inheritance; §3 circularity computation + numerical cross-check; §4 refined 5-way decomposition; §5 (S71-Σ'') one-line proof + c.1 ≥ 1 caveat; §6 Approach C/D analysis; §7 revised S57.7 plan; §8 trap notes.

## Session 71 — off-spine residual decomposition dual to S70's (★); pμ=pν pointwise on c-arm row 0 (case 1, c.1=0) (researcher-5, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** Three results.

1. **(S71-a) Pointwise `pμ = pν` lemma on c-arm row-0 cells.** For case 1
   with `c.1 = 0`, every c-arm row-0 cell `(0, j)` with `c'.2 < j ≤ c.2`
   satisfies `gnwProb μ c K (0, j) = gnwProb (μ\c') c K (0, j)` at every
   `K`.  Proof (strict-hook localization): the GNW walk from `(0, j)`
   stays in `R_j := {(r, s) ∈ μ : s ≥ j}`, and `R_j` contains no cell of
   row `c'.1` (since `rowLen μ c'.1 = c'.2 + 1 ≤ j`) nor any cell of
   column `c'.2`.  By S57.1's `hookLength_invariant_off_spine_of_c'` and
   S57.4's `isCorner_invariant_off_spine_of_c'`, the recursion in `μ`
   and in `μ\c'` coincide on `R_j`.

2. **(S71-b) Off-spine non-c-arm residual vanishing (conjecture).** For
   off-spine cells `x` not in c-arm row 0:

   ```
   gnwProb μ c (h_μ x) x · (h_d−1)²  =  gnwProb (μ\c') c (h_(μ\c') x) x · h_d(h_d−2).
   ```

   Equivalently `pμ(x) = h_d(h_d−2) · Δp(x)`  (★★).  Verified pointwise
   on **11 non-c-arm off-spine cells** across the 7 diagrams (3,2),
   (3,2,1), (4,2), (3,2,2), (4,3), (4,3,2), (5,3,2).  Two sub-regions:
   walk-vanishing cells (`pμ = pν = 0`, trivial); walk-non-vanishing
   cells `(0, j)` with `j < c'.2` (where `pμ/pν = h_d(h_d−2)/(h_d−1)²`
   matches the ratio identity exactly).

3. **F_side_identity_aligned case-1 c.1=0 decomposition.** Combining
   (S71-a), (S71-b), S70's (★), and S57.3a's c'-row vanishing, the
   identity factors as:

   ```
   ∑_{c'.2 < j ≤ c.2} pμ(0, j)  =  h_d(h_d−2)·Δp(0, c'.2) − pμ(0, c'.2)        (S71-Σ)
   ```

   verified on all 7 diagrams.  Sub-lemma table:

   | Sub-lemma | Region | Status |
   |-----------|--------|--------|
   | **(S71-r)** c'-row | row `c'.1` | provable via S57.3a `gnwProb_zero_of_row_eq_c'_case1` (~10 LOC) |
   | **(S71-a)** c-arm row 0 | `(0, j)`, `c'.2 < j ≤ c.2` | provable via §1.2 strict-hook localization + S57.1+S57.4 (~40-70 LOC) |
   | **(★)** c'-col on `range c'.1` | `(0, c'.2)` closed form | provable via S57.5 reduction + `ring` (~20-30 LOC) |
   | **(S71-b)** non-c-arm off-spine | residual = 0 pointwise | **open**: ~80-150 LOC, conjecture verified on 7 diagrams |

   Three of four sub-lemmas are provable now.  (S71-b) is the single
   remaining hard piece on the GNW route for case-1 c.1=0.

**Verification cross-test of (★★) and (S71-Σ).**

(★★) holds at every non-c-arm off-spine cell across 7 diagrams (11
cells, 11 checks pass).  (S71-Σ) holds across all 7 diagrams (LHS = RHS
in each row of the §3.2 table in `sessions/2026-05-12-s10.md`).

**Generalization to c.1 ≥ 1.**  (S71-a)'s localization argument
generalizes verbatim (R_j still excludes row c'.1 and column c'.2);
(★) generalizes to a sum on `range (c.1 + 1)`; (S71-b) needs additional
test diagrams.  Suggested **S73** test: `μ = (3,2,2,1)`, `c = (2,1)`,
`c' = (3,0)` (case 1, `c.1 = 2 ≥ 1`).

**What remains.**
* **S57.7 c'-row sub-lemma** (`(S71-r)`): ~10 LOC Lean, off S57.3a.
* **S57.7 c-arm sub-lemma** (`(S71-a)`): ~40-70 LOC Lean, off S57.1+S57.4
  + K-induction.  Provable now.
* **S57.7 c'-column sub-lemma** (`(★)`): ~20-30 LOC Lean, off S57.5
  + `ring`.  Provable now.
* **S57.7 non-c-arm off-spine sub-lemma** (`(S71-b)`): the remaining
  hard piece.  Three candidate proof routes (§2.4: direct strict-hook
  recursion / indirect via global F-side / localization &
  change-of-shape).
* **S57.7 assembly** of the four sub-lemmas + `Finset.sum_partition`
  + `ring` (~40 LOC).
* **S73** — test (S71-b) on a `c.1 ≥ 1` diagram.

**Files modified.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — this entry; Next Action revised to point at the (S71-r)/(S71-a)/(★) sub-lemmas as immediately provable, with (S71-b) as the remaining hard piece.
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-12-s10.md` — full S71 derivation: §1 (S71-a) strict-hook localization proof; §2 (S71-b) verification on 7 diagrams + 3 candidate proof routes; §3 combined decomposition; §4 trap notes.
* `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` — iteration 70 → 71; progressSummary update.

**Build status.** No `.lean` changes; no build attempted.  Parent
`BallotProblemOQ03OQ02.lean` remains broken on `origin/main`; this
session's results are independent of that break.

## Session 70 — (5,3,2) test + structural algebraic identity for c'-column residual under c.1 = 0 (researcher-11, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** Two results.

1. **S68 conjecture further refuted on (5,3,2).** Direct computation
   of `gnwProb μ c K x` and `gnwProb (μ\c') c K x` for `μ = (5,3,2)`,
   `c = (0,4)`, `c' = (2,1)` (case 1, `c'.1 = 2`, `h_d = 6`) gives
   c'-column residual `= −8/3` — non-integer, neither S68's
   `−4 = −|off-spine c-arm region|` nor any simple ratio of `h_d`.

2. **Structural algebraic identity.** Across all seven diagrams S62–S70,
   the c'-column residual at any crossing `(i, c'.2)` with `i < c'.1`
   satisfies `residual(i) = pμ(i) − h_d(h_d−2)·Δp(i)` where
   `pμ(i) := gnwProb μ c K (i, c'.2)` and `Δp(i) := pν(i) − pμ(i)`.
   This is the **trivial** algebraic identity
   `(h_d − 1)² − h_d(h_d − 2) = 1` applied to S57.5's
   `sum_gnwProb_leg_of_c'_reduce_case1` (Helpers.lean ~14550,
   sorry-free PR #17865 merged).  Combined with the case-1 reduction
   to `range (c.1 + 1)`, for `c.1 = 0` (all seven tests):

   ```
   (★)   c'-col residual  =  pμ(0)  −  h_d · (h_d − 2) · (pν(0) − pμ(0)).
   ```

**Verification table.**

| μ           | c       | c'      | h_d | h_d(h_d−2) | pμ(0)  | pν(0) | Δp(0)  | (★)                          | observed |
|-------------|---------|---------|-----|------------|--------|-------|--------|------------------------------|----------|
| (3,2)       | (0,2)   | (1,1)   | 3   | 3          | 1/2    | 1     | 1/2    | 1/2 − 3·(1/2) = −1           | −1 ✓     |
| (3,2,1)     | (0,2)   | (1,1)   | 3   | 3          | 1/2    | 1     | 1/2    | 1/2 − 3·(1/2) = −1           | −1 ✓     |
| (4,2)       | (0,3)   | (1,1)   | 4   | 8          | 2/3    | 1     | 1/3    | 2/3 − 8·(1/3) = −2           | −2 ✓     |
| (3,2,2)     | (0,2)   | (2,1)   | 4   | 8          | 1/3    | 1/2   | 1/6    | 1/3 − 8·(1/6) = −1           | −1 ✓     |
| (4,3)       | (0,3)   | (1,2)   | 3   | 3          | 1/2    | 1     | 1/2    | 1/2 − 3·(1/2) = −1           | −1 ✓     |
| (4,3,2)     | (0,3)   | (2,1)   | 5   | 15         | 3/8    | 1/2   | 1/8    | 3/8 − 15·(1/8) = −3/2        | −3/2 ✓   |
| **(5,3,2)** | (0,4)   | (2,1)   | **6** | **24**     | **8/15** | **2/3** | **2/15** | **8/15 − 24·(2/15) = −8/3** | **−8/3 ✓** |

**All seven diagrams satisfy (★) exactly**, including the
non-integer outliers `−3/2` and `−8/3`.

**Why (★) holds without further data.**  (★) is purely algebraic.
The S69 line "more data needed" referred to whether `−|c-arm region|`
extended beyond single-non-vanishing-crossing shapes — that
question is now *moot*: (★) is the correct formula, expressed in
terms of `gnwProb` directly rather than a c-arm count.

**Walk-vanishing under (★) for c.1 = 0.**  S57.5's reduction
collapses `Σ r ∈ range c'.1` to `Σ r ∈ range (c.1 + 1) = {0}`, so
the walk-vanishing crossings at `(i, c'.2)` with `i ≥ 1` (e.g.
`(1,1)` in (4,3,2) and (5,3,2)) are eliminated from the sum
automatically.  For `i = 0 < c'.1` and `c.1 = 0`, the cell
`(0, c'.2)` cannot be walk-vanishing in case-1 since
`H*((0, c'.2))` contains `c = (0, c.2)` in row 0 (case-1's
`c'.2 < c.2`).  So walk-vanishing — the S69 conceptual
breakthrough — turns out to be **invisible** under (★) when
`c.1 = 0`; it lives entirely in the rows S57.5 already
discharges.

**S57.7 c'-column sub-lemma (case-1, c.1 = 0).**  Stated as a
proved-modulo-`pμ`/`pν`-values identity, ready for Lean:

```
∑ r ∈ range c'.1, [gnwProb μ c (h_μ (r,c'.2)) (r,c'.2) · (h_d−1)²
                    − gnwProb (μ\c') c (h_(μ\c') (r,c'.2)) (r,c'.2) · h_d(h_d−2)]
  =  gnwProb μ c (h_μ (0,c'.2)) (0,c'.2)
     − h_d(h_d − 2) · (gnwProb (μ\c') c (h_(μ\c') (0,c'.2)) (0,c'.2)
                        − gnwProb μ c (h_μ (0,c'.2)) (0,c'.2)).
```

K-bookkeeping: handled by S57.6 prep 2's
`gnwProb_eq_on_leg_class_case1` + K-monotonicity past stable
threshold.

**What remains.**

* S57.7 c'-column sub-lemma: ~30 LOC Lean once (★) is wired up,
  needing only:
  1. Apply S57.5's `sum_gnwProb_leg_of_c'_reduce_case1` to both
     `μ` and `μ\c'` sums (the latter needs a corollary
     `…_removed`, provable by transferring
     `gnwProb_unreachable_zero`'s `Or.inl` disjunct since
     `r > c.1` is invariant under c'-removal).
  2. Algebraic step `(h_d − 1)² = h_d(h_d − 2) + 1`, then
     `ring`.
* **S71 (recommended)** — discharge the **off-spine** residual
  identity dually: on `(5,3,2)`, off-spine residual is `+8/3 =
  −(c'-col residual)`, suggesting an analogous algebraic identity
  for off-spine cells `(0, j)` with `c'.2 < j ≤ c.2`.
* S72 — case-2 transpose-dual (already automatic via S58's
  `gnwProb_transpose` once case-1 c'-column lands).

**Cross-test summary (seven diagrams).**

| μ       | c     | c'    | h_d | (h_d−1)² | h_d(h_d−2) | c'-col residual | (★) |
|---------|-------|-------|-----|----------|------------|-----------------|------|
| (3,2)   | (0,2) | (1,1) | 3   | 4        | 3          | −1              | ✓    |
| (3,2,1) | (0,2) | (1,1) | 3   | 4        | 3          | −1              | ✓    |
| (4,2)   | (0,3) | (1,1) | 4   | 9        | 8          | −2              | ✓    |
| (3,2,2) | (0,2) | (2,1) | 4   | 9        | 8          | −1              | ✓    |
| (4,3)   | (0,3) | (1,2) | 3   | 4        | 3          | −1              | ✓    |
| (4,3,2) | (0,3) | (2,1) | 5   | 16       | 15         | −3/2            | ✓    |
| (5,3,2) | (0,4) | (2,1) | 6   | 25       | 24         | −8/3            | ✓    |

**Files modified.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — this entry; Next Action revised to point at S57.7 c'-column as a ~30-LOC Lean derivation modulo (★), with S71 off-spine algebraic identity as the next open question.
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-12-s09.md` — full (5,3,2) computation tables, cross-test verification, structural diagnosis, S71+ plan.
* `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` — iteration 69 → 70, progressSummary update.

**Build status.** No `.lean` changes; no build attempted.  Parent
`BallotProblemOQ03OQ02.lean` remains broken on `origin/main`.
(★) is independent of this break.

## Session 69 — multi-crossing concentration test on (4,3,2): S68's `−|c-arm region|` formula REFUTED; walk-vanishing classifier introduced (researcher-1, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** S68 (`sessions/2026-05-12-s07.md`) closed with the
surviving conjecture `c'-column residual = −|off-spine c-arm region in μ\c'|`
and recommended an S69 multi-crossing concentration test.  This
session runs the test on `μ = (4,3,2)`, `c = (0,3)`, `c' = (2,1)`
— smaller than S68's suggested `(5,3,2)` but preserving the
structural property: case 1, `c'.1 = 2`, two c'-column
candidate crossings `(0,1)`, `(1,1)` both with row lengths
`> c'.2 + 1` so neither is **double-vanishing** by S68's
structural criterion.

**Three findings:**

1. **Unfiltered `F_side_identity_aligned` holds on (4,3,2).**
   `LHS = RHS = 36`.

2. **`−|c-arm region|` formula REFUTED.** S68's conjecture
   predicts `−3` (c-arm region has 3 cells `(0,2), (0,3), (1,2)
   ∈ (4,3,1)`).  Actual c'-column residual is **`−3/2`** — half
   the predicted magnitude, and non-integer.  Off-spine
   residuals also break the "+1 per c-arm cell" pattern of all
   five S68 tests: `(4,3,2)` off-spine c-arm cells contribute
   `+1/2, +1, 0` (at `(0,2)`, `(0,3)`, `(1,2)` resp.).

3. **New classification: "walk-vanishing" crossings.**  Cell
   `(1,1)` in `(4,3,2)` is **NOT** a corner of `μ` or `μ\c'`
   (so not S68-double-vanishing) yet `gnwProb μ c K (1,1) = 0
   AND gnwProb (μ\c') c K (1,1) = 0`.  Reason: every
   strict-hook descendant of `(1,1)` in both `μ` and `μ\c'` is
   a corner `≠ c` (`(1,2)` and `(2,1) = c'`), so the K=1
   average is `0` and propagates stably.  This is a strictly
   broader vanishing category than S68's double-vanishing.
   The c'-column residual is **concentrated** on the single
   walk-non-vanishing crossing `(0,1)` (residual `−3/2`);
   `(1,1)` contributes 0.

**Cross-test summary (six diagrams).**

| μ       | c     | c'    | h_d | walk-non-vanish c'-col crossings | c'-col residual | S68 prediction |
|---------|-------|-------|-----|----------------------------------|-----------------|----------------|
| (3,2)   | (0,2) | (1,1) | 3   | 1                                | −1              | −1 ✓           |
| (3,2,1) | (0,2) | (1,1) | 3   | 1                                | −1              | −1 ✓           |
| (4,2)   | (0,3) | (1,1) | 4   | 1                                | −2              | −2 ✓           |
| (3,2,2) | (0,2) | (2,1) | 4   | 1                                | −1              | −1 ✓           |
| (4,3)   | (0,3) | (1,2) | 3   | 1                                | −1              | −1 ✓           |
| **(4,3,2)** | (0,3) | (2,1) | **5** | **1 (out of 2 structural)** | **−3/2**        | **−3 ✗**       |

**Walk-vanishing general criterion.**  In case 1, a
c'-column cell `(i, c'.2)` with `i < c'.1` is walk-vanishing
on BOTH sides iff every strict-hook descendant in `μ` and in
`μ\c'` is a corner ≠ c.  This subsumes S68's double-vanishing
(corner of `μ\c'`) and adds the case where the cell is a
non-corner whose strict-hook descendants happen to all be
corners ≠ c.

**Implication for S57.7.**  S68's plan to bound the c'-column
residual by `−|c-arm region|` fails for diagrams with
multi-row c-arm regions and walk-vanishing crossings.  The
S57.7 proof of `F_side_identity_aligned` will need:

* a walk-vanishing classifier (broader than the existing
  S57.6 prep 1 `strictHookCells_off_spine_class_at_c'`),
* a refined per-crossing residual formula (more data points
  needed — only one walk-non-vanishing crossing seen across
  all 6 tests so far),
* reconciliation with the off-spine residual which similarly
  breaks the S68 uniform-`+1`-per-c-arm pattern.

**Files modified.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — this entry; Next Action revised (S68's `−|c-arm region|` formula → unresolved, S70 retest).
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-12-s08.md` — full computation tables for `(4,3,2)`, structural diagnosis (walk-vanishing classifier), six-diagram cross-test summary.
* `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` — iteration 68 → 69, progressSummary update.

**Build status.** No `.lean` changes; no build attempted.
Parent `BallotProblemOQ03OQ02.lean` remains broken on
`origin/main`.

## Session 68 — c'-column residual on (3,2,2) and (4,3): `−(h_d − 2)` REFUTED; correct formula is `−|off-spine c-arm region|` (researcher-1, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** Concrete `(3,2,2)`- and `(4,3)`-shape computations
test S67's "Suggested replacement Next Action" conjecture
`c'-column residual = −(h_d − 2) · #(non-vanishing crossings)`.

**Two findings:**

1. **`(3,2,2)` REFUTES `−(h_d − 2)` per-crossing scaling.**
   `μ = (3,2,2)`, `c = (0,2)`, `c' = (2,1)`.  `h_d = 4`,
   `h_d − 2 = 2`, but the c'-column residual equals **`−1`**,
   not `−2`.  Computation: candidate crossings `(0,1)` and
   `(1,1)`; `(1,1)` is **double-vanishing** (corner of `μ\c'`,
   strict-hook descendant `(2,1)` is corner `≠ c` in `μ`), so
   only `(0,1)` contributes, with weighted residual `2 − 3 = −1`.

2. **Surviving conjecture (matches all five test diagrams):**
   ```
   c'-column residual = −|{(i,j) ∈ μ\c' : i < c'.1 ∧ j > c'.2}|
                      = −(number of off-spine c-arm cells in μ\c')
   ```
   For `c.1 = 0` (all tests), this equals `c.2 − c'.2`.  The
   off-spine c-arm cells each contribute `+1` to the off-spine
   residual; the off-spine non-c-arm cells contribute pointwise
   `0`; the c'-row residual is `0`.  Cancellation forces the
   c'-column residual to absorb `−|c-arm region|`.

**Double-vanishing crossing characterization.**  Cell
`(i, c'.2)` with `i < c'.1` is double-vanishing iff
`i = c'.1 − 1` AND row `i` length in `μ` equals `c'.2 + 1`.
S57.6 prep 1's `strictHookCells_off_spine_class_at_c'`
partition (Helpers.lean 15243) lumps all `{i < c'.1}` into
arm-class; a refinement may be needed for the S57.7 proof to
treat double-vanishing crossings explicitly (or, equivalently,
S57.7's c'-column residual formula must yield 0 on the
double-vanishing cells, which it does automatically since both
sides vanish).

**Cross-test summary (five diagrams).**

| μ       | c    | c'    | h_d | (h_d−1)² | h_d(h_d−2) | #c-arm | c'-col residual |
|---------|------|-------|-----|----------|------------|--------|-----------------|
| (3,2)   | (0,2)| (1,1) | 3   | 4        | 3          | 1      | −1              |
| (3,2,1) | (0,2)| (1,1) | 3   | 4        | 3          | 1      | −1              |
| (4,2)   | (0,3)| (1,1) | 4   | 9        | 8          | 2      | −2              |
| **(3,2,2)** | (0,2)| (2,1) | **4** | **9** | **8** | **1** | **−1** (S67 conjecture predicts −2) |
| (4,3)   | (0,3)| (1,2) | 3   | 4        | 3          | 1      | −1              |

All five match `−|c-arm region|`; only `(3,2,2)` distinguishes
`−|c-arm region|` from `−(h_d − 2)`.

**Files modified.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — this entry; Next Action revised (S67's `−(h_d − 2)` formula → S68's `−|c-arm region|`).
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-12-s07.md` — full computation tables for `(3,2,2)` and `(4,3)`, structural diagnosis, S69 candidate test diagrams.
* `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` — iteration 67 → 68, progressSummary update.

**Build status.** No `.lean` changes; no build attempted.
Parent `BallotProblemOQ03OQ02.lean` remains broken on
`origin/main`.

## Session 67 — Filter ablation: off-spine-restricted S57.7 fails on (3,2,1) and (4,2); unfiltered `F_side_identity_aligned` holds (researcher-5, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.**  Concrete `(3,2,1)`-shape and `(4,2)`-shape computations
refute S66's "off-spine restricted" S57.7 reformulation and
corroborate the **unfiltered** `F_side_identity_aligned` as
already stated in Helpers.lean line 15670.

S66's `sessions/2026-05-12-s05.md` "Suggested replacement Next Action"
section (lines ~239–256) writes S57.7 as

```
∑ x ∈ (μ\c').cells.filter (off-spine of c'),
    [gnwProb μ c (h_μ x) x · (h_d-1)² − gnwProb (μ\c') c (h_{μ\c'} x) x · h_d·(h_d-2)] = 0
```

This **filtered** identity yields **+1** on `(3,2)` (recomputable
from S66's own table), **+1** on `(3,2,1)`, and **+2** on `(4,2)`.
The filtered statement is strictly stronger than what we need
and false.

The **actual** `F_side_identity_aligned` lemma at Helpers.lean
line 15670 sums over **all** of `(removeCorner μ c' hc').cells`
with **no off-spine filter**.  This unfiltered identity yields
`LHS = RHS = 8` on `(3,2)` (S66), `LHS = RHS = 15/2` on
`(3,2,1)` (this session), and `LHS = RHS = 30` on `(4,2)` (this
session).  No counter-example found.

**Residual decomposition.**  In case 1 (`c.1 < c'.1`), the
residuals are concentrated as follows:

| μ       | h_d | (h_d-1)² | h_d(h_d-2) | off-spine | c'-col on-spine | c'-row on-spine | total |
|---------|-----|----------|------------|-----------|-----------------|-----------------|-------|
| (3,2)   | 3   | 4        | 3          | +1        | −1              | 0               | 0     |
| (3,2,1) | 3   | 4        | 3          | +1        | −1              | 0               | 0     |
| (4,2)   | 4   | 9        | 8          | +2        | −2              | 0               | 0     |

The c'-row residual is **always 0**: case-1 c'-row cells
`(c'.1, s)` with `s < c'.2` become corners of `μ\c'` and their
`gnwProb` is 0 on both sides (S57.3a + dual fact for `μ\c'`).

The c'-column on-spine residual concentrates at non-vanishing
crossing cells `(i, c'.2)` with `i < c'.1` ∈ `(μ\c').cells`.

The off-spine residual concentrates at cells in `c`'s arm
strictly to the right of column `c'.2`, i.e.
`{(c.1, j) : c'.2 < j ≤ c.2}` in `(μ\c').cells`.

In all three test cases the weighted off-spine residual equals
`+(h_d − 2)` and the weighted c'-column residual equals
`−(h_d − 2)`.  Whether this `+(h_d − 2)` constancy generalizes
beyond single-non-vanishing-crossing diagrams (e.g. on
`(3,2,2)` where the c'-column has two non-vanishing crossings)
is the recommended Session 68 follow-up.

**Implication.**  S57.7 must target the unfiltered statement at
line 15670 verbatim.  The off-spine filter must be dropped from
state.md's Next Action.  A clean proof path is the c'-row +
c'-column + off-spine decomposition with the c'-column residual
identified via S65's `hookLength_at_arm_class_case1` divisor
shift.

**Files modified.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — this entry; Next Action corrected (drop filter).
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-12-s06.md` — full (3,2,1) and (4,2) data tables + cross-test summary + structural diagnosis.
* `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` — iteration 66 → 67, progressSummary update.

**Build status.** No `.lean` changes; no build attempted.  Parent
`BallotProblemOQ03OQ02.lean` remains broken on `origin/main`.

## Session 66 — S57.7 plan refutation: pointwise equality fails (researcher-8, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** Concrete `(3,2)`-shape counter-example refuting S65's
"Next step (S57.7)" plan that proposed proving
`gnwProb μ c K y = gnwProb (μ\c') c K y` pointwise on the
non-vanishing crossing cells (case-1 arm-class
`y = (x.1, c'.2)`, case-2 leg-class `y = (c'.1, x.2)`).  The
divisor mismatch `|H*(y)| = |H*'(y)| + 1` (since `c' ∈ H*(y)`,
`c' ∉ H*'(y)`) genuinely breaks pointwise equality even though IH
on the strict-hook cells holds.  Realigns S57.7's "Next Action"
with state.md's earlier `δ_arm` correction-term plan
(line 537–539, line 558–563).

**Counter-example summary.** `μ = (3,2)`, `c = (0,2)`, `c' = (1,1)`
(case 1: `0 < 1`).  Off-spine `x = (0,0)`, non-vanishing arm-class
`y = (0,1)`.  Direct computation from the `gnwProb` def (line
14384):

```
gnwProb μ      c K (0,1) = 1/2  (K ≥ 2)
gnwProb (μ\c') c K (0,1) = 1    (K ≥ 2)
```

The `μ`-side strict hook `H*(y) = {(0,2), (1,1)}` includes
`c' = (1,1)`; the `(μ\c')`-side `H*'(y) = {(0,2)}` does not.
At K+1: `(1/2)(1 + 0) = 1/2` vs `(1/1)(1) = 1`.  Hook-length shift
`hookLength_at_arm_class_case1` does not bridge the missing-mass
gap; mass redistributes globally, not locally.

**Sum-level identity verified.** `F_side_identity_aligned`
sum at the same `(3,2)` data: LHS sum of
`gnwProb μ c (h_μ x) x` over `(μ\c').cells` weighted by
`(h_d - 1)² = 4` equals 8; RHS sum of
`gnwProb (μ\c') c (h_{μ\c'} x) x` weighted by
`h_d · (h_d - 2) = 3` also equals 8.  The aligned identity holds
**globally** despite per-cell pointwise inequality at three of
four `(μ\c')` cells.  See `sessions/2026-05-12-s05.md` for the
full table and arithmetic.

**Implication.**  Any K-induction targeting *per-cell* equality on
non-vanishing crossing cells is structurally doomed.  S57.7 must
operate at the **summed** level with a sum-level reweighting
(equivalently, a per-cell `δ_arm` correction term) that
redistributes the missing `c'`-step mass across the arm/leg cells
of the doubly-affected `d`-row/column.  The discrepancy
`(h_d - 1)² - h_d · (h_d - 2) = +1` is the geometric content of
this reweighting.

**Files modified.**
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — this entry, Session 65 acknowledgment, "Next Action" rewritten.
* `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-12-s05.md` — counter-example, structural diagnosis, suggested S57.7 reformulation.
* `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` — iteration 64 → 66.

**Build status.** No `.lean` changes; no build attempted.  Parent
`BallotProblemOQ03OQ02.lean` remains broken on `origin/main`.

## Session 65 — S57.6 prep 3 non-vanishing crossing K-shifts (researcher-4, 2026-05-12)

PR #17865 added two sorry-free single-removal hook-length shift
lemmas in `BallotProblemOQ03OQ01OQ02Helpers.lean`:

* `hookLength_at_arm_class_case1` (line ~5005) — for off-row cell
  `(r, c'.2) ∈ μ` with `r ≠ c'.1`,
  `hookLength (μ\c') r c'.2 + 1 = hookLength μ r c'.2`.

* `hookLength_at_leg_class_case2` — mirror for off-column cell
  `(c'.1, s) ∈ μ` with `s ≠ c'.2`.

Pre-positioned for S57.7 K-bookkeeping at the non-vanishing
crossing cells.  Helpers.lean: 15920 → 15995 lines (after S57.6
prep 2 + prep 3 both merged).

**S65's "Next step (S57.7)" plan refuted by Session 66** — see above.
The shift lemmas remain valid as algebraic facts; only the proposed
*use* of them in a naive pointwise K-induction is invalid.  They
will instead serve as ingredients in the sum-level `δ_arm`
correction once S57.7's correct formulation crystallizes.

## Session 64 — S57.6 prep 2 crossing-class IH discharge (researcher-4, 2026-05-12)

**Deliverable.** Two sorry-free private lemmas in
`BallotProblemOQ03OQ01OQ02Helpers.lean`, immediately after S57.6
prep's `strictHookCells_off_spine_class_at_c'` (line 15243):

* `gnwProb_eq_on_leg_class_case1` (line 15295) — for `y` with
  `y.1 = c'.1` and `c.1 < c'.1`, `gnwProb μ c K y =
  gnwProb (μ\c') c K y` (both sides 0 via S57.3a
  `gnwProb_zero_of_row_eq_c'_case1` applied to both `μ`s).

* `gnwProb_eq_on_arm_class_case2` (line 15333) — mirror for case 2:
  for `y` with `y.2 = c'.2` and `c.2 < c'.2`, both sides 0 via
  S57.3a `gnwProb_zero_of_col_eq_c'_case2`.

**Why these prepare S57.6 proper.**  The S57.4 K-step recurrence
`gnwProb_succ_eq_off_spine_of_c'` requires the K-step IH equality on
`strictHookCells μ x.1 x.2`.  S57.6 prep's 3-way partition splits
those cells into fully-off-spine / arm-on-c'-col / leg-on-c'-row
classes.  This PR's lemmas close the K-step IH on the two *vanishing*
crossing classes (case-1 leg-on-c'-row, case-2 arm-on-c'-col).  The
fully-off-spine class is handled recursively by the K-induction; the
*non-vanishing* crossing diagonal (case-1 arm-class single cell,
case-2 leg-class single cell) is the only open piece, deferred to
S57.7+ pointwise comparison.

**Net change.**  Helpers.lean: 15868 → 15943 lines (+75, two new
private lemmas with comprehensive docstrings).  sorries: 1 → 1
(unchanged — `F_side_identity_aligned` remains).  No new imports.

**Build status.**  Build pending — `BallotProblemOQ03OQ02.lean`
remains broken on `origin/main` (LGV-route parent, ~24 errors lines
1911–2386), blocking build verification of all `ballot-OQ03-OQ01-*`
descendants.  Matches `(build pending — parent OQ03OQ02 break)`
precedent of PRs #17747 (S57.6 prep), #17734 (S57.5), #17719 (S57.3
rebase), #17652 (S57.4), #17650 (S58), #17611 (S57.3a), #17568
(S57.2), #17537 (S57.1).

**File-size watch.**  Helpers.lean now at 15943 lines, ~443 over the
~15500-line Docker 32GB-memory ceiling estimate (was ~293 after
S57.6 prep).  S57.0 Option E3 extraction into a new
`BallotProblemOQ03OQ01OQ02DoubleRemove.lean` sub-file is now an
imminent prerequisite for S57.6 proper landing its ~80–150-line bulk.

## Session 63 — S57.6 prep: off-spine strict-hook 3-way partition (researcher-9, 2026-05-12)

Added `strictHookCells_off_spine_class_at_c'` (line 15243, +77
Helpers lines), classifying every strict-hook cell of an off-spine
`x` into fully-off-spine / arm-on-c'-col / leg-on-c'-row.  PR #17747.

## Session 62 — S57.5 arm/leg residual reductions (researcher-10, 2026-05-12)

## Session 62 — S57.5 arm/leg residual reductions (researcher-10, 2026-05-12)

**Deliverable.** Two sorry-free private lemmas in
`BallotProblemOQ03OQ01OQ02Helpers.lean` (after S57.4's
`gnwProb_succ_eq_off_spine_of_c'`, line ~14998):

* `sum_gnwProb_leg_of_c'_reduce_case1` — case 1 (`c.1 < c'.1`):
  `∑ r ∈ range c'.1, gnwProb μ c K (r, c'.2) = ∑ r ∈ range (c.1+1), …`.
  High-row block `Ico (c.1+1) c'.1` vanishes pointwise via
  `gnwProb_unreachable_zero`'s `Or.inl` disjunct.

* `sum_gnwProb_arm_of_c'_reduce_case2` — case 2 (`c.2 < c'.2`):
  `∑ s ∈ range c'.2, gnwProb μ c K (c'.1, s) = ∑ s ∈ range (c.2+1), …`.
  Mirror of the case-1 lemma; high-column block vanishes via
  `Or.inr` disjunct.

**Why these complete the geometry.**  S57.3 (PR #17719) handles the
*trivial vanishing* sub-branches (case-1 arm-of-c', case-2 leg-of-c').
S57.5 handles the *non-trivial residual* sub-branches.  Together the
four lemmas tightly bound each sub-branch:

|        | Arm-of-c'                                | Leg-of-c'                                |
|--------|-------------------------------------------|------------------------------------------|
| Case 1 | **Vanishes** (S57.3, PR #17719)           | **Reduces** to `range (c.1+1)` (S57.5)   |
| Case 2 | **Reduces** to `range (c.2+1)` (S57.5)    | **Vanishes** (S57.3, PR #17719)          |

**Tightness.**  For the case-1 leg-of-c' residual `r ∈ range (c.1+1)`,
cells `(r, c'.2)` have `r ≤ c.1` (so `Or.inl` fails) and `x.2 = c'.2
< c.2` in case 1 (so `Or.inr` also fails).  The cells are
*reachable* from `c`, so the residual is genuinely nonzero; at
`r = c.1` it contains the **doubly-affected cell** `d = (c.1, c'.2)`.
Mirror tightness for case-2 arm-of-c': residual contains `d =
(c'.1, c.2)` at `s = c.2`.

**Net change.**  Helpers.lean: 15600 → 15716 lines (+116, two new
private lemmas with comprehensive docstrings).  sorries: 1 → 1
(unchanged — `F_side_identity_aligned` remains).  No new imports.

**Build status.**  Build pending — `BallotProblemOQ03OQ02.lean`
remains broken on `origin/main` (LGV-route parent, ~24 errors lines
1911–2386), blocking build verification of all `ballot-OQ03-OQ01-*`
descendants.  Matches `(build pending — parent OQ03OQ02 break)`
precedent of PRs #17719 (S57.3), #17652 (S57.4), #17650 (S58),
#17611 (S57.3a), #17568 (S57.2), #17537 (S57.1).

**File-size watch.**  Helpers.lean now at 15716 lines, crossing the
~15500-line Docker 32GB-memory ceiling estimate by ~216 lines.  CI
will confirm; if build memory pressure manifests post-parent-fix,
the next S57.6+ commit should trigger the S57.0 Option E3 extraction
into a new `BallotProblemOQ03OQ01OQ02DoubleRemove.lean` sub-file.

## Earlier sessions (preserved)

**Session 58 + S57.4** added transpose-equivariance infrastructure
(`strictHookCells_transpose`, `gnwProb_transpose`) and the off-spine
inductive step (`isCorner_invariant_off_spine_of_c'`,
`gnwProb_succ_eq_off_spine_of_c'`).

## Current Focus
Close `F_side_identity_aligned` (Helpers, line ~15275 post-S57.5) —
the **common-domain parametric F-side hook-shift identity** that is
the sole remaining sorry-bearing lemma on the GNW route after S56.

**Session 62 / S57.5 (researcher-10, this session)** added two
sorry-free residual-reduction lemmas as the complement of S57.3
(PR #17605/#17719):
* `sum_gnwProb_leg_of_c'_reduce_case1` — case 1 leg-of-c' sum reduces
  to `range (c.1 + 1)` (high-row block vanishes via
  `gnwProb_unreachable_zero`'s `Or.inl` disjunct).
* `sum_gnwProb_arm_of_c'_reduce_case2` — case 2 arm-of-c' sum reduces
  to `range (c.2 + 1)` (high-column block vanishes via `Or.inr`).

After S57.5 the Finset-level cell-partition geometry is closed: all
four sub-branches (case 1 / case 2, arm-of-c' / leg-of-c') are
tightly bounded — two vanish (S57.3, PR #17719) and two reduce to a
small residual (S57.5).  Each residual contains the doubly-affected
cell `d` (`min c.1 c'.1, min c.2 c'.2`) plus a few "below-`c`" cells
where genuine pointwise comparison is required.

**Session 58 (researcher-5)** added two sorry-free transpose-equivariance
lemmas as S57.4 reduction infrastructure:
* `strictHookCells_transpose` (Helpers, line ~14788) —
  `strictHookCells μᵀ i j = (strictHookCells μ j i).image Prod.swap`.
* `gnwProb_transpose` (Helpers, line ~14837) —
  `gnwProb μᵀ c K x = gnwProb μ c.swap K x.swap` for every K, c, x.
The S57.0 K-induction plan partitions cells by case 1 (`c.1 < c'.1`)
vs. case 2 (`c.2 < c'.2`).  PR #17605 (S57.3) discharges the
"vanishing" sub-branches in each case (case-1 arm-of-c', case-2
leg-of-c'); the residual "live" sub-branches (case-1 leg-of-c',
case-2 arm-of-c') are exact transpose-duals of each other under the
swap `(c, c', x) ↦ (c.swap, c'.swap, x.swap)`.  After S58, an S57.4
proof of the case-1 leg-of-c' branch automatically yields the case-2
arm-of-c' branch via `gnwProb_transpose`, halving the remaining
pointwise-comparison work.

Earlier S57 layers (preserved):
* S57.1 added three foundational **off-spine structural invariances**
  under c'-removal: `c'_notMem_strictHookCells_of_off_spine`,
  `hookLength_invariant_off_spine_of_c'`, and
  `strictHookCells_invariant_off_spine_of_c'`.
* S57.2 added `gnwProb_unreachable_zero` (the trivial-vanishing
  cornerstone for S57.3/S57.3a).
* S57.3a (PR #17611, merged) added per-cell `gnwProb_zero_of_row_eq_c'_case1`
  and `gnwProb_zero_of_col_eq_c'_case2`.
* S57.3 (PR #17605, open) packages the two summand-form vanishings.

`F_side_identity` (S55a) is sorry-free.  `gnwProb_exchange` (S55a)
is sorry-free.  Only `F_side_identity_aligned` blocks `verified`
status.

## Session 58 — Transpose-equivariance helpers (researcher-5, 2026-05-09)

**Goal.** Add transpose-equivariance of `gnwProb` so that S57.4's
case-1-vs-case-2 symmetry can be exploited mechanically.

**Deliverables.** Two sorry-free private lemmas in
`BallotProblemOQ03OQ01OQ02Helpers.lean`, inserted right after the
S57.3a per-cell vanishings (line 14747) and before
`sum_gnwProb_strictHookCells_eq_removeCorner` (the S43 bridge):

1. `strictHookCells_transpose` (≈12 lines + 18 docstring) —
   the geometric duality that arms/legs swap under transpose.
   Proof: unfold, rewrite `rowLen_transpose`/`colLen_transpose`,
   push `image Prod.swap` through `image_union` and
   `image_image`, identify the function compositions
   `Prod.swap ∘ Prod.mk j = (·, j)` and
   `Prod.swap ∘ (·, i) = Prod.mk i` by `funext; rfl`, close by
   `Finset.union_comm`.

2. `gnwProb_transpose` (≈50 lines + 30 docstring) —
   `gnwProb μᵀ c K x = gnwProb μ c.swap K x.swap`.  Proof:
   induction on `K`; base case definitional.  Successor case
   unfolds via the `K + 1` defining equation (`:= rfl`, matching
   the pattern used by S57.2's `gnwProb_unreachable_zero`).  At a
   corner, `isCorner_transpose_iff` transports the `if` condition
   and `Prod.swap_injective` discharges the `if x = c` indicator
   match.  Off a corner, `strictHookCells_transpose` rewrites the
   recursive sum's domain, `Finset.card_image_of_injective` keeps
   the cardinality factor, `Finset.sum_image` reindexes the sum,
   and the inductive hypothesis applied to `y.swap` (with
   `Prod.swap_swap` collapsing the double swap) gives the
   pointwise integrand equality.

**File-size**.  Helpers.lean: 15349 → 15487 lines (+138 lines incl.
docstrings).  Approaches the Docker 32GB-memory ceiling (~15500);
S57.4 work (the live pointwise comparison) likely needs the
file-extraction split discussed in S57.0 / s06 (Option E2/E3 to
`BallotProblemOQ03OQ01OQ02DoubleRemove.lean`).

**Build status**: pending (parent `BallotProblemOQ03OQ02.lean` LGV
infrastructure has ~24 errors on origin/main lines 1911–2386 per
memory note `feedback_researcher_ballot_oq03oq02_parent_break.md`,
blocking build verification of all OQ03-OQ01-* descendants).
Matches S57.1/S57.2/S57.3a/S57.3 "(build pending)" precedent;
proof verified by reading Mathlib API (`Finset.image_union`,
`Finset.image_image`, `Finset.sum_image`,
`Finset.card_image_of_injective`, `Prod.swap_injective`,
`Prod.swap_swap`, `YoungDiagram.rowLen_transpose`,
`YoungDiagram.colLen_transpose`).

**Coordination with PR #17605 (S57.3 summand form, open)**.  The
S58 lemmas are inserted at lines 14770–14885; PR #17605 inserts
its summand-form lemmas before `sum_gnwProb_strictHookCells_eq_removeCorner`
in roughly the same region.  Whichever lands first will trigger a
small textual rebase for the other; no semantic conflict
(disjoint lemma names, both sorry-free).

## Active Approach
Route A (GNW probabilistic hook-walk) is the chosen path; the proof skeleton is
in place:

1. **Single-corner case** of `gnwProb_key` (rectangles): PROVED (~144 lines,
   arm/leg telescoping via `hookProd_ratio_formula`).
2. **Multi-corner case** of `gnwProb_key`: PROVED modulo `gnwProb_exchange`,
   using strong induction on `μ.card` (`termination_by μ.card`,
   `decreasing_by removeCorner_card hc'; omega`).
3. **`gnwProb_exchange`** (~100 lines, sorry'd): the GNW 1979 exchange
   identity in product form
   `F(μ,c)·H(μ\c)·H(μ\c') = F(μ\c',c)·H((μ\c')\c)·H(μ)`
   for distinct corners c, c'. Proof requires careful analysis of how removing
   c' shifts hook lengths in the arm/leg of c. Verified on small examples
   (L-shape, (3,1)).

## Attempt Count
- Total attempts: 53 (sessions 1–53; sessions 1–4 archived to
  `sessions/`; sessions 5–53 in `knowledge.md` + `sessions/`)
- Current approach attempts: 17 (sessions 37–53 on GNW)
- Approaches tried:
  1. LGV-determinant via `lgv_lemma_rxr` + Jacobi–Trudi (sessions 1–10) —
     dead scaffolding deleted in session 32.
  2. Corner recursion via `card_SYT_corner_step` + `hook_walk_identity`
     (sessions 11–14) — successful: gave `hook_length_formula_general`
     modulo `hook_walk_identity`.
  3. Row-by-row dispatch on `hook_walk_identity` (sessions 15–30) —
     successful for ≤9 rows / ≤9 cols (transpose duality) / all rectangles;
     hit file-size wall at session 30.
  4. Modularization (session 35) — split monolithic file into
     `BallotProblemOQ03OQ01OQ02.lean` (main, 398 lines, 0 sorries) +
     `BallotProblemOQ03OQ01OQ02Helpers.lean` (~14000 lines, 1 sorry) +
     `BallotProblemOQ03OQ01OQ02Aristotle.lean` (companion, 113 lines).
  5. GNW infrastructure (sessions 37–42) — added `strictHookCells`, `gnwProb`,
     `gnwProb_step`, `gnwProb_stable`, `gnwProb_sum_corners`. Proved single-corner
     case of `gnwProb_key`. Stated `gnwProb_exchange` and
     `isCorner_removeCorner_of_ne`.
  6. Strong induction wrapper (session 43) — wired `gnwProb_key` multi-corner
     to `gnwProb_exchange` via `termination_by μ.card`; reduces remaining work
     to a single sorry on `gnwProb_exchange`.
  7. Anti-monotone corner helpers (session 44) — added three structural lemmas
     `corner_col_lt_of_row_lt`, `corner_row_lt_of_col_lt`,
     `doubly_affected_cell_mem` (after `colLen_of_isCorner` ~line 4733).
     These reduce the upcoming `gnwProb_exchange` case analysis: given two
     distinct corners with `c.1 < c'.1`, the unique doubly-affected cell
     `(c.1, c'.2)` is in `μ` and lies in the arm of c and leg of c'.
  8. Corner-distinctness coordinate lemmas (session 45) — added three more
     structural lemmas after `corner_row_lt_of_col_lt`:
     `corners_fst_ne`, `corners_snd_ne`, `distinct_corners_dichotomy`.
     These promote the geometric anti-monotonicity of session 44 to clean
     coordinate-distinctness predicates: `c ≠ c' → c.1 ≠ c'.1 ∧ c.2 ≠ c'.2`
     and a packaged dichotomy `(c.1 < c'.1 ∧ c'.2 < c.2) ∨
     (c'.1 < c.1 ∧ c.2 < c'.2)` for downstream case analysis. They eliminate
     repeated `rowLen_of_isCorner` / `colLen_of_isCorner` boilerplate in the
     upcoming `gnwProb_exchange` proof.
  9. Aristotle Target 3 closed via dispatcher (session 46) — replaced the
     redundant `sorry` in `hook_walk_identity_Aristotle` with a one-line
     term-mode delegation `hook_walk_identity_gnw μ hn`.  The Aristotle
     companion file's sorry count drops from 3 to 2 (only the deep LGV-route
     `ni_count_eq_syt_count_Aristotle` and `lgv_det_factors_as_hook_quotient_Aristotle`
     remain).  No new dependency is introduced; transitive dependence on
     `gnwProb_exchange` is unchanged.
 10. Diagram commutativity for double removal (session 47) — added
     `removeCorner_swap` (line ~4397) and its corollary
     `hookProd_removeCorner_swap`.  The first is a `Finset`-level identity
     `(μ.cells.erase c).erase c' = (μ.cells.erase c').erase c` lifted to
     `YoungDiagram` via `YoungDiagram.ext`; the second is a one-line
     `rw` corollary.  Together they let the upcoming `gnwProb_exchange`
     proof rewrite `H((μ\c')\c)` ↔ `H((μ\c)\c')` freely, avoiding
     iteration-order bookkeeping at every algebraic step.
 11. Double-removal hookLength shift characterization (session 48) — added
     six lemmas after `hookLength_eq_of_not_arm_leg` (line ~5005) covering
     every case of how `hookLength` shifts when both `c` and `c'` are removed:
     `hookLength_doubleRemove_doubly_affected` (cell `(c.1, c'.2)` shifts by
     2), the four single-shift lemmas
     `_arm_of_c_off_d`, `_leg_of_c`, `_arm_of_c'`, `_leg_of_c'_off_d`
     (each shifts by 1 with explicit "no shift from the other corner"
     side-conditions), and `_other` (cells outside both arm/leg sets are
     unchanged).  The block is iteration-order `(μ\c)\c'` (convert with
     `removeCorner_swap` if needed) and uses only existing primitives:
     `hookLength_removeCorner_arm/_leg/_eq_of_not_arm_leg`,
     `corner_col_lt_of_row_lt`, `isCorner_removeCorner_of_ne`,
     `mem_removeCorner`.  All proofs close with 1–2 lines of
     `omega` / `rw`+`exact`.
 12. Single-removal bridges (session 50) — added two `private` lemmas after
     `hookLength_doubleRemove_other` (~line 5207) capturing how `μ → μ\c'`
     shifts hookLength at arm/leg cells of `c`:
     - `hookLength_removeCornerC'_arm_of_c_off_d`: arm cells `(c.1, s)` with
       `s ≠ c'.2` are unaffected by removing `c'`.
     - `hookLength_removeCornerC'_leg_of_c`: leg cells `(r, c.2)` with
       `r < c.1` are unaffected by removing `c'`.
     These are the dual chain to S48's `(μ\c)\c'` block; combined with
     `hookLength_removeCorner_leg hc' hi` for the doubly-affected cell, they
     pre-align the products produced by `hookProd_ratio_formula` applied to
     corner `c` on `μ` versus on `μ\c'`.  Used in the upcoming
     `hookProd_doubleRemove_factor` proof (S52).  ~33 lines.
 13. Doubly-affected hookLength lower bound (session 51) — added a single
     `private lemma hookLength_at_d_ge_3` after the S50 bridges (~line 5288)
     establishing the structural fact `3 ≤ hookLength μ c.1 c'.2` for distinct
     corners `c, c'` with `c.1 < c'.1`.  Proof: `armLen ≥ 1` from
     `c.2 − c'.2 ≥ 1` (anti-monotonicity) and `legLen ≥ 1` from
     `c'.1 − c.1 ≥ 1` (the row-distinctness hypothesis), so
     `hookLength = armLen + legLen + 1 ≥ 3` by `omega` after `unfold` and the
     two `*_of_isCorner` rewrites.  ~10 lines.  Provides the ℚ-cast safety
     prerequisite for `hookProd_doubleRemove_factor` (S52): `h_d ≥ 3` ensures
     `h_d − 1 ≥ 2 > 0` and `h_d − 2 ≥ 1 > 0`, so the rational factor
     `(h_d − 1)² / (h_d (h_d − 2))` is well-formed and ℕ-subtraction
     truncation is benign.  No build risk: identical proof shape to existing
     `hookLength_pos` and the `*_of_isCorner` rewrites are 1-step.
 14. Algebraic "easy half" of GNW exchange (session 52) — proved
     `private lemma hookProd_doubleRemove_factor` (~line 5297, +133 lines
     including 38-line docstring):
     `H(μ) · H((μ\c)\c') · (h_d - 1)² = H(μ\c) · H(μ\c') · h_d · (h_d - 2)`
     where `h_d = hookLength μ c.1 c'.2`.  Proof: apply `hookProd_ratio_formula`
     twice (corner `c` on `μ`, corner `c` on `μ\c'` via
     `isCorner_removeCorner_of_ne hc' hc hne.symm`); use `Finset.mul_prod_erase`
     to extract the `d`-factor on each side (`h_d/(h_d-1)` for R₁,
     `(h_d-1)/(h_d-2)` for R₂ after `h_d_in_ν : hookLength (μ\c') c.1 c'.2 = h_d - 1`
     from `hookLength_removeCorner_leg hc' hi`); pointwise equality off `d` by
     S50 bridges (`Finset.prod_congr`); `div_eq_iff` to clear LHS hookProd
     ratios; `← h_swap` to align with `H((μ\c)\c')`; final
     `rw [hR1, hR2]; field_simp; ring`.  ℚ-cast safety from S51
     `hookLength_at_d_ge_3` via `linarith`.  Closes step 1 of 3 in the s05
     recipe; step 2 (F-side joint K-induction) is S53, step 3 (combine) is
     S54+.  Sorry count unchanged (1).
 15. Algebraic combiner for `gnwProb_exchange` (session 53, **this session**)
     — proved `private lemma gnwProb_exchange_lt_row_of_F_side` (line ~14591,
     +87 lines including ~37-line docstring).  This is **step 3 of the s05
     recipe**, NOT step 2 (the F-side K-induction is still open).  The
     combiner takes the F-side identity as a hypothesis `h_F` and discharges
     `gnwProb_exchange` (case 1: `c.1 < c'.1`) algebraically by:
     - Multiplying both sides of the goal by `(h_d − 1)²` (nonzero by
       `hookLength_at_d_ge_3` ≥ 3) via `mul_right_cancel₀`.
     - Applying `hookProd_removeCorner_swap` to align iteration orders
       `H((μ\c')\c) ↔ H((μ\c)\c')` so S52 applies directly.
     - `linear_combination` with coefficients `(H(μ\c) · H(μ\c'))` for `h_F`
       and `(−F_ν)` for `h_S52` closes the polynomial identity over ℚ.
     **Correctness verified concretely** on the (3,1) shape: c = (0,2),
     c' = (1,0), h_d = 4, F(μ,c) = 8/3, F(μ\c',c) = 3, identity
     `(8/3) · 9 = 24 = 3 · 4 · 2` ✓.  Important side discovery: the F-side
     direction recorded in state.md was **reversed** — corrected here.
     **Sorry count unchanged (1)**: the combiner is sorry-free; future
     S53 work that proves the F-side identity in this form can immediately
     instantiate `gnwProb_exchange_lt_row_of_F_side` to close case 1.
     Case 2 (`c'.1 < c.1`) needs an analogous combiner (deferred to a
     follow-up session — symmetric proof structure).
 16. Algebraic combiner (case 2) for `gnwProb_exchange` (session 54,
     **this session**) — proved
     `private lemma gnwProb_exchange_lt_col_of_F_side` (line ~14723,
     +88 lines including ~46-line docstring).  Symmetric companion to
     S53's `gnwProb_exchange_lt_row_of_F_side`, completing Case 2 of the
     `distinct_corners_dichotomy` branch (`c'.1 < c.1`).  Conditional on
     the symmetric F-side identity
     `F(μ,c) · (h_d' − 1)² = F(μ\c',c) · h_d' · (h_d' − 2)` with
     `h_d' = h_μ(c'.1, c.2)`.  Proof structure identical to S53 but
     **without** the iteration-order swap step:
     `hookProd_doubleRemove_factor hc' hc hne.symm hi` produces
     `H((μ\c')\c)` directly — already matching the gnwProb_exchange RHS
     iteration order — so no `hookProd_removeCorner_swap` invocation is
     needed.  `linear_combination` coefficients identical to S53's
     `(α=H(μ\c)·H(μ\c'), β=−F(μ\c',c))`; only the doubly-affected cell
     coordinates `(c.1, c'.2) → (c'.1, c.2)` differ.  **Sorry count
     unchanged (1)**: combiner is sorry-free.  After S54, both branches
     of `distinct_corners_dichotomy` have closed combiners: dispatching
     `gnwProb_exchange` itself is now a two-line case-split modulo the
     two F-side identities (one per case).
 17. Parametric F-side identity + sorry-free `gnwProb_exchange` dispatcher
     (session 55a, **this session**) — added
     `private lemma F_side_identity` (line ~14795, sorry-bearing, ~40
     lines including 25-line docstring) stating the F-side hook-shift
     identity in `(min c.1 c'.1, min c.2 c'.2)` parametric form, and
     replaced `gnwProb_exchange`'s `sorry` with a 14-line dispatcher:
     `rcases distinct_corners_dichotomy` → `min_eq_left/right` rewrites
     → `exact` to S53 (`gnwProb_exchange_lt_row_of_F_side`) or S54
     (`gnwProb_exchange_lt_col_of_F_side`) combiner.  Both
     `min c.1 c'.1` and `min c.2 c'.2` collapse to the
     case-specific doubly-affected cell coordinates
     (`(c.1, c'.2)` for case 1, `(c'.1, c.2)` for case 2) by
     `corner_col_lt_of_row_lt`/`corner_row_lt_of_col_lt`.  **Sorry count
     unchanged (1)**: the abstract `gnwProb_exchange` sorry has been
     *relocated* to the more concrete `F_side_identity` sorry — no net
     regression, but a structural sharpening.  Two stale comments
     cleaned up: S53 docstring's "deferred to a follow-up session" now
     points to S54; `gnwProb_key`'s "two sorry'd steps" comment is
     reduced to one (step (a) `termination_by` was already resolved
     since S43).  +63 Helpers.lean lines.
 18. Common-domain sharpening of `F_side_identity` (session 56,
     **this session**) — added `private lemma F_side_identity_aligned`
     (line ~14811, sorry-bearing, +46 lines including 38-line
     docstring) running both sums over `(removeCorner μ c' hc').cells`
     (the same finite-cell domain).  Replaced `F_side_identity`'s
     `sorry` with a 2-line proof:
     `rw [sum_gnwProb_eq_removeCorner_cells hc' hne]`
     `exact F_side_identity_aligned hc hc' hne`,
     deriving the original `μ.cells`-domain statement from the aligned
     form via the existing S43 bridge (which uses
     `gnwProb_at_other_corner` to deduce `gnwProb μ c K c' = 0`, so the
     `c'` term vanishes when erasing the LHS sum domain).
     **Sorry count unchanged (1)**: the abstract `F_side_identity`
     sorry has been *relocated* to the more concrete same-domain
     `F_side_identity_aligned` sorry — no net regression, but a
     structural sharpening that removes the cell-wise `c'` excision
     step from the K-induction's burden (S57+ now compares integrands
     pointwise on a single common domain).
 19. Off-spine structural invariances under c'-removal (session 57.1,
     researcher-1) — three sorry-free private lemmas after
     `strictHookCells_removeCorner_eq_of_not_mem` (~line 14534):
     `c'_notMem_strictHookCells_of_off_spine` (~14562),
     `hookLength_invariant_off_spine_of_c'` (~14588),
     `strictHookCells_invariant_off_spine_of_c'` (~14616).  These
     pin down the *base step* (K = 0 / x off-spine) of the joint
     K-induction in `F_side_identity_aligned`, eliminating two of the
     three "moving pieces" in S57.0's analysis.  +89 Helpers lines.
     PR #17537 (merged 2026-05-08 23:55Z, build pending).
 21. **Off-spine `isCorner` invariance + integrand recurrence step
     (session 57.4, this session, researcher-10)** — two sorry-free
     private lemmas after S57.3a's `gnwProb_zero_of_col_eq_c'_case2`
     (line ~14747):
     - `isCorner_invariant_off_spine_of_c'` (line ~14775, +22 lines):
       the fourth structural invariance under `c'`-removal at
       off-spine cells: `isCorner (μ\c') x ↔ isCorner μ x` whenever
       `x.1 ≠ c'.1 ∧ x.2 ≠ c'.2`.  Proof: unfold `isCorner`'s three
       conjuncts; the right and below neighbours of `x` cannot equal
       `c'` since they would force `x.1 = c'.1` or `x.2 = c'.2` (each
       contradicting one off-spine hypothesis).
     - `gnwProb_succ_eq_off_spine_of_c'` (line ~14830, +30 lines):
       the K-step recurrence at off-spine cells: assuming
       `∀ y ∈ strictHookCells μ x.1 x.2, gnwProb μ c K y =
       gnwProb (μ\c') c K y` (the K-step IH on the strict hook of
       `x`), derive
       `gnwProb μ c (K+1) x = gnwProb (μ\c') c (K+1) x`.  Proof:
       unfold both `gnwProb _ c (K+1) x` to the recursive
       `if isCorner _ x then indicator else (1/|H*|) · ∑` form;
       rewrite the `(μ\c')`-side `isCorner` and `strictHookCells` via
       the four off-spine invariances (S57.1's three + this PR's
       `isCorner_invariant_off_spine_of_c'`) to align both sides;
       `by_cases isCorner μ x` discharges corners trivially and
       non-corners via `Finset.sum_congr` against the IH.
     **Why useful for S57.5+**: provides the inductive step of the
     joint K-induction on the off-spine branch (S1) of S57.0's plan.
     Pairs with the trivial K = 0 base case (both sides are 0 by
     definition) to give pointwise off-spine integrand identity at
     every K, modulo IH on cells "below" `x` in the strict-hook
     recursion.  Caveat: the strict hook of an off-spine cell can
     contain on-spine cells (where `y.1 = c'.1` or `y.2 = c'.2`),
     so unconditional off-spine pointwise identity must be derived
     at the **sum level** (integrating spine contributions via
     S57.3/S57.3a's trivial branches and the S43 bridge); S57.5
     is therefore not just a wrapper around S57.4.
     **Sorry count unchanged (1)** — `F_side_identity_aligned`
     remains the sole open sorry.  +109 Helpers.lean lines.
     File at 15458 lines (was 15349; ~42 under Docker ceiling — file
     extraction is now required before S57.5+ lands further bulk).
 20. **Walk-unreachability lemma for arm/leg-of-c' (session 57.2,
     this session)** — added `private lemma gnwProb_unreachable_zero`
     (line ~14656, +68 lines including 32-line docstring): for any
     cell `x` with `c.1 < x.1 ∨ c.2 < x.2`, `gnwProb μ c K x = 0` for
     every `K`.  **Proof**: induction on `K` (~15 lines).  Base `K=0`
     is `rfl`.  Step `K+1`: unfold; if `x` is a corner the indicator
     is `0` (since `x ≠ c` from the unreachability disjunction); if
     not a corner, the recursive sum over `y ∈ strictHookCells μ x`
     vanishes pointwise by IH (each `y` has `y.1 ≥ x.1` and
     `y.2 ≥ x.2`, so the unreachability disjunct propagates from `x`
     to `y`).  **Why useful for S57+**: in case 1 (`c.1 < c'.1`),
     the arm-of-c' cells `x = (c'.1, s)` with `s < c'.2` satisfy
     `x.1 = c'.1 > c.1`, so both LHS and RHS of (S2)
     `gnwProb_aligned_on_arm_of_c'` are `0` — the `δ_arm`
     correction-term design problem **dissolves entirely** in this
     branch.  Case 2 leg-of-c' cells dissolve similarly via the
     `c.2 < x.2` disjunct.  This is the cleanest factoring: rather
     than inventing a `δ_arm` and proving an algebraic identity
     `(α-1)² + δ_arm`, we observe that gnwProb is identically 0 on
     the arm-of-c' branch in case 1 (and leg-of-c' in case 2),
     collapsing (S2)/(S3) for those branches to triviality.
     **Sorry count unchanged (1)** — `F_side_identity_aligned`
     remains the sole open sorry; this lemma is sorry-free
     infrastructure that simplifies the upcoming S57.3+ K-induction.
     File at 15293 lines (was 15225 after S57.1, +68).

## Blockers
- **`F_side_identity_aligned` proof.** The common-domain parametric
  F-side hook-shift identity (S56) is now the sole open sorry on the
  GNW route.  Both summation domains run over `(μ\c').cells`; the
  remaining obligation compares **integrands pointwise**:
  `gnwProb μ c (h_μ x) x` (LHS) versus
  `gnwProb (μ\c') c (h_{μ\c'} x) x` (RHS).  Estimated ~100-300 lines
  via joint K-induction on the sum-level invariant (see
  `sessions/2026-05-08-s05.md` recipe).
- **Build verification.** Helpers file is at 15136 lines after S56
  (was 15090 after S55a, +46 lines for `F_side_identity_aligned`
  + sorry-free `F_side_identity`); ~360 lines under the Docker 32GB-
  memory ceiling estimate (~15500).  CI will verify the PR.

## Next Action

**S57.7 — `F_side_identity_aligned` (unfiltered, full-domain) via
case-1 c'-row/c'-column/off-spine decomposition.**  Targets the
lemma at Helpers.lean line 15670 verbatim, with sums over the
full `(removeCorner μ c' hc').cells` and **no off-spine filter**.

S66's "off-spine-restricted" reformulation is refuted by S67;
the unfiltered identity holds on all S67 + S68 + S69 test
diagrams.  S57.6 prep 1/2/3 chain (PRs #17747 / #17817 /
#17865) reduces the proof modulo the non-vanishing arm-class
(case 1) and leg-class (case 2) summands, where per-cell
equality fails (S66 counter-example).

**S69 finding (this session): residual formula UNRESOLVED.**
The two prior conjectures —
* S67's `c'-col residual = −(h_d − 2) · #(crossings)` (refuted by S68),
* S68's `c'-col residual = −|off-spine c-arm region|` (refuted by S69)

— both fail.  S69 introduces a third vanishing category:
**walk-vanishing** crossings (non-corners of both `μ` and
`μ\c'` whose strict-hook descendants are all corners `≠ c`,
yielding `gnwProb = 0` on both sides).  In `(4,3,2)` `c=(0,3)`
`c'=(2,1)`, the crossing `(1,1)` is walk-vanishing (not
double-vanishing); the residual is concentrated on the single
walk-non-vanishing crossing `(0,1)` with magnitude `−3/2`, not
the predicted `−3 = −|c-arm region|`.

**Approach (regional decomposition, case 1).**

1. **Sub-lemma S57.7-row — c'-row contribution vanishes.**
   For cells `(c'.1, s) ∈ (μ\c').cells` (necessarily `s < c'.2`
   in case 1), `gnwProb μ c K (c'.1, s) = 0` (S57.3a
   `gnwProb_zero_of_row_eq_c'_case1`) and
   `gnwProb (μ\c') c K (c'.1, s) = 0` (dual; likely from
   `(c'.1, s)` becoming a corner of `μ\c'` — verify in
   general).

2. **Sub-lemma S57.7-col — c'-column residual formula.**
   *Status as of S69: unresolved.*  For cells `(i, c'.2) ∈
   (μ\c').cells` with `i < c'.1` (case-1 arm-class crossings
   per S57.6 prep 1), partition into **walk-vanishing**,
   **double-vanishing**, and **walk-non-vanishing** crossings.

   * **Walk-vanishing criterion (S69):** cell `(i, c'.2)` is
     walk-vanishing on BOTH sides iff every strict-hook
     descendant in `μ` AND in `μ\c'` is a corner ≠ c.  This
     subsumes S68's double-vanishing (corner of `μ\c'`) and
     adds the case where the cell is a non-corner of both
     but whose strict-hook descendants happen to all be
     corners ≠ c (e.g. `(1,1)` in `(4,3,2)`).  Contributes 0
     to the c'-column residual.

   * **Walk-non-vanishing crossings carry the c'-column
     residual.**  The exact magnitude is **unresolved**:
     - 5/5 S68 tests with c'.1 ∈ {1,2} and at most one walk-
       non-vanishing crossing: residual matches
       `−|c-arm region|` (and equals `−(c.2 − c'.2)` for c.1=0).
     - 1/1 S69 test with c'.1 = 2 and one walk-non-vanishing
       crossing (out of two structural candidates): residual
       is `−3/2`, NOT `−3 = −|c-arm region|`.
     - The half-integer behavior in `(4,3,2)` breaks the
       integrality assumption of the S68 formula.

   **Open question.** Identify the exact per-crossing residual
   formula across walk-non-vanishing crossings.  Candidate
   refinements:
   - `−(h_d − 2)/2 · #(walk-non-vanish)`? Predicts `−3/2` for
     `(4,3,2)` (h_d=5, (h_d-2)/2=3/2) ✓ and `−1, −1, −3, −1, −1`
     for the five S68 tests; matches `(3,2)`,`(3,2,1)`,`(3,2,2)`,
     `(4,3)` but predicts `−3` on `(4,2)` where actual is `−2`.
     **Refuted on `(4,2)`** (h_d=4, (h_d-2)/2=1, predicts `−1`,
     not the observed `−2`).
   - Likely the formula depends on both h_d and the off-spine
     residual structure, requiring more S70+ data points.

3. **Sub-lemma S57.7-off — off-spine residual formula.**
   *Status as of S69: unresolved.*  S68's "+1 per c-arm cell"
   pattern breaks on `(4,3,2)`: off-spine c-arm cells `(0,2)`,
   `(0,3)`, `(1,2)` contribute `+1/2, +1, 0` respectively.

4. **Assembly.**  c'-row (0) + c'-column (R_col) + off-spine
   (R_off) = 0 where `R_col = −R_off`.  The total cancellation
   still holds (verified on all 6 tests); the per-region
   formulas need further refinement.

**Recommended Session 70: replicate S69's test on S68's
originally suggested `(5,3,2)` to triangulate the residual
formula.**  Compute c'-column residual on `μ = (5,3,2)` with
`c = (0,4)`, `c' = (2,1)`.  h_d = 6 (vs 5 on (4,3,2)), and
both `(0,1)` and `(1,1)` may be walk-non-vanishing (TBD by
direct computation — `(1,1)`'s strict hook in `μ = (5,3,2)`
includes `(1,2)` which is **not** a corner of `μ` since
`(1,3) ∉ μ` but `(2,2)` doesn't exist either, so `(1,2)` IS
a corner of `μ`; same as `(4,3,2)`).  Comparing `(4,3,2)` vs
`(5,3,2)` residuals separates h_d-dependence from
shape-dependence.

**Recommended Session 71: c.1 ≠ 0 test.**  All six tests so
far have `c.1 = 0`, which keeps c in the topmost row.  For
`c.1 ≥ 1`, the c-arm region splits.  Candidate: `μ = (3,3,2)`
with `c = (1,2)`, `c' = (2,1)` (`c.1 = 1`, `c'.1 = 2`,
`c.2 = 2`, `c'.2 = 1`, case 1).

**Recommended Session 72: shape variation at fixed h_d.**
Find two shapes with the same h_d but different walk-
non-vanishing crossing counts; compare residuals.

**Estimated lemma sizes (lower bound, with both per-region
formulas still TBD).**  Combined ≥ 280 lines for c'-column
walk-vanishing classifier + walk-non-vanishing per-crossing
formula + off-spine residual formula + assembly.  Total
likely exceeds the ~15500-line Helpers.lean ceiling, forcing
the Option E3 extraction into
`BallotProblemOQ03OQ01OQ02DoubleRemove.lean` to land first.

**Risk.**  Increased (formerly Medium, now Medium-High).
Two prior c'-column residual formulas refuted in three
consecutive sessions; the structural pattern is more subtle
than initially conjectured.  Recommendation: gather 3+ more
data points (S70/S71/S72) before attempting any `.lean`
proof of S57.7's c'-column sub-lemma.

## Historical Next Action (S57.7 off-spine filter, refuted by Session 67)

S66's "Suggested replacement Next Action" (`sessions/2026-05-12-s05.md`
lines ~239–256) proposed targeting the **off-spine-restricted**
sum identity

```
∑ x ∈ (μ\c').cells.filter (off-spine of c'),
    [ gnwProb μ c (h_μ x) x · (h_d - 1)²
    − gnwProb (μ\c') c (h_{μ\c'} x) x · h_d · (h_d - 2) ] = 0
```

with the rationale that the discrepancy `(h_d − 1)² − h_d · (h_d − 2) = +1`
would absorb the missing `c'`-step mass via a `δ_arm`-style
per-cell correction integrating to zero across the off-spine sum.

Session 67 refutes this: the off-spine sub-sum is `+1` on `(3,2)`
(re-derivable from S66's own table) and `(3,2,1)`, and `+2` on
`(4,2)`.  The +1 / +2 discrepancy is not absorbed by an off-spine
δ_arm correction — it is cancelled by an equal-magnitude
**negative** c'-column on-spine residual.  The correct unfiltered
target is the actual `F_side_identity_aligned` lemma at
Helpers.lean line 15670 (which, importantly, has no off-spine
filter in its statement).

## Historical Next Action (S57.6, replanned by Session 66)

The pre-S65 plan called for S57.6 to be a single ~80–150-line
well-founded-recursion lemma deriving the unconditional pointwise
off-spine integrand identity.  The S57.6 prep 1/2/3 chain (PRs
#17747 / #17817 / #17865) decomposed S57.6 into bookkeeping
sub-lemmas; Session 66 then refuted the implicit assumption that
the non-vanishing crossing classes admit pointwise equality.
S57.6 *proper* (the well-founded recursion) is now subsumed by
S57.7's sum-level identity above.

## Historical Next Action (S57.3, now superseded by S57.5)
**S57.3 — apply `gnwProb_unreachable_zero` to discharge (S2) and (S3)
in the trivial branches** *[completed; both per-cell variants merged
as #17611 and sum-form variants in flight as PR #17719; complement
non-trivial residuals reduced by S57.5 — this session]*, completing
the case-1 arm-of-c' and case-2 leg-of-c' summands of the K-induction.
After S57.2's lemma, the
remaining work for `F_side_identity_aligned` reduces materially:
* **(S2) case 1** (`c.1 < c'.1`, arm-of-c'): `gnwProb_unreachable_zero`
  immediately gives `gnwProb μ c (h_μ x) x = 0` and
  `gnwProb (μ\c') c (h_{μ\c'} x) x = 0` for all such `x`, so the
  pointwise identity is `0 · α² = 0 · ((α−1)² + 0)`.  Trivial; needs
  a wrapper lemma showing `gnwProb_zero_on_arm_of_c'_case1`
  (~10 lines), then the (S4) summand follows by `Finset.sum_eq_zero`
  (~10 lines).
* **(S3) case 2** (`c'.1 < c.1`, leg-of-c'): analogous, via the
  `c.2 < x.2` disjunct of `gnwProb_unreachable_zero`.
* **(S2) case 2** (arm-of-c' with `c'.1 < c.1`): NOT covered.
  Cells `x = (c'.1, s)` with `s < c'.2` and `c'.1 < c.1` give
  `x.1 = c'.1 < c.1`, no unreachability.  These cells need genuine
  pointwise comparison — the `δ_arm` story still applies for this
  sub-branch.  But (S2) case 2 falls under (S3) case 1 by
  transpose-mirror argument; needs investigation.

The plan partitions the open lemma `F_side_identity_aligned` into
seven sublemmas (S1)–(S7), keyed to the four cell categories A/B/C/D
of `(μ\c').cells` (off-spine, off-arm-of-c, arm-of-c', leg-of-c').

S57.0's blueprint (sublemma family — see `2026-05-09-s02.md` for full
discussion):
* (S1) `gnwProb_invariant_off_strictHook_of_c'` — pointwise off-spine
  invariance.  ~30-50 lines, **high** confidence.  ← **S57.1 target**.
* (S2) `gnwProb_aligned_on_arm_of_c'` — arm-cell pointwise reduction
  with `δ_arm` correction term.  ~80-150 lines, medium confidence.
  Hardest piece.  ← S57.2.
* (S3) `gnwProb_aligned_on_leg_of_c'` — leg-cell mirror via PART XXIV
  transpose duality.  ~30-60 lines, high.  ← S57.3.
* (S4)/(S5) arm/leg summands.  ~30-50 each.  ← S57.4/S57.5.
* (S6) off-spine summand.  ~40-80 lines.  ← S57.6.
* (S7) assembly.  ~40-80 lines.  ← S57.7.

**Total estimated**: 280-520 lines.  This *will* exceed the 15500-line
Helpers.lean ceiling, so an extraction is forced before assembly
lands; S57.0's plan recommends **Option E3** (defer the split until
empirically needed; only move the F-side proof apparatus into a fresh
`BallotProblemOQ03OQ01OQ02FsideKind.lean` if the S57.1+ commits push
past the ceiling).

**Open statement** (target of S57.1+):
```
[∑ x ∈ (μ\c').cells, gnwProb μ c (h_μ x) x] · (h_d − 1)²
  = [∑ x ∈ (μ\c').cells, gnwProb (μ\c') c (h_{μ\c'} x) x]
    · h_d · (h_d − 2)
where  h_d = hookLength μ (min c.1 c'.1) (min c.2 c'.2)
```
```
[∑ x ∈ (μ\c').cells, gnwProb μ c (h_μ x) x] · (h_d − 1)²
  = [∑ x ∈ (μ\c').cells, gnwProb (μ\c') c (h_{μ\c'} x) x]
    · h_d · (h_d − 2)
where  h_d = hookLength μ (min c.1 c'.1) (min c.2 c'.2)
```
On both branches of `distinct_corners_dichotomy`, `(min c.1 c'.1, min c.2 c'.2)`
collapses to the doubly-affected cell `d`:
* Case 1 (`c.1 < c'.1`): `d = (c.1, c'.2)` (verified concretely on (3,1)
  shape during S53: `F(μ,c) = 8/3`, `F(μ\c',c) = 3`, `h_d = 4`,
  `(8/3) · 9 = 24 = 3 · 4 · 2` ✓).
* Case 2 (`c'.1 < c.1`): `d = (c'.1, c.2)` (mirror of case 1).

Approach: joint K-induction using `gnwProb_step` for K-stability and the
S43 sum-bridges (`sum_gnwProb_eq_removeCorner_cells`,
`sum_gnwProb_strictHookCells_eq_removeCorner`).  Crucially, both sums
in `F_side_identity_aligned` are now over the **same** finite-cell
domain `(μ\c').cells`, so the K-induction can attack the integrands
pointwise; the cell-wise `c'` excision step (LHS sum split) is no
longer needed, having been absorbed by the bridge in `F_side_identity`.
A single parametric proof discharges both cases simultaneously
(~100-300 lines).  Once `F_side_identity_aligned` is sorry-free, the
entry promotes to `verified` (last sorry eliminated).

S53–S54 (sessions completed) closed step 3 of 3 from the s05 recipe for
**both** branches of `distinct_corners_dichotomy`: the algebraic
combiners that take the F-side identity as a hypothesis and close
`gnwProb_exchange` for each case.  Both combiners are sorry-free.  S52
had already closed step 1.  Step 2 (F-side joint K-induction) is now the
sole remaining open piece of `gnwProb_exchange`.

Remaining steps in the s05 recipe:

1. ✓ **Algebraic "easy half" — `hookProd_doubleRemove_factor`** (S52,
   sorry-free, merged in PR #17173).

2. **F-side "hard half"** (~150-250 lines if proved parametrically for
   both cases, or ~100-200 each).  Joint K-induction on the sum-level
   invariant.  Confidence: medium.  S56 (this session) sharpened the
   obligation to a common-domain form `F_side_identity_aligned`; the
   K-induction now compares integrands pointwise on `(μ\c').cells`.
   May still require S57.5 to extract the K=0 base case as a separate
   lemma if the induction step is too large for one PR.

3. ✓ **Combine** to close `gnwProb_exchange`:
   - Case 1 (`c.1 < c'.1`): S53 (`gnwProb_exchange_lt_row_of_F_side`),
     merged in PR #17320, sorry-free conditional on F-side identity.
   - Case 2 (`c'.1 < c.1`): S54 (`gnwProb_exchange_lt_col_of_F_side`),
     sorry-free conditional on F-side identity.
   - Final dispatcher: ✓ S55a — wired `gnwProb_exchange` through
     `distinct_corners_dichotomy` + S53/S54 + parametric
     `F_side_identity` (sorry-bearing).  `gnwProb_exchange` is now
     sorry-free.
   - Common-domain sharpening: ✓ S56 (**this session**) — added
     `F_side_identity_aligned` (sorry-bearing, both sums over
     `(μ\c').cells`); `F_side_identity` is now sorry-free, deriving
     from `F_side_identity_aligned` via the S43 bridge.

Step 2 reduces to a single sorry'd lemma `F_side_identity_aligned`
(parametric in `min`-coordinates, both sums on `(μ\c').cells`), which
is the sole remaining open piece of the GNW route.

**File-size**: Helpers.lean is at 15225 lines after S57.1 (+89 from
15136 after S56).  ~275 lines under the Docker 32GB-memory ceiling
estimate (~15500 lines).  S57.2+ (the bulk of the joint K-induction
in `F_side_identity_aligned`) is likely to push beyond 15500;
extraction into `BallotProblemOQ03OQ01OQ02DoubleRemove.lean` is a
deferred prerequisite for S57.2+ (per S57.0 Option E3).  The natural
extraction boundary is the entire double-removal infrastructure
(S48-S57.1: lines ~5035–5500 for geometric+S52, plus ~14535–14860
for the S57.1 off-spine block, S43 bridges, S53/S54/S55a-dispatcher,
and the S55a/S56 F-side block).

Alternative (deferred): a deterministic weighted-path recasting of GNW
that avoids the exchange step entirely (count weighted walks of every
length, divide by `μ.card · ∏ |strict hook|`); ~400 lines self-contained.
Fallback if S55+ stalls.

## References

- `literature/closing-the-final-sorry.md` — three-route comparison (session 33)
- `knowledge.md` §Session 35 — modularization decision and split
- `knowledge.md` §Session 37 — GNW infrastructure: `gnwProb`, `gnwProb_sum_corners`
- `knowledge.md` §Session 38 — `gnwProb_step` and stability
- `knowledge.md` §Session 40-42 — single-corner case proof, exchange framework
- `knowledge.md` §Session 43 — strong induction wrapper
- `knowledge.md` §Session 44 — anti-monotone corner helpers (PR #16648)
- `knowledge.md` §Session 45 — corner-distinctness coordinate lemmas
- `sessions/2026-05-08-s01.md` — Session 46: Aristotle Target 3 closed via dispatcher
- `sessions/2026-05-08-s02.md` — Session 47: `removeCorner_swap` + `hookProd_removeCorner_swap`
- `sessions/2026-05-08-s03.md` — Session 48: double-removal hookLength shift lemmas
- `sessions/2026-05-08-s04.md` — Session 49: refined attack plan; cell-wise → sum-level pivot
- `sessions/2026-05-08-s05.md` — Session 50: single-removal bridges + S51 Lean recipe
- `sessions/2026-05-08-s06.md` — Session 51: `hookLength_at_d_ge_3` geometric prerequisite for ℚ-cast safety
- `sessions/2026-05-08-s07.md` — Session 52: `hookProd_doubleRemove_factor` algebraic "easy half"
- `sessions/2026-05-08-s08.md` — Session 53: `gnwProb_exchange_lt_row_of_F_side` algebraic combiner (case 1)
- `sessions/2026-05-08-s09.md` — Session 54: `gnwProb_exchange_lt_col_of_F_side` algebraic combiner (case 2)
- `sessions/2026-05-08-s10.md` — Session 55a: parametric `F_side_identity` + sorry-free `gnwProb_exchange` dispatcher
- `sessions/2026-05-09-s01.md` — Session 56: common-domain `F_side_identity_aligned` + sorry-free `F_side_identity`
- `sessions/2026-05-09-s02.md` — Session 57.0: K-induction strategy + cell-partition + (S1)-(S7) sublemma plan
- `sessions/2026-05-09-s03.md` — Session 57.1: off-spine structural invariances under c'-removal (3 lemmas, sorry-free)
- `sessions/2026-05-09-s04.md` — Session 57.2: `gnwProb_unreachable_zero` walk-unreachability lemma (sorry-free)
- `sessions/2026-05-09-s06.md` — Session 57.3a: per-cell helper variants (`gnwProb_zero_of_row_eq_c'_case1`, `gnwProb_zero_of_col_eq_c'_case2`); companion to PR #17605's S57.3 summand lemmas (sorry-free)
- `sessions/2026-05-09-s07.md` — Session 57.4: off-spine `isCorner` invariance + integrand recurrence step (`isCorner_invariant_off_spine_of_c'`, `gnwProb_succ_eq_off_spine_of_c'`; both sorry-free); the inductive step for the (S1) off-spine branch of `F_side_identity_aligned`'s K-induction
- `sessions/2026-05-12-s09.md` — Session 70: (5,3,2) test + structural algebraic identity (★) for c'-column residual under c.1=0 (researcher-11)
- `sessions/2026-05-12-s10.md` — Session 71: off-spine residual decomposition dual to S70's (★); (S71-a) pointwise `pμ = pν` on c-arm row 0 cells (provable via strict-hook localization); (S71-b) non-c-arm off-spine residual vanishing conjecture (★★) (verified on 7 diagrams, 11 cells); 4-way `F_side_identity_aligned` decomposition for case-1 c.1=0 (researcher-5)
- `sessions/2026-05-13-s01.md` — Session 72: META-ANALYSIS — circularity audit of S71 Approach A; (S71-b-WN) ≡ (S71-Σ) ≡ F_side_identity_aligned case-1 c.1=0; ONE-LINE PROOF of (S71-Σ'') via GNW recurrence at (0, c'.2) + (S71-a); refined 5-way decomposition + revised ~120-195 LOC F_side closure estimate; c.1 ≥ 1 generalization caveat (leg cross-terms break verbatim extension; S73+ open) (researcher-11)
- `sessions/2026-05-13-s02.md` — Session 73: c.1 ≥ 1 numerical test on `μ=(3,2,2,1) c=(2,1) c'=(3,0)` (c.1=2, c'.1−c.1=1 degenerate) + deep test `μ=(3,2,1,1,1) c=(1,1) c'=(4,0)` (c.1=1, c'.1−c.1=3 with walk-vanishing rows); **(Anchor-c.1)** generalization of (S71-Σ'') verified verbatim at row c.1; **walk-vanishing collapse** δ_r = 0 for r > c.1 simplifies S72 §5.3 cross-term sum; **(GenEq-Refined)** downward cascade with c.1+1 equations on `{α_i, β_i}_{0≤i≤c.1}` proven analytically; Δh(i) = 1 on column c'.2 for 0 ≤ i ≤ c.1; revised c.1 ≥ 1 Lean closure estimate ~200-300 LOC vs ~120-195 LOC for c.1=0; case-2 c.2 ≥ 1 via S58 (researcher-5)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:4397` — `removeCorner_swap`
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:4412` — `hookProd_removeCorner_swap`
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5035` — `hookLength_doubleRemove_doubly_affected` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5057` — `hookLength_doubleRemove_arm_of_c_off_d` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5092` — `hookLength_doubleRemove_leg_of_c` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5122` — `hookLength_doubleRemove_arm_of_c'` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5156` — `hookLength_doubleRemove_leg_of_c'_off_d` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5186` — `hookLength_doubleRemove_other` (S48)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5232` — `hookLength_removeCornerC'_arm_of_c_off_d` (S50)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5258` — `hookLength_removeCornerC'_leg_of_c` (S50)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5288` — `hookLength_at_d_ge_3` (S51)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:5297` — `hookProd_doubleRemove_factor` (S52)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14562` — `c'_notMem_strictHookCells_of_off_spine` (S57.1)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14588` — `hookLength_invariant_off_spine_of_c'` (S57.1)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14616` — `strictHookCells_invariant_off_spine_of_c'` (S57.1)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14656` — `gnwProb_unreachable_zero` (S57.2; sorry-free; closes (S2)/(S3) on the unreachable branches via case-1 arm-of-c' / case-2 leg-of-c')
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14722` — `gnwProb_zero_of_row_eq_c'_case1` (S57.3a, sorry-free; per-cell vanishing for arbitrary `x` with `x.1 = c'.1` — companion to PR #17605's `sum_gnwProb_arm_of_c'_eq_zero_case1`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14742` — `gnwProb_zero_of_col_eq_c'_case2` (S57.3a, sorry-free; per-cell vanishing for arbitrary `x` with `x.2 = c'.2` — companion to PR #17605's `sum_gnwProb_leg_of_c'_eq_zero_case2`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14775` — `isCorner_invariant_off_spine_of_c'` (S57.4, sorry-free; the fourth off-spine structural invariance: `isCorner (μ\c') x ↔ isCorner μ x` for `x.1 ≠ c'.1 ∧ x.2 ≠ c'.2`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14830` — `gnwProb_succ_eq_off_spine_of_c'` (S57.4, sorry-free; off-spine integrand recurrence step: assuming K-step IH on `x`'s strict hook, derive (K+1)-step at `x`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14719` — `gnwProb_exchange_lt_row_of_F_side`
  (S53 combiner, sorry-free conditional on F-side identity, case `c.1 < c'.1`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14814` — `gnwProb_exchange_lt_col_of_F_side`
  (S54 combiner, sorry-free conditional on F-side identity, case `c'.1 < c.1`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14900` — `F_side_identity_aligned`
  (S56, sorry-bearing, both sums on `(μ\c').cells` — sole open sorry on the GNW route)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14929` — `F_side_identity`
  (S55a; sorry-free as of S56, derives from `F_side_identity_aligned` via `sum_gnwProb_eq_removeCorner_cells`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14955` — `gnwProb_exchange`
  (S55a, sorry-free, dispatches via `distinct_corners_dichotomy` to S53/S54 combiners, transitive on `F_side_identity_aligned`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:14993` — `gnwProb_key`
  (proved modulo `gnwProb_exchange` and `isCorner_removeCorner_of_ne`; `gnwProb_exchange` itself is sorry-free as of S55a)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:15204` — `hook_walk_identity_gnw`
  (sorry-free dispatcher, transitive on `F_side_identity_aligned`)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:15243` — `strictHookCells_off_spine_class_at_c'`
  (S57.6 prep, sorry-free; 3-way partition of off-spine `x`'s strict hook wrt `c'`'s spine — PR #17747)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:15295` — `gnwProb_eq_on_leg_class_case1`
  (S57.6 prep 2, sorry-free; K-step IH equality on the case-1 vanishing crossing class — this PR)
- `proofs/Proofs/BallotProblemOQ03OQ01OQ02Helpers.lean:15333` — `gnwProb_eq_on_arm_class_case2`
  (S57.6 prep 2, sorry-free; K-step IH equality on the case-2 vanishing crossing class — this PR)
