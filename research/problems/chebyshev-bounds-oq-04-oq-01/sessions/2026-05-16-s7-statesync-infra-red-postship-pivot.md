# Session 7 — STATE-SYNC: 3-RED INFRA escalation + post-S6-PREP stale-wording absorb

**Researcher**: researcher-6
**Wall clock**: 2026-05-16T20:15Z (S6 PREP merged T-11h20min ago at 08:55:05Z)
**Phase**: PREP (continuation — Iter 5a still the next analytic step; iteration counter unchanged)
**Scope**: 0 Lean changes. Doc-only consolidation: absorb 3 new RED INFRA
blockers on host, fix two stale "this PR" leftovers from S6 PREP's
write of `progressSummary` + `insights[11]`, reaffirm S6 PREP's split
sub-iter plan, restate the picker decision matrix for the next ACT
attempt under host-degraded conditions.

---

## 1. Why S7 fires (strict refinement, not deviation)

S6 PREP (#19455, researcher-9, merged 2026-05-16T08:55:05Z) shipped:

- `state.md` head replacement summarising Iter 4 merge absorption
- New session memo `2026-05-16-s6-prep-iter5a-symmetry-formula.md` (379 LOC)
  with full Mathlib bearer manifest at pin `2df2f0150c…`
- Research-JSON `phase` / `since` / `iteration` / `lastUpdate` / `focus` /
  `nextAction` / `knowledge.insights` / `knowledge.nextSteps` refresh
- Sub-iter split recommendation: 5a-α / 5a-β / 5a-γ (150–230 LOC total)
- Side-discovery flag: Mathlib has `Chebyshev.psi` natively, with upper-
  bound only (`psi_le_const_mul_self`); does NOT discharge parent's axiom

What S6 PREP did **not** anticipate (post-merge deltas):

1. **Stale "this PR" wording**: `currentState.focus`, `knowledge.progressSummary`,
   and `knowledge.insights[11]` each refer to "this PR" at session-author
   time. After S6 PREP merged, those phrases now refer to a merged PR
   (#19455 itself). Mild drift; readable as "S6 PREP this PR" if context
   is followed, but the JSON should be authoritative not write-time-anchored.
2. **Iter 4 wording**: `knowledge.progressSummary` opens with
   "Iter 4 (2026-05-16, build verified 7744 jobs, this PR) closes the
   literal Möbius-inversion form..." — the "this PR" there refers to
   Iter 4 (#19400), now merged 16h20min ago. Should be "(MERGED as PR
   #19400 at 2026-05-16T03:52:02Z)".
3. **3 RED INFRA blockers on host** (T-0 = now, 2026-05-16T20:15Z):
   - **G7 disk: 3.2 Gi available** on `/dev/disk3s5` (100% capacity).
     Below same-day soft floors set by adjacent slugs: shannon-channel-
     coding-oq-02 ACT @ 5.8 Gi, ballot-problem-oq-02-oq-05 ACT @ 5.4 Gi
     (per memory `_postship_pivot_to_act_ready_slug_where_single_prep_
     staged_skeleton_with_intentional_sorry_add_ship_act_under_build_
     pending` host disk forecast). 3.2 Gi forecloses any Docker Lean
     build at the current `7744`-job size (~4–8 Gi peak working set).
   - **G8 Docker: hung daemon**. `docker info` returns Client block
     populated but Server: (empty). Pattern matches `_postship_pivot_
     lands_on_act_slug_whose_just_merged_statesync_inherited_cross_prep_
     namespace_cite_regression` G8 RED and predecessor S6 PREP's bearer
     manifest cannot be re-verified via local lake build.
   - **G9 `proofs/.lake`: circular self-symlink** (`/Users/rwalters/
     GitHub/lean-genius/proofs/.lake → /Users/rwalters/GitHub/lean-
     genius/proofs/.lake`). Same pattern flagged in abel-ruffini-oq-04-
     oq-09 S7 STATE-SYNC #19755 (researcher-12, T-1h57min before this
     session start) and sqrt2-minpoly-oq-03 S6 STATE-SYNC #19760
     (researcher-12, T-1h36min). Confirms cross-slug repeatable host
     condition, not slug-local artifact.
4. **Mathlib pin unchanged**: `proofs/lake-manifest.json` rev still
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0). S6
   PREP's bearer manifest remains transitively SHA-stable.

S7 STATE-SYNC's scope is **strictly tighter** than S6 PREP: zero new
plan content, zero new bearer claims, zero Lean changes. It absorbs the
4 deltas above and reaffirms S6's plan unchanged.

---

## 2. 3-RED INFRA detail + recovery prescriptions

### 2.1 G7 disk — 3.2 Gi available (RED, 100%)

```
$ df -h /Users/rwalters
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   887Gi   3.2Gi   100%     21M   33M   39%   /System/Volumes/Data
```

**Same-day disk-floor table** (from session memos T-30h to T-0h):

| Wall clock (UTC) | Avail | Slug, session | Verdict |
|---|---:|---|---|
| 2026-05-15T17:00Z | ~7.0 Gi | shannon S17 PREP combined recipe | AMBER |
| 2026-05-15T22:55Z | ~6.9 Gi | lagrange S10 PREP paste-ready | AMBER |
| 2026-05-16T03:50Z | ~6.5 Gi | abel-ruffini S5 STATE-SYNC | AMBER |
| 2026-05-16T13:00Z (approx) | ~5.4 Gi | ballot S5 PREP combined skeleton | AMBER |
| 2026-05-16T14:30Z | ~5.8 Gi | shannon S18a-1 ACT def-only | AMBER (just under prior floor) |
| 2026-05-16T17:55Z | ~3.8 Gi | binomial S18 STATE-SYNC (researcher-10) | RED |
| 2026-05-16T18:35Z | ~3.3 Gi | abel-ruffini S7 STATE-SYNC (researcher-12) | RED |
| **2026-05-16T20:15Z** | **3.2 Gi** | **this S7 STATE-SYNC (researcher-6)** | **RED** |

Trend: monotone degradation ~0.6–1.5 Gi/h over the last 3h, suggesting
an ambient process (Docker volumes, /tmp accretion, or a runaway
worktree clone). G7 is foreclosing all post-T-17:55Z ACTs across
researchers 6/10/11/12; cross-researcher mechanic intervention has
been requested via the abel-ruffini S7 STATE-SYNC and parallel sqrt2-
minpoly S6 STATE-SYNC sibling.

**Recovery prescription** (host-side, not in scope for this PR):

```bash
# Identify Docker volume bloat (most likely culprit)
docker system df 2>&1 | head -20   # blocked by G8 hung daemon
# Alternate: direct disk inspection
du -hd 1 /Users/rwalters/Library/Containers/com.docker.docker/Data 2>&1 | tail
# Worktree cleanup
cd /Users/rwalters/GitHub/lean-genius && git worktree list | wc -l
# /tmp accretion
sudo du -hd 1 /private/tmp 2>&1 | sort -h | tail -10
```

### 2.2 G8 Docker — daemon hung (Server: section empty)

```
$ timeout 10 docker info 2>&1 | grep -E "^(Server|ERROR|Cannot|connect)"
Server:
(no further output — Server section never populated)
```

`docker info` exits 0 after returning only the Client: block, indicating
the daemon socket is alive but the engine itself is hung (matches
predecessor pattern across at least 4 same-wave slugs: abel-ruffini
S7 #19755, sqrt2-minpoly S6 #19760, binomial-theorem S18 STATE-SYNC,
this session). Recovery prescription (host-side, out of scope):

```bash
# Docker Desktop: Settings → Troubleshoot → Restart
# Or CLI:
killall Docker 2>/dev/null
open -a Docker
# Wait 30–60s, then:
docker info | head -20   # expect Server: section populated
```

### 2.3 G9 `proofs/.lake` — circular self-symlink

```
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  1 rwalters  staff  47 May 16 09:04
  /Users/rwalters/GitHub/lean-genius/proofs/.lake
  -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

`readlink` confirms the target equals the link itself. Same pattern
documented in abel-ruffini S6 PREP #19633 (researcher-11). Recovery
prescription: remove the symlink + recreate as a directory or as a
correct relative symlink (out of scope; requires Docker rebuild after
fix).

```bash
cd /Users/rwalters/GitHub/lean-genius/proofs
rm .lake                           # remove circular symlink
# Then re-run Docker build to repopulate .lake/packages from scratch
./scripts/docker-build.sh Proofs.ChebyshevBoundsOQ04OQ01
```

---

## 3. Stale "this PR" wording in JSON — fix in this session

Three loci in `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
carry "this PR" wording authored at S6 PREP write-time (now stale post-
merge):

| Field | Stale wording | Corrected wording |
|---|---|---|
| `currentState.focus` | "(researcher-9, 2026-05-16T04:37Z, doc-only, this PR)" | "(researcher-9, 2026-05-16T04:37Z, doc-only, MERGED as PR #19455 at 08:55:05Z)" |
| `knowledge.progressSummary` | "Iter 4 (2026-05-16, build verified 7744 jobs, this PR)" | "Iter 4 (2026-05-16, build verified 7744 jobs, MERGED as PR #19400 at 03:52:02Z)" |
| `knowledge.insights[11]` | "S6 PREP scope-honesty finding (2026-05-16, this PR)" | "S6 PREP scope-honesty finding (2026-05-16, MERGED as PR #19455 at 08:55:05Z)" |

These are factual corrections, not content rewrites. No insight or
plan content is altered.

---

## 4. 2-bearer spot-check (SHA-stability sample, not exhaustive walk)

Per `_SHA_stable_busywork` memory (recheck-all-N-bearers is busywork
when pin unchanged), this S7 STATE-SYNC spot-checks exactly two
bearers — one already in use at Iter 4, one staged for Iter 5a-α.

### 4.1 Iter 4 in-use bearer (regression sentinel)

**Bearer**: `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`
**File**: `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:240`
**Pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

```
theorem sum_eq_iff_sum_mul_moebius_eq [NonAssocRing R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (μ x.fst : R) * g x.snd = f n
```

Byte-stable vs Iter 4's cite. ✅ GREEN.

### 4.2 Iter 5a-α staged bearer (recipe sentinel)

**Bearer**: `sum_mul_eq_sub_integral_mul₀'`
**File**: `Mathlib/NumberTheory/AbelSummation.lean:229`
**Pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

```
theorem sum_mul_eq_sub_integral_mul₀' (hc : c 0 = 0) (m : ℕ)
    (hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) m, DifferentiableAt ℝ f t)
    (hf_int : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) m)) :
    ∑ k ∈ Icc 0 m, f k * c k =
      f m * (∑ k ∈ Icc 0 m, c k) -
        ∫ t in Set.Ioc (1 : ℝ) m, deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k := by
  ...
```

Byte-stable vs S6 PREP's manifest. ✅ GREEN.

### 4.3 Carry-forward rationale (no bearer recheck)

S6 PREP's full bearer manifest (10+ entries across `Moebius.lean`,
`Divisors.lean`, `AbelSummation.lean`, `SumIntegralComparisons.lean`,
`VonMangoldt.lean`) is **carry-forward valid by SHA-pin transitivity**:
the pin has not changed and 2-of-N spot-check confirms no surface
delta. Per memory traps (`_SHA_stable_busywork`, `_postship_pivot_to_
act_ready_rich_slug_with_predecessor_prep_escalation_and_single_disk_
degradation_delta_across_sameday_softfloor_ship_thin_statesync`):
1-spot-check spot-check, not 9/9 mechanical walk.

### 4.4 Net bearer-stability verdict

S6 PREP's bearer manifest remains **transitively SHA-stable** with
zero observed drift. The next ACT attempt (5a-α or 5a-β) inherits a
valid bearer manifest without amendment.

---

## 5. Readiness gate table (G1–G9)

| Gate | Iter 4 merge (T-16h20m) | S6 PREP merge (T-11h20m) | This S7 STATE-SYNC (T-0) |
|---|---|---|---|
| **G1** Mathlib pin | `2df2f0150c…` | `2df2f0150c…` (unchanged) | `2df2f0150c…` (unchanged) ✅ |
| **G2** Bearer manifest staged | — | 10+ at pin ✅ | 2-spot-check GREEN, transitive ✅ |
| **G3** No open PRs (slug) | 0 | 0 | 0 ✅ |
| **G4** Recipe paste-ready | — | YES (3 sub-iters) ✅ | YES (unchanged) ✅ |
| **G5** Build verification | 7744 jobs (Docker) ✅ | inherits Iter 4 ✅ | inherits Iter 4 ✅ |
| **G6** JSON ↔ state.md ↔ meta.json consistency | YES | YES (S6 PREP touched) | YES (this S7 fixes 3 "this PR" stales) ✅ |
| **G7** Disk avail | ~7 Gi | ~6.5 Gi | **3.2 Gi** ❌ RED |
| **G8** Docker | unknown (host snapshot not taken) | unknown | **hung (Server: empty)** ❌ RED |
| **G9** `.lake` symlink | — | — | **circular self-symlink** ❌ RED |

**Net**: Plan/recipe gates (G1–G6) all GREEN. Host gates (G7–G9) all
RED. ACT is structurally foreclosed at this wall-clock until host
recovers; doc-only iteration is the only safe path.

---

## 6. Picker decision matrix for S{8} (the next session)

Five rows covering all G7/G8/G9 combinations the next picker may face:

| # | G7 disk | G8 Docker | G9 `.lake` | Mathlib SHA | Recommended action |
|---|---|---|---|---|---|
| **R1** | ≥6.0 Gi | up | OK | unchanged | ACT 5a-α (Abel summation against `f(t) = (log t)²`, 60–90 LOC, 2–4 Docker iters) per S6 PREP §6. Per `_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier`, leaf-only file (zero importers besides this slug's parent) + recent BUILD-VERIFY (Iter 4 7744 jobs) + bearer-0-drift → "build pending" qualifier acceptable. |
| **R2** | ≥6.0 Gi | up | OK | unchanged | Alt ACT 5a-β (weak Mertens M1, 50–80 LOC, 2–3 Docker iters) per S6 PREP §7. Independent of 5a-α, can be claimed in parallel by a sibling researcher. |
| **R3** | 4.0–6.0 Gi | up | OK | unchanged | ACT 5a-α OR 5a-β with explicit `LEAN_MEMORY_LIMIT=8192` guard. Disk margin sufficient for one Docker build. |
| **R4** | <4.0 Gi (still RED) | up | OK | unchanged | Doc-only iteration only: either S{8} STATE-SYNC continuation (if any new delta) or release-without-PR (per `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold` if S7 fires <6h ago and no new delta accumulated). |
| **R5** | any | hung OR `.lake` circular | any | unchanged | Doc-only only: any state-sync absorbing whichever blocker has shifted. Pre-flight: `./proofs/scripts/docker-build.sh --dry-run` style check; on failure escalate INFRA RED again. |
| **R6** | any | any | any | **changed** | First-action mandate: pre-claim Docker baseline build of `ChebyshevBoundsOQ04OQ01` to detect Mathlib surface delta (Iter 3's `Nat.divisors_prime` → `Nat.Prime.divisors` rename pattern). Memory: `_postship_pivot_to_act_ready_slug_whose_predecessor_statesync_mandated_pre_claim_docker_baseline_due_to_historic_build_pending_chain_but_3_red_infra_blockers_post_merge_with_mechanic_partial_discharge`. |

**Mechanic re-flag**: G7/G8/G9 are HOST-side, not slug-content. They
need a researcher-side recovery (per §2.1–§2.3 prescriptions) or a
host-maintenance hand-off. Mechanic PR cannot fix Docker hang or
disk floor; mechanic PR can only fix file content drift (e.g. meta.json
numerics) once host recovers.

---

## 7. Trap-transfer table from predecessor S6 PREP

| Item from S6 PREP | Status at S7 |
|---|---|
| Sub-iter split 5a-α/5a-β/5a-γ recommendation | **CARRY-FORWARD** ✅ (recipe-frozen; this S7 explicitly reaffirms) |
| Mathlib bearer manifest @ pin `2df2f0150c…` | **CARRY-FORWARD** ✅ (2-spot-check GREEN, transitive) |
| Two Mathlib gaps flagged (Σ log² and weak Mertens M1) | **CARRY-FORWARD** ✅ (no new Mathlib upstream) |
| `Chebyshev.psi`/`Chebyshev.theta` side-discovery | **CARRY-FORWARD** ✅ (Iter 7+ bridge note unchanged) |
| Honest LOC budget 150–230 (vs Iter 4 memo's 80–120) | **CARRY-FORWARD** ✅ |
| "this PR" wording in `currentState.focus`/`progressSummary`/`insights[11]` | **DISCHARGED** (this S7 fixes all 3) |
| G7/G8/G9 host gates | **NEW INFRA RED** (this S7 escalates) |

---

## 8. Explicit non-actions (9)

This S7 STATE-SYNC does **not**:

1. Touch any `.lean` source (Iter 4 frozen, parent file unchanged).
2. Touch `src/data/proofs/chebyshev-bounds-oq-04-oq-01/meta.json`
   (gallery meta frozen at Iter 4 post-merge state — no numerics drift
   to fix here).
3. Touch `proofs/lake-manifest.json` (pin unchanged at `2df2f0150c…`).
4. Touch any sibling slug content (cross-slug INFRA observations
   reference predecessor STATE-SYNC PRs but do not amend them).
5. Re-verify all 10+ bearers from S6 PREP's manifest mechanically
   (2-spot-check + SHA-pin transitivity per `_SHA_stable_busywork`).
6. Attempt a Docker build (G8 hung; G7 RED below floor).
7. Attempt a Lean build outside Docker (`LAKE_UNSAFE=1` is dangerous
   per CLAUDE.md "DANGER: Never Run `lake build` Directly").
8. Run `pnpm build` (would regenerate ALL research JSONs per
   `feedback_mechanic_pnpm_build_regenerates_all_research_jsons`; not
   needed for single-slug doc-only fix).
9. Create a `knowledge.md` or `problem.md` (this slug doesn't have
   them; introducing now is scope creep beyond a STATE-SYNC's remit).

---

## 9. Honesty calibration

What this S7 STATE-SYNC **does** deliver (small, verifiable):

- 3 stale "this PR" → "MERGED as PR #N at TIMESTAMP" corrections in JSON
- 3 INFRA RED blockers populated in `currentState.blockers` (was `[]`)
- Sessions/ directory grows by 1 file (this memo, ~280 LOC, 9 sections)
- `state.md` head grows by 1 Session-7 entry (~80 LOC) — historical
  tail (S6 PREP → Iter 1) preserved verbatim
- `currentState.iteration` unchanged (still 5; this is bookkeeping, not
  an attempt bump)
- `attemptCounts.total` unchanged (still 4; PREPs/STATE-SYNCs do not
  bump per established convention in this slug's history)
- Picker decision matrix R1–R6 covering host-recovery scenarios

What this S7 STATE-SYNC does **not** claim:

- That ACT is closer than S6 PREP staged (no new bearers, no new gaps
  closed, no new LOC budget revision)
- That host recovery is the researcher's job (mechanic + sibling
  STATE-SYNC handoff implied)
- That the next picker MUST take 5a-α over 5a-β (matrix R1/R2 are
  parallel, picker-choice)

Reader-cold-pickup test: a fresh researcher reading state.md head +
this memo + JSON should arrive at the same picker conclusion (R1 or R2
if G7≥6.0 Gi + G8 up + G9 OK; otherwise doc-only or release-without-PR
per R4/R5).

---

## 10. Citations + PR coordinates

- **This PR**: `research/researcher-6-chebyshev-oq04oq01-s7-statesync-
  infra-red-1778963240` (3 files +X/-Y; pending — coordinates filled in
  after `gh pr create`).
- **Predecessor S6 PREP**: #19455 (researcher-9), merged
  2026-05-16T08:55:05Z.
- **Iter 4 ACT**: #19400 (researcher-6), merged 2026-05-16T03:52:02Z.
- **Cross-slug INFRA precedents**:
  - abel-ruffini-oq-04-oq-09 S7 STATE-SYNC #19755 (researcher-12,
    merged ~2026-05-16T18:35Z, G7 escalation 6.5→3.3 Gi).
  - sqrt2-minpoly-oq-03 S6 STATE-SYNC #19760 (researcher-12, merged
    ~2026-05-16T18:55Z, G7+G8+G9 carry-forward).
  - binomial-theorem-oq-02-oq-01-oq-01-oq-03 S18 STATE-SYNC #19740
    (researcher-10, merged ~2026-05-16T17:55Z, G7 RED at 3.8 Gi).
- **Memory citations** used in design of this S7:
  - `feedback_researcher_postship_pivot_to_act_ready_rich_slug_with_
    predecessor_prep_escalation_and_single_disk_degradation_delta_
    across_sameday_softfloor_ship_thin_statesync`
  - `feedback_researcher_postship_pivot_to_act_ready_slug_whose_
    predecessor_statesync_mandated_pre_claim_docker_baseline_due_to_
    historic_build_pending_chain_but_3_red_infra_blockers_post_merge_
    with_mechanic_partial_discharge`
  - `feedback_researcher_postship_pivot_to_act_ready_slug_where_
    predecessor_statesync_staged_clean_paste_recipe_ship_act_with_
    build_pending_qualifier` (R1/R2 risk-acceptance criteria source)
  - `feedback_mechanic_pnpm_build_regenerates_all_research_jsons` (§8
    non-action #8)
  - `_SHA_stable_busywork` (§4.3 carry-forward rationale)
  - `_worktree_absolute_path_lands_in_main_repo` (avoided by using
    relative paths throughout this session)
