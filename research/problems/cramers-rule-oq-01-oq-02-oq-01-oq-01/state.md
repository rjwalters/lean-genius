# Current State

**Phase**: S17 PREP (post-S16 STATE-SYNC with ACT-readiness gate degradation to 8/9 GREEN + 1/9 AMBER: host disk regressed from S16 PREP's 97 Gi avail to 7.8 Gi avail at 100% capacity; Docker remains RESPONSIVE; ACT plan unchanged — S16+1 ACT picker follows S15 PREP §6.2 7-step checklist)
**Since**: 2026-06-02T04:34:00Z (S17 PREP, researcher-1)
**Iteration**: 17
**Last session**: S17 PREP — post-S16 STATE-SYNC + degraded gate refresh (researcher-1, 2026-06-02, doc-only)
**Last Updated**: 2026-06-02T04:34:00Z

> _Phase note: state.md previously stayed at iter 15 because S16 PREP (researcher-1, 2026-05-25) did not propagate iteration counter to state.md — only updated the JSON. This S17 PREP brings state.md back in sync (15 → 17, skipping the unmemorialised 16)._

## Session 17 — S17 PREP, post-S16 STATE-SYNC + degraded gate refresh (researcher-1, 2026-06-02, doc-only)

Doc-only quiescence sync 8 days after S16 PREP (researcher-1,
2026-05-25T08:43:15Z, "9/9 GREEN" snapshot). Re-probes the ACT-readiness
gate items 7 (Docker) and 8 (disk) per S16 PREP §1:

- **Docker daemon**: GREEN — `timeout 10 docker info` returns the Server
  section cleanly in ~3 s. Client v29.4.1, Context `desktop-linux`.
  Matches S16 PREP's GREEN reading.
- **Host disk**: **DEGRADED to AMBER** — `df -h /Users/rwalters` shows
  **7.8 Gi avail at 100% capacity**. Same neighbourhood as S15 PREP's
  5.4 Gi AMBER reading; far below the 97 Gi declared GREEN at S16 PREP.

**Net gate refresh**: S16 PREP 9/9 GREEN → S17 PREP **8/9 GREEN + 1/9 AMBER**
(item 8: host disk).

The disk AMBER does NOT block the S16+1 ACT picker outright; the S15 PREP
disk-pressure mitigations remain applicable. The S16+1 ACT picker should:

- Re-probe `df -h /Users/rwalters` at branch creation; abort if avail < 5 Gi.
- Run `docker system prune --volumes -f` before build if avail < 10 Gi
  (frees ~10-30 Gi typically; safe but may interrupt parallel agents).
- Apply S15 PREP §5.2 "ship with build-pending qualifier" fallback if
  the build attempt fails on disk exhaustion.

The ACT plan and target file (`CramersRuleOQ01OQ02OQ01OQ01.lean`, 293 LOC,
9 thm, 0 ax, **1 sorry**) are unchanged from S16 PREP. The `qdetN_step_eq_qdetF`
discharge follows the corrected Form 1 statement from S15 PREP §4.1:
`det(A.sub) = (-1)^((j : ℕ) + (j.succAbove q : ℕ) + 1) * ∑ p, A(i.succAbove p) j * adjugate M q p`.

Full memo at `sessions/2026-06-02-s17-prep-statesync-degraded-gate.md` (~110 LOC).

### Files touched (3 — doc-only)

- `state.md` (this file): S17 PREP block prepended; iteration 15 → 17
  (catching up the unmemorialised S16 jump).
- `sessions/2026-06-02-s17-prep-statesync-degraded-gate.md`: NEW
  (~110 LOC, gate refresh + ACT picker guidance).
- `src/data/research/problems/<slug>.json`: `currentState.{phase, since,
  iteration, focus}` refresh; `lastUpdate` bump; 1 new `knowledge.insights`
  entry (S17 PREP gate-refresh result, disk regression).

**Zero Lean / meta.json / gallery / candidate-pool edits.**

## Session 15 — S15 PREP, `submatrix_chain` sign correction (latent correctness gap surfaced before S15+1 ACT) (researcher-6, 2026-05-16, doc-only)

Doc-only PREP iteration catching a **latent correctness gap** in the
`submatrix_chain` intermediate-have statement as stated in **S4f PREP §2.7 / §2.9**
and elaborated in **S12 PREP §1.1 / §2.2**. The recipe gives the sign factor as
`(-1)^((q : ℕ) + (p : ℕ))` distributed inside the sum-over-p; numerical check at
`n = 2, i = j = 0, q = 0` shows the recipe RHS computes
`A 1 0 * A 2 2 + A 2 0 * A 1 2` whereas the actual `det(A.submatrix
i.succAbove (j.succAbove q).succAbove)` is `A 1 0 * A 2 2 − A 1 2 * A 2 0` —
the signs on the second term differ. (Cross-check at `i=0, j=1, q=0` and
`i=0, j=0, q=1` also fail.)

**Root cause**: the S12 PREP §2.2 Block IV `h_sign` comment "Not always true!"
correctly flagged that `(-1)^(p + j_col) = (-1)^(q + p)` is not provable as
stated, but did not trace the issue back to the §1.1 statement of
`submatrix_chain`. After re-tracing through Steps (a)-(d) of S12 PREP §1.2,
the correct combined sign is `(-1)^(2p + j_col + q) = (-1)^(j_col + q)`,
which is **independent of p** and thus factors OUTSIDE the sum-over-p.

**Corrected σ(q)** (closed form, no j_col case-split exposed in statement):
```
σ(q) = (-1)^((j : ℕ) + (j.succAbove q : ℕ) + 1)
```
Equivalently:
- Case q.val < j.val: `(j.succAbove q).val = q.val`, so `σ(q) = (-1)^(j + q + 1)`.
- Case q.val ≥ j.val: `(j.succAbove q).val = q.val + 1`, so `σ(q) = (-1)^(j + q + 2) = (-1)^(j + q)`.
- In `j_col` terms: `σ(q) = (-1)^(j_col + q)` (same as the §2 derivation's output).

**Outer §2.9 verification**: the required relation for the outer
`field_simp + ring` to close is `(-1)^(i + j.succAbove q) * σ(q) = -(-1)^(i+j)`.
Substituting σ(q) gives `(-1)^(i + j.succAbove q + j + j.succAbove q + 1) =
(-1)^(i + j + 1) = -(-1)^(i+j)` ✓. (Detailed §3.2 derivation in session memo.)

Three numerical witnesses verify the corrected σ(q) at n=2:
- (i,j,q) = (0,0,0): σ = +1, sum = `A(1,0)A(2,2) - A(2,0)A(1,2)` = det ✓
- (i,j,q) = (0,1,0): σ = +1, sum = `A(1,1)A(2,2) - A(1,2)A(2,1)` = det ✓
- (i,j,q) = (0,0,1): σ = −1, sum = `A(1,0)A(2,1) - A(2,0)A(1,1)` = det ✓

**Revised Block I-IV plan** (S15 PREP §5; total ~40 LOC, slightly tighter than
S12 PREP §2.2's ~30-45 LOC range BECAUSE Block IV's `h_sign` sub-sorry is now
unnecessary):
- Block I: define `j_col : Fin n` via `if-then-else` on `q.val < j.val` (~8 LOC).
- Block II: apply `det_eq_sum_mul_adjugate_col` + `submatrix_apply` (~8 LOC).
- Block III: `adjugate_fin_succ_eq_det_submatrix` forward + `submatrix_submatrix`
  simp (~10 LOC).
- Block IV (simplified, no h_sign): `h_col_eq` Fin-comp identity + clean
  `(-1)^(2p + j_col + q) = (-1)^(j_col + q)` rewrite (~10 LOC) + wrap to
  closed-form σ(q) (~5 LOC).

### Files changed this S15 PREP cycle

1. NEW `sessions/2026-05-16-s15-prep-submatrix-chain-sign-correction.md`
   (~520 LOC, 8 sections incl. numerical refutation + algebraic derivation +
   outer skeleton verification + Form 1/Form 2 corrected statements + revised
   Block I-IV plan + risk inventory R1-R5 + alternative paths P1-P3 + LeanFiles
   drift handoff). **No paste-ready ACT body** — see §5 of memo for Lean
   skeleton snippets.
2. EDIT this state.md (head replace preserving Sessions 1-14 bodies + this
   Session 15 heading + narrative).
3. EDIT `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`
   (`currentState.{iteration 14→15, since, focus rewrite, blockers refresh,
   nextAction rewrite pointing at S15 PREP §5 corrected Block I-IV,
   lastUpdate, attemptCounts.total 12→13}` + `knowledge.{progressSummary
   prepend Session-15 paragraph, insights += 1 sign-correction insight,
   mathlibGaps unchanged, nextSteps refresh pointing at S15 PREP §6.2
   8-step picker checklist}`).

0 Lean edits. 0 meta.json edits. 0 problem.md / knowledge.md edits.
0 axiom change (0 / 0 in slug). 0 sorry change (1 sorry preserved at line 287
of `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`).

### Host infra this S15 PREP cycle

- **Docker daemon still hung** (same B1 condition; `docker info` returns
  Client section + Plugin list but no `Server:` body past 10s timeout).
  Cumulative hung-window: ~7.5+ h (covering S13 PREP-2 + S14 PREP + this S15
  cycle).
- **Disk degraded**: 5.4 Gi avail (was 6.54 Gi at S14 PREP start; −1.1 Gi
  in 52 min). Approaching ~5 Gi safety-floor.
- No sibling `iter-<TS>` branches on origin for this slug.
- 0 open PRs for this slug at cycle start.
- Mathlib lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0,
  unchanged since S11 STATE-SYNC; **7 successive PREPs at same SHA** now
  incl. this one read-only).

### ACT-readiness gate (refreshed from S14 PREP §5; new row for σ(q) correctness)

| Item | Status (this S15 PREP) | Source |
|------|------------------------|--------|
| 5 S12 PREP bearers | ✓ | S12 §3 |
| 4 S13 PREP-2 bearers (was ⚠) | ✓ | S13 PREP-2 §2 |
| Lake SHA stable | ✓ | 0 drift since S11 (7 PREPs at same SHA) |
| Slug file builds clean at HEAD | ✓ | S10 build-verify (3060 jobs) |
| Sign exponent convention (outer) locked | ✓ | S4 PR #19142 |
| **Sub-sorry tactic plan locked + correct** | **✓ (corrected this S15)** | **S15 PREP §5 (revised Blocks I-IV)** |
| **submatrix_chain statement correct (NEW row)** | **✓ (corrected this S15)** | **S15 PREP §4 (Form 1)** |
| Docker daemon responsive | **✗** | Still hung this cycle (7.5+ h cumulative) |
| Host disk ≥ 5 Gi avail | ⚠ | 5.4 Gi avail (−1.1 Gi since S14 PREP) |

Gate: GREEN for documentation prerequisites (7/9 ✓); RED for infra (Docker);
AMBER on disk (degrading but above floor). S15+1 ACT proper (paste corrected
Block I-IV + outer §2.9 skeleton + meta deltas) **remains correctly deferred**
to the next post-Docker-recovery picker.

### Post-S15 next-picker checklist (8 steps, supersedes S14 PREP's 7-step)

Step count rises 7 → 8 because the corrected Block IV needs an explicit
sign-collection rewrite `(-1)^(2p + j_col + q) = (-1)^(j_col + q)` step that
wasn't in the prior plan (the prior plan's h_sign sub-sorry was effectively
the same step, but mis-stated; the corrected step is provable cleanly).

1. **Confirm Docker daemon healthy** (`timeout 10 docker info` returns
   `Server:` body; `docker ps` works).
2. **Adopt Option B (private lemma)** per S12 PREP §5: declare
   `private lemma submatrix_chain` above `qdetN_step_eq_qdetF`.
   **Use the CORRECTED statement (Form 1 per S15 PREP §4.1)** — NOT the S12
   PREP §1.1 or S4f PREP §2.7 form.
3. **Paste the §2.9 outer skeleton** with `submatrix_chain` reference replaced
   by the private-lemma name.
4. **Implement Block I** per S15 PREP §5.1 (~8 LOC).
5. **Implement Block II** per S15 PREP §5.2 (~8 LOC).
6. **Implement Block III + IV combined** per S15 PREP §5.3 + §5.4 + §5.5
   (~25 LOC; sign collection now provable cleanly, no h_sign sub-sorry).
7. **Drop S4f PREP §4 sanity-check `example` blocks** at `(i,j) = (0,0)` and
   `(0,1)` (~24 LOC; re-verified algebraically at 3 witnesses in S15 PREP §3.4).
8. **Docker-verify** via `./proofs/scripts/docker-build.sh
   Proofs.CramersRuleOQ01OQ02OQ01OQ01`. Forecast 3060→3060 jobs warm cache.
   **Sorry count target**: 1 → 0 (Blocks I-IV fully discharge) or 1 → 1
   (h_col_eq partial, S15+2 follow-up).

Estimated S15+1 ACT wall time (when Docker is healthy): 60-90 min (4-6 Docker
iters at ~60-180s each in warm cache).

Session note: `sessions/2026-05-16-s15-prep-submatrix-chain-sign-correction.md`.

## Session 14 — S14 PREP, JSON-catchup absorbing S13 PREP-2 + Docker B1 reaffirm + stranded-branch reaffirm (researcher-4, 2026-05-16, doc-only)

Doc-only catchup iteration discharging the only follow-up that the S13 PREP-2 commit
message explicitly deferred: research JSON drift.

The just-merged S13 PREP-2 (PR #19579, merged 2026-05-16T13:52:16Z, ~4 min before this
cycle start) said in its commit message _"Files changed: 2 (state.md head update, new
session memo). ... No JSON edits."_ This left
`src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`'s
`currentState.iteration` at 12 / `since` at S12 PREP's 04:35Z / `focus` quoting S12
PREP / `nextAction` step 1 still calling for the bearer re-fetch that S13 PREP-2 §2
had already discharged.

The highest-cost drift was `nextAction` step 1 ("Re-fetch 4 ⚠-deferred bearers ... live
at moment of paste"). The next picker landing on this slug (via `claim-random` or
sibling-coordination read) would either re-run the `gh api` calls unnecessarily
(~10–15 min wasted on already-locked line numbers) or skim state.md to confirm
done (extra navigation overhead). S14 PREP catches JSON up so the next picker's JSON
view aligns with state.md head and the next-action checklist starts at the
Docker-dependent steps directly.

Full triage matrix, JSON delta scope, stranded-branch reaffirm, Docker B1 reaffirm,
readiness gate refresh, R1–R5 risk inventory, and the post-S14 picker checklist
(steps reduced from 8 to 7 because S13 PREP-2 §2 + this S14 §2 discharge two former
prep-side items) are in
`sessions/2026-05-16-s14-prep-json-catchup.md` (~280 LOC).

### Files changed this S14 PREP cycle

1. NEW `sessions/2026-05-16-s14-prep-json-catchup.md` (this iteration's session memo).
2. EDIT this state.md (head replace preserving Sessions 1–13 bodies + add this
   Session 14 heading + brief narrative).
3. EDIT `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`
   (`currentState.{iteration,since,focus,nextAction,lastUpdate,attemptCounts.total}`
   refresh + `knowledge.insights` += 2 + `knowledge.builtItems` += 2 +
   `knowledge.progressSummary` light extension).

0 Lean edits. 0 meta.json edits. 0 problem.md / knowledge.md edits. 0 axiom change
(0 / 0 in slug). 0 sorry change (1 sorry preserved at line 287 of
`proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`).

### Host infra this S14 PREP cycle

- Docker daemon **still hung** (same B1 condition as S13 PREP-2; Server section
  unresponsive past 8s; Client + Plugin list respond fine; 0 visible containers).
  Cumulative hung-window across S13 PREP-2 + this cycle: ~6.5+ h.
- Disk: 6.54 Gi avail (down 0.36 Gi since S13 PREP-2 cycle start at 6.9 Gi; still
  above the ~5 Gi safety floor but approaching the ≤ 8 Gi saturated-queue trigger zone).
- No sibling `iter-<TS>` branches on origin for this slug (`git ls-remote origin
  refs/heads/research/cramers-rule-oq-01-oq-02-oq-01-oq-01-*` → empty).
- 0 open PRs for this slug at cycle start (verified via `gh -R rjwalters/lean-genius
  pr list --state open --search ...`).

### ACT-readiness gate (unchanged from S13 PREP-2 §3 except infra row trend)

| Item | Status (this S14 PREP) | Source |
|------|------------------------|--------|
| 5 S12 PREP bearers | ✓ | S12 §3 |
| 4 ⚠-deferred bearers (now ✓-locked) | ✓ | S13 PREP-2 §2 |
| Lake SHA stable | ✓ | 0 drift since S11 (6 successive PREPs at same SHA incl this one read-only) |
| Slug file builds clean at HEAD | ✓ | S10 build-verify (3060 jobs) |
| Sign exponent convention locked | ✓ | S4 PR #19142 + S12 §3 + S13 PREP-2 §2.1 |
| Sub-sorry tactic plan locked | ✓ | S12 §2.2 + S12 §5 (Option B) |
| Docker daemon responsive | **✗** | Still hung this cycle (6.5+ h cumulative) |
| Host disk ≥ 5 Gi avail | ⚠ | 6.54 Gi avail (−0.36 Gi since S13 PREP-2) |

Gate: GREEN for documentation prerequisites; RED for infra (Docker); AMBER on disk.
S14 ACT proper (~95–115 LOC Lean paste discharging `qdetN_step_eq_qdetF`) remains
correctly deferred to the next post-Docker-recovery picker.

### Post-S14 next-picker checklist (Docker-dependent only, supersedes S12 PREP §8)

1. Adopt Option B from S12 PREP §5: hoist `submatrix_chain` to private lemma above
   `qdetN_step_eq_qdetF`.
2. Paste S4f PREP §2.9 ~58-LOC outer skeleton with `submatrix_chain` reference
   replaced by the new private-lemma name.
3. Implement Block I (`j_col` via `Fin.cases` on `q.val < j.val`) → Block II
   (`det_eq_sum_mul_adjugate_col` + submatrix simplification) → Block III
   (`adjugate_fin_succ_eq_det_submatrix` ± + `submatrix_submatrix` simp) → Block IV
   (`h_col_eq` funext + sign collection `by_cases hqj`). See S12 PREP §2.2 for
   paste-ready code.
4. Drop S4f §4 sanity-check `example` blocks at (0,0) and (0,1) (~24 LOC; verified
   algebraically in S12 PREP §4.2).
5. `./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01`.
   Forecast: 3060 → 3060 jobs warm cache.
6. Slug-file diff target: −1 sorry (1 → 0) if Block I–IV fully discharge, or 1 → 1
   if Block I or IV partial (S15 follow-up). +~95–115 LOC total.
7. See S12 PREP §6 + this S14 §5 readiness gates (6 GREEN + 1 AMBER + 0 RED once
   Docker recovers).

(Step count drops 8 → 7 because S13 PREP-2 §2 discharged the bearer-fetch detour
and this S14 PREP discharged the JSON-catchup detour.)

## Session 13 — S13 PREP-2, 4 ⚠-deferred-bearer live-pin pre-fetch + ACT-readiness confirmation (researcher-4, 2026-05-16, doc-only)

Doc-only PREP-2 iteration discharging the **only PREP-side item** on S12 PREP §8's next-picker checklist: live-fetch the 4 ⚠-deferred bearers (`Matrix.det_succ_row`, `Matrix.inv_def`, `Ring.inverse_eq_inv`, `Fin.sum_univ_succAbove`) from lake SHA via `gh api` and lock their line numbers.

Cycle triggered by `claim-random` returning this slug at 2026-05-16T09:55Z (researcher-4, RICH score 22, 0 open PRs, no sibling `iter-<TS>` branches on origin). Host infra: **Docker daemon hung** (Server section unresponsive after 30s while Client section + plugin list respond fine; 0 running containers; 0 images visible; disk 100% / 6.9 Gi avail). Substantive S13 ACT (~95-115 LOC paste) is genuinely risky to ship blind without Docker build-verify; this PREP-2 takes the only Docker-free prep item off the picker checklist and stages the slug for the next claim-random landing once Docker recovers.

### What S13 PREP-2 adds

**4 ⚠-deferred bearers now ✓ live-pinned** at unchanged lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (0 drift from S12 PREP's pin SHA; 5th successive PREP at same SHA):

| # | Bearer | Path | Line | Signature highlight |
|---|--------|------|-----:|---------------------|
| 6 | `Matrix.det_succ_row` | `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean` | 769 | `det A = ∑ j, (-1)^(i+j) * A i j * det (A.submatrix i.succAbove j.succAbove)` |
| 7 | `Matrix.inv_def` | `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` | 167 | `A⁻¹ = Ring.inverse A.det • A.adjugate := rfl` |
| 8 | `Ring.inverse_eq_inv` | `Mathlib/Algebra/GroupWithZero/Units/Basic.lean` | 374 | `Ring.inverse a = a⁻¹` |
| 9 | `Fin.sum_univ_succAbove` | `Mathlib/Algebra/BigOperators/Fin.lean` | 68 (parent `prod_univ_succAbove` `@[to_additive]`) | `∑ i, f i = f x + ∑ i : Fin n, f (x.succAbove i)` (auto-additive) |

**Aggregate bearer surface**: now **9-out-of-9 ✓ live-pinned, 0 ⚠ deferred** (was 5 ✓ + 4 ⚠ at S12 PREP close).

**Sign exponent confirmation**: `det_succ_row` signature confirms `(-1)^(i+j)` exponent (matches qdetN_step_eq_qdetF's callsite parity per S4 statement-fix PR #19142).

**Namespace caveat for picker**: `Fin.sum_univ_succAbove` is generated by `@[to_additive]` (not directly declared). Use the fully-qualified name `Fin.sum_univ_succAbove` at the use site unless `open Fin` is in scope.

### Refreshed S13 ACT readiness gate

| Item | Status (this S13 PREP-2) | Source |
|------|--------------------------|--------|
| 5 S12 PREP bearers (`adjugate_fin_succ_eq_det_submatrix`, `det_eq_sum_mul_adjugate_row`, `det_eq_sum_mul_adjugate_col`, `submatrix_submatrix`, `submatrix_id_id`) | ✓ | S12 §3 |
| 4 ⚠-deferred bearers (`det_succ_row`, `inv_def`, `Ring.inverse_eq_inv`, `Fin.sum_univ_succAbove`) | ✓ (was ⚠) | **NEW this S13 PREP-2 §2** |
| Lake SHA stable | ✓ | 0 drift since S11 STATE-SYNC (5 successive PREPs at same SHA) |
| Slug file builds clean at HEAD | ✓ | S10 build-verify (3060 jobs); no upstream change since |
| Sign exponent convention locked | ✓ | S4 statement-fix PR #19142 + S12 §3 + S13 PREP-2 §2.1 confirmation |
| Sub-sorry tactic plan locked | ✓ | S12 §2.2 (Blocks I-IV, ~30-45 LOC) + S12 §5 (Option B private-lemma sequencing) |
| Docker daemon responsive | **✗** | Hung this S13 PREP-2 cycle; **BUILD-VERIFY DEFERRED to S13 ACT** when host recovers |
| Host disk ≥ 5 Gi avail | ⚠ | 6.9 Gi avail / 100% capacity (barely above floor) |

**Gate**: **GREEN for documentation prerequisites; RED for infra**. The single ✗ (Docker daemon) is infra-only; expected to recover within ~1-6 h per memory pattern `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`.

### Tightened S13 ACT next-picker checklist (replaces S12 §8 step 1)

After this S13 PREP-2 lands, the picker checklist tightens to (only Docker-dependent steps remain):

1. **Confirm Docker daemon healthy** (`timeout 10 docker info` returns Server section + `docker ps` works).
2. **Adopt Option B (private lemma)** per S12 §5: declare `private lemma submatrix_chain` above `qdetN_step_eq_qdetF`.
3. **Paste the §2.9 skeleton** with `submatrix_chain` reference replaced by name.
4. **Implement Block I–IV** from S12 §2.2 inside the private lemma. Budget ~30–45 LOC. Bearer names + lines all locked per S13 PREP-2 §2.
5. **Drop the §4 sanity-check `example` blocks** (n=1 at (0,0) and (0,1)) from S4f PREP §4 (~24 LOC).
6. **Docker-build** via `./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01`. Forecast: 3060 → 3060 jobs (warm cache, ~60-180s per iter).
7. **Sorry count outcome**: 1 → 0 if Blocks I-IV fully discharge; 1 → 1 if Block I or IV partially closes (S14 follow-up scope).

Estimated S13 ACT wall time (when Docker is healthy): 60-90 min (4-6 Docker iters at ~60-180s each in warm cache).

### Counts (post-S13-PREP-2, unchanged from S12 PREP close because doc-only)

| Metric | Value |
|--------|------:|
| File LOC | 293 (unchanged) |
| Sorries | 1 (line 287, `qdetN_step_eq_qdetF`) |
| Axioms | 0 |
| Build | verified clean at S10 (3060 jobs); no upstream change |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: this state.md (+~70 LOC, prepending S13 PREP-2 section before S12 — preserves S12's prior body); 1 new sessions/ note (~280 LOC). 0 Lean file edits. 0 sibling-slug edits. 0 meta.json edits. 0 research-JSON edits.

**Next action**: S13 ACT — when Docker daemon recovers, follow the tightened 7-step picker checklist above.

Session note: `sessions/2026-05-16-s13-prep2-deferred-bearer-prefetch.md`.

## Current Focus

S4 ACT is **fully unblocked** and the `submatrix_chain` sub-sorry — the hardest
piece of the §2.9 skeleton per S4f PREP §2.7 — now has a paste-ready 4-block
tactic plan from S12 PREP §2.2 (~30–45 LOC, decomposed into Block I `j_col`
definition, Block II `det_eq_sum_mul_adjugate_col` application, Block III
`adjugate_fin_succ_eq_det_submatrix` + `submatrix_submatrix` chain, Block IV
sign collection via case-split on `q.val < j.val`). The S12 PREP also revises
the LOC estimate upward from S4f PREP's "~15 LOC" to "~30–45 LOC" for the
sub-sorry alone, with full-theorem total now ~95–115 LOC.

`Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` on `origin/main` (SHA
`0a6466a8f0dd7422cbb214031871ef9bfde1d068` at S12 PREP claim): **293 lines**,
1 actual `sorry` (line 287, `qdetN_step_eq_qdetF`), 0 axiom. (Note: the
JSON `leanFiles[].sorryCount` legacy value of 5 is stale per the actual
file — PR #19435 mechanic fix updates gallery `meta.json` `sorries 0 → 1`,
matching the on-disk count.)

Bearer drift recheck (S12 PREP §3 live at lake SHA `2df2f0150c...`):
4 critical bearers re-verified — `Matrix.adjugate_fin_succ_eq_det_submatrix`
at `Adjugate.lean:362`, `Matrix.det_eq_sum_mul_adjugate_row` at
`Adjugate.lean:401`, `Matrix.det_eq_sum_mul_adjugate_col` at `Adjugate.lean:415`,
`Matrix.submatrix_submatrix` at `LinearAlgebra/Matrix/Defs.lean:406` (`@[simp]`).
Plus new pin: `Matrix.submatrix_id_id` at `Defs.lean:402` (`@[simp]`).
**0 substantive drift** since S11 STATE-SYNC. The signature of
`adjugate_fin_succ_eq_det_submatrix` is locked at `(-1)^(j + i) * det(A.submatrix j.succAbove i.succAbove)`
(sign exponent `j + i`, parameter-swap handles `(i+j)` callsite need).

**Next picker action — S13 ACT.** Per S12 PREP §8 step list:
1. Re-fetch 4 ⚠-deferred bearers (`det_succ_row`, `inv_def`, `Ring.inverse_eq_inv`,
   `Fin.sum_univ_succAbove`) live at moment of paste.
2. **Adopt Option B (private lemma)** per S12 PREP §5: hoist `submatrix_chain`
   out of inline `have` into a `private lemma` above `qdetN_step_eq_qdetF`.
3. Paste the §2.9 skeleton with `submatrix_chain` reference replaced by name.
4. Implement Block I–IV from S12 PREP §2.2 inside the private lemma. Budget
   ~30–45 LOC.
5. Drop the n=1 sanity-check `example` blocks at `(i,j) = (0,0)` and `(0,1)`
   from S4f PREP §4 (~24 LOC, verified algebraically in S12 PREP §4.2).
6. Docker-verify `./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01`.
   Forecast: 3060 → 3060 jobs (warm cache, ~60–180s per iter per
   MEMORY pattern `_postship_buildverify_discharge_when_peerauthored_statesync_stages_it`).
7. Slug-file diff target: **−1 sorry (1 → 0) if Block I–IV fully discharge, OR
   1 → 1 if Block I or IV partially close (S14 follow-up)**, +~95–115 LOC.

**Build-verify (Session 10, retained for context).** Session 10's S4
statement-correction was build-verified by applying mechanic PR #19072's
parent-file patches as a transient local overlay and Docker-building the
slug under the corrected statement: ⚠ [3060/3060] Built clean (2.7s),
only `sorry` warning at the strategic theorem itself. Both PR #19072 and
PR #19142 have since merged; the post-merge SOTC on `origin/main` matches
the overlay-verified state.

## Session 12 — S12 PREP, `submatrix_chain` concrete tactic plan (researcher-11, 2026-05-16, doc-only)

**Trigger.** S11 STATE-SYNC's §4 readiness gate marked `submatrix_chain`
implicitly as a row-4 gate at "S4f PREP §2.7 bearer sketch only". The S13
ACT picker reading S11 STATE-SYNC would arrive at the `submatrix_chain`
sub-sorry with a 4-bearer mention (`submatrix_submatrix`,
`det_eq_sum_mul_adjugate_col`, `adjugate_fin_succ_eq_det_submatrix`,
`pow_add`/`Nat.add_comm`) but no concrete Lean tactic plan. Per MEMORY
pattern `feedback_researcher_act_paste_ready_skeleton_typically_needs_1_to_3_acttime_fallbacks`,
the highest-risk hot-spot in any §2.9 skeleton paste is the one step with
only a bearer sketch. This session pre-flights it.

**Deliverable.** Doc-only:

* New session note `sessions/2026-05-16-s12-prep-submatrix-chain-tactic-plan.md`
  (~520 LOC) with: §0 context, §1 mathematical derivation in 4 steps with
  sign-tracking witnesses, §2 paste-ready Lean tactic plan (Block I–IV,
  ~30–45 LOC with 2 Option-A/Option-B alternates), §3 live bearer pin
  re-verification at lake SHA via `gh api` raw-fetch (5 bearers; 4 critical
  + 1 helper), §4 n=1 worked numerical example at `(0,0)` and `(0,1)` pivots,
  §5 sequencing recommendation `private lemma` over inline `have`, §6
  updated 7-row S13 ACT readiness gate (6 GREEN + 1 AMBER unchanged on
  deployer org-cap), §7 anti-targets + conflict-free guarantees, §8 8-step
  S13 ACT picker checklist, §9 diff manifest.
* `state.md` head replacement (this section): preserves all prior session
  content unchanged below `## Session 11 — …`.
* `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`
  refresh: `currentState.iteration` 11 → 12, `currentState.since`
  2026-05-16T03:10 → 2026-05-16T04:35, `currentState.focus` rewritten,
  `currentState.nextAction` rewritten to S13 ACT 8-step checklist,
  `attemptCounts.total` 9 → 10, `lastUpdate` bump, 2 `insights` prepended
  (sub-sorry-LOC-revision + private-lemma-recommendation).

**Net.** 0 Lean edits. 0 sorry change (1 actual on disk → 1). 0 axiom change
(0 → 0). 0 line change in `proofs/`. 3 files: 1 NEW session note + 1
head-rewrite (state.md) + 1 JSON refresh.

**Bearer drift recheck (§3 of session note).** 4 critical bearers
re-verified live at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
0 substantive drift; line numbers locked at Adjugate.lean:362, 401, 415
and LinearAlgebra/Matrix/Defs.lean:406. 4 supporting bearers (`det_succ_row`,
`inv_def`, `Ring.inverse_eq_inv`, `Fin.sum_univ_succAbove`) deferred to S13
ACT pick-time re-verification per S4f PREP §3's pin-grep-at-paste discipline.

**LOC revision.** S4f PREP §2.7 estimated ~15 LOC for `submatrix_chain`.
S12 PREP §2.3 honest assessment: ~30–45 LOC including the case-split on
`q.val < j.val` (Block I + Block IV's `h_col_eq` Fin-arithmetic identity).
This pushes the full S4 ACT body estimate from S4f PREP §2.9's ~58 LOC to
S12 PREP's ~95–115 LOC.

**Race-safety.** Pre-claim probe (2026-05-16T04:30Z): `gh search prs --repo
rjwalters/lean-genius "cramers-rule-oq-01-oq-02-oq-01-oq-01" --state open`
returned 1 PR (#19435, mechanic `meta.json` `sorries 0 → 1`, disjoint paths).
This PR's diff is strictly orthogonal — sessions/, state.md, slug JSON only.
Pre-push will re-verify.

**Next picker action — S13 ACT.** Per §8 of S12 PREP session note: 8-step
checklist with Option B (private lemma `submatrix_chain` above
`qdetN_step_eq_qdetF`). Bearers are pin-stable, statement signature is locked
(signed RHS per Session 10 PR #19142), parent files compile, tactic plan is
on disk. Forecast 4–6 Docker iters in warm cache band; sorry target 1→0
if Block I–IV fully discharge (S14 follow-up only if Block I or IV partial).

## Session 11 — S11 STATE-SYNC, post-drain catch-up (researcher-11, 2026-05-16)

**Trigger.** Four sibling/parent-file PRs merged in a drain wave between
2026-05-15 18:04 UTC and 2026-05-15 23:39 UTC; this slug's `state.md` head
and JSON `currentState` did not yet reflect any of the four. Specifically:
the head still listed PR #19072 and PR #19142 as preconditions for S4 ACT
even though both had merged; the JSON `blockers` listed the parent-file
v4.26.0 regression as still active even though PR #19072's repair was on
disk; the JSON `nextAction` was conditional on two now-satisfied merges.

**Deliverable.** Doc-only:

* New session note `sessions/2026-05-16-s11-statesync-postdrainwave.md`
  (~430 LOC) with: drain-wave snapshot table (§1), bearer drift recheck
  against lake-pinned Mathlib SHA (§2), slug-file SOTC verification (§3),
  6-row S4 ACT readiness gate (§4), conflict-free guarantee (§5),
  state.md head replacement seed (§6), JSON refresh delta (§7), 3-option
  next-picker advice (§8).
* `state.md` head replacement (this section): preserves all prior session
  content unchanged below `## Session 10 — …`.
* `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json`
  refresh: `currentState.iteration` 10 → 11, `currentState.since` 2026-05-14
  → 2026-05-16, `currentState.focus` rewritten, `currentState.blockers`
  drops the parent-file blocker (3 entries remain), `currentState.nextAction`
  unconditional, `attemptCounts.total` 8 → 9, `lastUpdate` bump, two
  `knowledge.nextSteps` "Wait for …" items dropped.

**Net.** 0 Lean edits. 0 sorry change (5 → 5). 0 axiom change (0 → 0). 0 line
change in `proofs/`. 3 files: 1 NEW session note + 1 head-rewrite (state.md) +
1 JSON refresh.

**Bearer drift recheck (§2 of session note).** All 10 bearers from S4f PREP
§3 re-verified live at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
0 substantive drift; 1 cosmetic 1-line shift on `Matrix.det_eq_sum_mul_adjugate_row`
(start line 400 vs 401). The `inv_mul_cancel₀` v4.26.0-canonical fallback
name is confirmed live at `Algebra/GroupWithZero/Basic.lean:263`. The
`neg_add_eq_sub` fallback is left to the S4 ACT picker to grep at the
moment of paste (per S4f PREP §3 disclaimer).

**Race-safety.** Pre-claim probe (2026-05-16 ~03:00 UTC): `gh pr list
--search "cramers-rule-oq-01-oq-02-oq-01-oq-01" --state open` returned 0.
This PR's diff is strictly orthogonal to all open PRs (zero overlap with
slug Lean, slug `state.md`, slug JSON, slug `sessions/`, slug `problem.md`,
slug `knowledge.md`, gallery `meta.json`, parent Lean files). Pre-push will
re-verify.

**Next picker action — recommended Option A (per session note §8).** S4 ACT
ship per the S4f PREP §2.9 skeleton. Bearers are pin-stable, statement is
mathematically correct (signed RHS), parent files compile, paste-ready
skeleton is on disk. The deployer is currently capped on org monthly usage
(104 open PRs and growing as of session start) — Option C (release and
rotate) was the right call **for this session (researcher-11)** because 5
own ships in this session is the right inventory ceiling. The cap reset
opens Option A for the next picker.



## Session 10 — S4 statement-correction + mechanic-PR overlay build-verify (researcher-12, 2026-05-14)

**Trigger.** Three prior PREP sessions (S4b PR #18409, S4c PR #18525,
S4e PR #18751) locked the recommendation that `qdetN_step_eq_qdetF`'s
RHS must carry a `(-1)^(i+j)` factor, but the Lean file itself was
never updated; the unsigned statement merged via S3 SCAFFOLD PR #18214
was still on disk. This session lands the correction.

**Deliverable.** Edits to `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`:

* Theorem signature: RHS changed `= qdetF A i j` →
  `= (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j`.
* Header docstring (~line 45): "recovers `qdetF`" → "recovers
  `(-1)^(i+j) * qdetF`" with explanatory inline note.
* Main-results entry (~line 58): now annotates "signed-RHS form
  `(-1)^(i+j) * qdetF`".
* Theorem docstring (~lines 244–264): expanded with the S4c PREP §2
  four-pivot verification reasoning and S4e PREP §2 proof-path pointer
  (`Matrix.det_eq_sum_mul_adjugate_row`).

The `by sorry` is unchanged. No new sorries, no new axioms. Effective
LOC change: ~10 (signature + docstrings).

**Build verification.** Mechanic PR #19072's diff was applied as a
local overlay (transient — reverted before commit), and Docker-build of
`Proofs.CramersRuleOQ01OQ02OQ01OQ01` succeeded: 3060/3060 jobs, 2.7s,
only `sorry` warning at the corrected theorem. This demonstrates the
slug-file diff in this PR will compile cleanly **once PR #19072 merges**.

Pre-claim baseline (without mechanic overlay) confirmed the
parent-file blocker still reproduces on `origin/main` (commit
`2afb1b79c0a`): `Proofs/CramersRuleOQ01OQ02OQ01.lean:241:35,249:49,273:52`
all error per the PR #19036 inventory.

**Why this matters.** A strategic sorry whose statement is false is a
trap: a downstream proof could "close" the sorry with a fake proof, or
rely on the false statement in a chain. By landing the statement
correction before S4 ACT, this session removes the latent error and
makes the strategic sorry actually provable per the ~55-LOC plan of
S4e PREP §3.

**Net.** +34 / -16 lines on the slug Lean file (statement + docstring).
+0 sorries (1 → 1). +0 axioms (0 → 0). Phase ACT — strategic sorry
re-stated correctly; full S4 ACT proof remains the next deliverable.

**Race-safety.** PR #19036 (researcher-9 S4 precheck, open) touches
state.md / JSON / a different sessions file — potential merge-conflict on
state.md + JSON only. PR #19072 (mechanic, open) touches the two parent
Lean files — disjoint from this PR. PR #18171 / #18374 / #18439 (meta
drift, open) touch `src/data/proofs/.../meta.json` — disjoint from this
PR's `src/data/research/.../json` change.

**Next action (S4 ACT proper).** Once PR #19072 + this PR merge,
implement the ~55-LOC proof per S4e PREP §2/§3 using
`Matrix.det_eq_sum_mul_adjugate_row`. Bearer line-numbers locked at
lake-pinned Mathlib SHA `2df2f015...`. Estimated 4–6 Docker iterations
to converge on the sign-tracking arithmetic (per S4e PREP §3 "honest
assessment of the LOC savings").

## Previous: Session 3 — S3 SCAFFOLD (researcher-10, 2026-05-12)

S3 SCAFFOLD: Route B (non-commutative) **one-step Schur formula**
`qdetN_step` added to `CramersRuleOQ01OQ02OQ01OQ01.lean`. The formula
takes the homological-relations inverse `Minv : Matrix (Fin n) (Fin n) D`
as an explicit parameter, sidestepping the mutual recursion that S4 will
deliver. The Schur correction
  `A i j − ∑_{p,q} A i (succAbove j q) · Minv q p · A (succAbove i p) j`
is stated uniformly in n and the field-consistency reduction
`qdetN_step_eq_qdetF` is stated with strategic sorry (proof strategy
fully documented inline). **Note (added 2026-05-14 by S4 statement-fix):
the unsigned-RHS form committed by this PR was later determined to be
mathematically FALSE for off-diagonal pivots; the corrected signed-RHS
form is in place as of Session 10.**

## Session 3 — S3 SCAFFOLD (researcher-10, 2026-05-12)

**Deliverable.** Add Part VI ("Non-commutative Schur Step") to
`proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`:

* `qdetN_step` (def, no sorry): the one-step Schur formula over a
  division ring `D`, taking the candidate inverse `Minv` of the
  complementary minor as a parameter. Non-recursive — the mutual
  `qdetN` ↔ `qdetN_inv` definition is deferred to S4.
* `qdetN_step_zero_minv` (theorem, proved): degenerate case
  `Minv = 0` gives `A i j`, anchoring the formula.
* `qdetN_step_eq_qdetF` (theorem, strategic sorry): field-consistency
  reduction — over a field, choosing `Minv := M⁻¹` (Mathlib's
  `Matrix.nonsingInv`) recovers `qdetF A i j = det A / det(minor)`.

The header docstring is updated to document both Routes (S2 + S3) and
to reference the four S3-deliverable lemmas in the "Main results" list.

**Why this scaffold (vs. full mutual recursion).** Mathlib's
structural-recursion machinery does not see the size-decrease of
`A.submatrix _ _` (the recursive call argument differs from the original
matrix), so the canonical S3-design ("define `qdetN` via well-founded
recursion on `Σ n, Matrix (Fin n) (Fin n) D`") is a non-trivial
infrastructure investment. Separating `qdetN_step` is the standard
"ingredient delivery" pattern:

1. The Schur **formula** is captured once (no mutual recursion needed).
2. The S4 mutual-recursion proof reduces to constructing a single
   matrix `qdetN_inv (minorIJ A i j)` that satisfies the inverse
   equation, rather than re-proving the entire recurrence at each level.
3. The field-consistency theorem `qdetN_step_eq_qdetF` becomes a
   one-time bridge between Routes A and B, independent of the eventual
   `qdetN_inv` construction.

**Net.** +111 / -24 lines (header docstring rewrite + new Part VI section
at end of file). +1 sorry on `qdetN_step_eq_qdetF` (field-consistency
bridge, S4 target). +1 proved theorem (`qdetN_step_zero_minv`). +1 def
(`qdetN_step`). 0 axiom changes. Phase ACT — Route B scaffolded,
field-consistency theorem stated; mutual recursion not yet built.

**Build status.** Build pending — worktree `proofs/.lake` is the
recursive self-symlink trap (per
`feedback_researcher_lake_symlink_broken.md`); CI will verify.
Sanity checks: the file is self-contained against parent files
`CramersRuleOQ01OQ02`, `CramersRuleOQ01OQ02OQ01` plus the existing
Mathlib imports (`Adjugate`, `NonsingularInverse`, `Tactic`).

**Race-safety.** Pre-claim probe (2026-05-12 ~16:55 UTC): 0 open
research PRs for slug; only 2 enrichment PRs (#18183, #18194 — orthogonal
to Lean file changes). Most recent research merge is the S2 PR #18098
(merged 12:30 UTC, ~4h before this S3 work). Pre-push probe will
re-verify.

**Next action (S4).** Discharge the `qdetN_step_eq_qdetF` sorry via:
1. Expand `Matrix.inv_def` to rewrite `(minorIJ A i j)⁻¹` as
   `(1 / (minorIJ A i j).det) • (minorIJ A i j).adjugate`.
2. Distribute the scalar `1 / det(minor)` across the double sum in
   `qdetN_step`.
3. Apply `Matrix.det_succ_row` (Laplace expansion along row `i`) to
   isolate the `k = j` summand and recognise the remaining cofactor
   sum.
4. Sign normalisation via `Matrix.adjugate_apply` to match the
   `Fin.succAbove`-indexed adjugate entries with the cofactor signs.
Estimated S4 proof size: ~60–90 Lean lines.

After S4 closes `qdetN_step_eq_qdetF`, S5 builds `qdetN` via well-founded
recursion (or via `Invertible (minorIJ _ _)` as a typeclass parameter,
which avoids mutual recursion entirely at the cost of a side-condition
hypothesis at the recurrence). S6 lifts to n×n Cramer over a division
ring.

## Session 2 — S2 ACT (researcher-9, 2026-05-12)

S2 ACT: Route A (commutative quasideterminant `qdetF`) implemented over a
field. `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` created. The file
contains the uniform-in-n quotient definition, the multiplicative defining
identity, non-vanishing, and three specializations bridging back to
the parent 2×2 and 3×3 files.

**Route A complete (S2)**: `qdetF (n+1)×(n+1)` over a field via
`A.det / (minor_{ij} A).det`. Three bridges proved:
- n=3 specialization: `qdetF_eq_qdet3` (by `rfl`).
- n=2 (0,0): `qdetF_eq_qdet00` (under `A 1 1 ≠ 0`).
- n=2 (1,1): `qdetF_eq_qdet11` (under `A 0 0 ≠ 0`).

## Blockers

- **Mathlib has no `Matrix.quasideterminant`.** Route A is the first
  uniform-in-n Lean formalization.
- **Mutual recursion + invertibility witnesses (S4)**: the canonical
  Route B encoding needs `WellFoundedRecursion` on
  `Σ n, Matrix (Fin n) (Fin n) D` carrying the `qdetN_inv` witnesses
  through the descent. S3 SCAFFOLD sidesteps this by parametrising
  `qdetN_step` with `Minv` directly; S4 chooses between (a) building
  the recursion or (b) `Invertible (minorIJ _ _)` typeclass parameter.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1
- Approaches tried: 1

## Session-by-session

- **S1 (2026-05-12, researcher-12)**: OBSERVE. Formalized statement,
  surveyed Mathlib API, mapped 6-session plan (S2-S6). PR opened for
  problem.md + knowledge.md + state.md + JSON only.
- **S2 (2026-05-12, researcher-9)**: ACT. Route A implemented.
  `CramersRuleOQ01OQ02OQ01OQ01.lean` created (~175 lines) with:
  - 1 abbrev (`minorIJ`)
  - 1 def (`qdetF`)
  - 6 theorems (`qdetF_field_quotient`, `qdetF_ne_zero`,
    `qdetF_eq_qdet3`, `qdetF_eq_qdet00`, `qdetF_eq_qdet11`,
    `qdetF_summary`)
  - 2 supporting lemmas (`minorIJ_22_00_det`, `minorIJ_22_11_det`)
  - 0 sorries
  - Build status: docker build kicked off, build-pending precedent
    per PR #17990 / PR #17718.

## Done When

See `knowledge.md` "Done When" section.

- [x] **S2 (Route A)**: `qdetF` defined uniformly in n;
      `qdetF_field_quotient` proved; n=2/n=3 bridges proved.
- [ ] **S3 (Route B)**: `qdetN` defined inductively over a division ring.
- [ ] **S4**: `qdetN_recurrence` proved.
- [ ] **S5**: consistency `qdetN_eq_qdetF` over fields proved.
- [ ] **S6**: `cramer_rule_nxn_qdet` proved over division rings.
