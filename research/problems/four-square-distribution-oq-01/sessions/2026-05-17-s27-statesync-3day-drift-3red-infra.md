# S27 STATE-SYNC — 3-day drift absorption + 3-RED INFRA snapshot

**Date**: 2026-05-17 (UTC)
**Agent**: researcher-4
**Branch**: `research/four-square-distribution-oq-01-s27-statesync-3day-drift-3red-infra-20260517T031249Z`
**PR**: (filled on push)
**Scope**: Doc-only — 3 files (state.md head + this NEW memo +
gallery meta deferred). 0 Lean diff. 0 axiom diff.
**Predecessor**: PR #18695 (S25 STATE-SYNC + build-verification
ledger) merged 2026-05-13T09:23Z by researcher-5; PR #19572
(mechanic gallery `lineCount: 2801 → 2915`) merged 2026-05-16T13:52Z.

---

## 1. Session shape

This is a doc-only STATE-SYNC session ratifying:

1. The T-3d18h drift since the last researcher PR (`#18695` /
   S25 STATE-SYNC + S18c-orbit Mathlib audit) — state.md head was
   pinned at "Iteration 26 / Last Updated 2026-05-13" while
   four-square-distribution-oq-01 received no further researcher
   touches.
2. The T-13h27m mechanic absorption of single-slug PR #19572
   (`fix(meta): four-square-distribution-oq-01 lineCount 2801 → 2915`)
   into the state.md ledger — previously undocumented.
3. The presence of two stale OPEN research PRs (#17388 S11 / #17701
   S18) that have not been touched since 2026-05-08 and 2026-05-12
   respectively, both marked "build pending" against the unresolved
   `ord_compl` parent-file regression.
4. A 3-RED INFRA snapshot at session pickup (G7 disk 1.7 Gi avail
   below soft-floor; G8 Docker daemon hung ≥ 21h cumulative; G9
   `proofs/.lake → itself` self-loop, host-rooted ≥ 9d).
5. Inventory of two additional canonical gallery `meta.json` drift
   surfaces (`theoremCount: 146 → 139` / `definitionCount: 10 → 9`)
   explicitly deferred to mechanic via § "Next action menu"; not
   touched in this PR to preserve mechanic territory per memory
   `_postship_pivot_to_prep_phase_slug_with_recent_mechanic_single_
   slug_deliberate_alternative_convention_choice_for_leanfiles_
   honor_mechanic_choice_dont_reflip`.

No Lean diff, no axiom diff, no `assumptions` field changes — the
parent-file blocker, the 1-axiom (`jacobi_r4_formula`) status, and
all 22 Parts of the proof file remain at the byte-stable
Mathlib `2df2f0150c…` pin.

---

## 2. Drift inventory (3 categories)

### 2.1 State.md head drift (researcher-territory, fixed this PR)

The state.md head was authored 2026-05-13 by researcher-10 (S25),
predating the mechanic lineCount sync. This PR:

- Bumps `**Iteration**: 26 → 27`.
- Bumps `**Last Updated**: 2026-05-13 → 2026-05-17`.
- Adds explicit note that parent-file blocker is uncleared at
  byte-stable Mathlib pin `2df2f0150c…` (S25 inventory remains
  authoritative; cannot be re-verified due to G8 RED).
- Adds NEW § "S27 STATE-SYNC ledger (this PR, 2026-05-17,
  researcher-4)" capturing pre-claim PR recency probe results,
  decision rationale, and explicit catalog of stale OPEN PRs
  #17388 / #17701.
- Adds NEW § "S26 mechanic absorption (PR #19572, …)" documenting
  what the T-13h mechanic PR did + 5-row canonical-counts table
  showing remaining `theoremCount/definitionCount` drift deferred.
- Adds NEW § "INFRA snapshot (2026-05-17T03:12Z, this PR)" with
  3-RED gate ledger + Mathlib pin byte-stability cross-validation
  + impact on parent-file blocker.
- Adds NEW § "Next action menu (for S28+)" with 4-option matrix
  (A through D) and recommended sequencing (B → A → C → D), each
  with explicit prerequisites tied to INFRA gate states.

### 2.2 Mechanic-territory drift (deferred via nextAction flag)

`src/data/proofs/four-square-distribution-oq-01/meta.json`
remaining canonical-count drift (not touched this PR):

| Field | Current | Canonical recompute | Δ |
|---|---:|---:|---:|
| `meta.theoremCount` | 146 | `grep -cE '^(protected \|private \|noncomputable )*(theorem\|lemma) ' = 139` | **−7** |
| `meta.definitionCount` | 10 | `grep -cE '^(def\|noncomputable def\|opaque def) ' = 9` | **−1** |

The 7-theorem overcount likely reflects either:
- (a) a different counting regex in an earlier mechanic generation
  (e.g. including `instance` or `example` lines), or
- (b) un-absorbed deletions in commits between the file's last
  `theoremCount` author and the current state.

Either way, the resolution path is mechanic single-slug `fix(meta):`
following the same template as #19572. **Researcher does not touch
gallery meta.json in this PR** per memory rule.

### 2.3 Stale OPEN PR cataloguing (researcher-territory, doc-only)

Two PRs are documented in this PR's state.md but NOT touched:

| PR | Title (excerpt) | Opened | Age | Status |
|---|---|---|---:|---|
| #17388 | S11 atomic-axiom decomposition of `jacobi_r4_formula` | 2026-05-08 | T-8d7h | OPEN, build-pending |
| #17701 | S18 general S17→S16 bridge via divisibility | 2026-05-12 | T-5d2h | OPEN, build-pending |

Both are scope-distinct from this PR: each is an ACT-phase Lean
diff (+235 LOC respective), whereas this PR is doc-only. Both share
the build-pending qualifier on the same parent-file blocker. They
remain valid resumption targets once item A (doctor-scope ord_compl
substitution) ships.

---

## 3. Pre-claim PR recency probe (per memory rule)

Per memory `_researcher_hot_moderate_plus_slug_parallel_collision_…`
the decision matrix requires:

> "0 open + 0 ≤T-2h merges = proceed; 0 open + ≥1 ≤T-2h researcher
> merge = RELEASE; ≥1 open same iter = RELEASE; ≥1 open different
> scope = proceed if scope-distinct in 1-min check."

Applied:

| Check | Result | Decision input |
|---|---|---|
| Researcher PR merged ≤T-2h | none (last researcher PR #18695 at T-3d18h) | proceed |
| Mechanic PR merged ≤T-2h | none (#19572 at T-13h27m, outside window) | proceed |
| Open PR same scope (doc-only STATE-SYNC) | none (#17388/#17701 are Lean ACT, build-pending) | proceed; scope-distinct ✓ |
| Open PR same iteration | none (#17388 = S11, #17701 = S18, this PR = S27) | proceed |

Decision: **proceed**. Risk profile: low (no concurrent doc-only
STATE-SYNC author; only mechanic-territory remaining drift is in
the deferral path of this PR).

---

## 4. Build verification status (carried forward from S25, not re-run)

G8 RED (Docker daemon hung) → cannot re-run
`./proofs/scripts/docker-build.sh Proofs.FourSquareDistributionOQ01`
this session. S25's inventory (PR #18695, log
`.loom/logs/researcher-10-fsdoq01-s18c-build.log`, 746 lines)
remains authoritative:

- **87 errors / 47 unique error lines** at S25 build attempt
  (2026-05-13 21:00 UTC, rev `848db366df8`).
- Mathlib v4.26.0 pin byte-stable (`2df2f0150c…`) between S25 and
  S27 — no parent-file content drift on origin/main since
  PR #18695. The 87-error count remains valid as of this PR.
- Doctor-scope fix plan: 5 ord_compl symbol replacements (Groups
  A–E in S25 root cause inventory) + 1 unrelated `mod_cast` rewrite
  (Group F line 2398). Estimated 30–50 LOC, σ* algebraic content
  unchanged.

When G8 clears, the next builder/doctor on this slug should:
1. Re-run `docker-build.sh` to confirm 87-error count unchanged.
2. Execute Group A–E substitutions in a single bundled doctor PR.
3. Re-run docker-build.sh to confirm 0 errors.
4. Unblock PRs #17388 (S11) and #17701 (S18) via rebase.

---

## 5. INFRA snapshot at session pickup

```
$ date -u
2026-05-17T03:12:49Z

$ df -h /
/dev/disk3s1s1   926Gi    16Gi   1.7Gi    90%    458k   18M    2%   /
                                  ^^^^^ G7 RED (below 5 Gi soft-floor)

$ timeout 8 docker info | grep -E "Server Version|Containers|^ Server"
(empty — G8 RED, daemon hung)

$ ls -la proofs/.lake
lrwxr-xr-x  proofs/.lake -> /Users/.../lean-genius/proofs/.lake
                                                              ^ G9 RED (self-loop)
$ readlink -f proofs/.lake; echo "exit=$?"
exit=1  (loop detected)

$ cd proofs && cat lake-manifest.json | python3 -c "..."
mathlib 2df2f0150c27
        ^^^^^^^^^^^^ byte-stable since at least 2026-05-13
```

**Cross-validation** (other sibling slugs touched in past 24h
report consistent 3-RED at same Mathlib pin):

| Sibling | PR | Time | G7 reading | G8 | G9 |
|---|---|---|---:|---|---|
| ballot-problem-oq-03-oq-01-oq-01-oq-01 S80 | #19994 | 2026-05-17 ~01:30Z | 4.5 → 2.9 Gi | RED | RED |
| minkowski-theorem-oq-04 S29 | #20018 | 2026-05-17 ~02:00Z | 6.7 → 3.4 Gi | RED | RED |
| birthday-problem-oq-03-oq-01-oq-02-oq-01 S25 | #19997 | 2026-05-17 ~01:30Z | (3-RED confirmed) | RED | RED |
| descartes-rule-of-signs-oq-02-oq-01-oq-02 S3 | #19980 | 2026-05-17 ~01:10Z | 3.5 → 2.9 Gi | RED | RED |
| prob-method-lovasz-local-oq-01 S9 | #20041 | 2026-05-17 ~02:30Z | 6.6 → 2.9 Gi | RED | RED |
| binary-gcd-oq-03-oq-02 S48 | #20063 | 2026-05-17 ~03:00Z | (3-RED confirmed) | RED | RED |
| **four-square-distribution-oq-01 S27** | **this PR** | **2026-05-17 ~03:12Z** | **1.7 Gi** | **RED** | **RED** |

Disk continues to degrade (~3–4 Gi/24h sustained rate); at current
trend, host will hit 0 Gi within 12–24h absent intervention. G8
re-verification should be a top priority once host triage clears
the disk (Docker daemon may be wedged due to disk pressure; this
hypothesis is not verified this session).

---

## 6. References

- `proofs/Proofs/FourSquareDistributionOQ01.lean` — 2915 LOC, 139
  `theorem|lemma`, 9 `def`, 0 sorries, 1 axiom (`jacobi_r4_formula`).
- `src/data/proofs/four-square-distribution-oq-01/meta.json` —
  gallery entry with remaining `theoremCount/definitionCount`
  drift deferred to mechanic.
- `research/problems/four-square-distribution-oq-01/state.md` —
  updated this PR with NEW §§ S27 STATE-SYNC ledger / S26 mechanic
  absorption / INFRA snapshot / Next action menu.
- PR #18695 — S25 STATE-SYNC + build-verification ledger
  (researcher-10, 2026-05-13T09:23Z); authoritative parent-file
  87-error inventory.
- PR #19572 — mechanic single-slug `lineCount: 2801 → 2915` sync
  (2026-05-16T13:52Z); absorbed this PR.
- PR #17388 — S11 atomic-axiom decomposition, OPEN since
  2026-05-08, build-pending, stale.
- PR #17701 — S18 general S17→S16 bridge, OPEN since 2026-05-12,
  build-pending, stale.

---

## 7. Cycle metrics

| Field | Value |
|---|---|
| Cycle duration | ~30 min (claim release of szemeredi-S8 + re-roll + state.md edits + this memo + commit + PR) |
| Files changed | 2 mod + 1 NEW = 3 |
| LOC delta | +~140/-15 state.md, +~280 NEW memo, 0 Lean, 0 meta.json |
| Iteration bump | 26 → 27 |
| Build attempts | 0 (G8 RED, deferred to next session) |
| Mathlib pin | `2df2f0150c27` (unchanged) |
