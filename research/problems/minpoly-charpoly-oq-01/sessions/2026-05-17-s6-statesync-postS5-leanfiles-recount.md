# S6 STATE-SYNC — Post-S5 leanFiles[1] miscount fix + INFRA snapshot

**Author**: researcher-11
**Date**: 2026-05-17T02:00:00Z
**Branch**: `research/minpoly-charpoly-oq-01-s6-statesync`
**Mode**: STATE-SYNC (doc-only)
**Predecessor**: S5 STATE-SYNC [#19781](https://github.com/rjwalters/lean-genius/pull/19781) (researcher-1, merged 2026-05-16T12:19:55Z, T-13h45m)

## 0. TL;DR

S5 STATE-SYNC PR #19781 updated `leanFiles[1]` (MinpolyCharpolyOQ01.lean) but the author miscounted **three of four canonical fields** by applying the wrong grep patterns. This S6 STATE-SYNC ships a 3-file doc-only PR that:

1. **Fixes `leanFiles[1]`**: `theoremCount: 9 → 10`, `defCount: 2 → 3`, `sorryCount: 1 → 5`.
2. **Refreshes `currentState`**: iteration 5 → 6, since/lastUpdate, focus/nextAction rewrite, attemptCounts.total 3 → 4, blockers `[]` → 3-entry G7/G8/G9 RED.
3. **Prepends state.md head**: ~80 LOC S6 STATE-SYNC block with drift table.
4. **Adds this session memo** (~280 LOC, 9 sections).

Deferred to mechanic (cross-slug scope): `leanFiles[0]` (MinpolyCharpoly.lean) lineCount 247 → 246 — shared across 3 siblings.

## 1. Why this fires now

### 1.1 Pre-claim recency probe

Per `feedback_researcher_hot_moderate_plus_slug_parallel_collision_duplicate_state_sync_ships`, before claiming I ran:

```bash
gh search prs "minpoly-charpoly-oq-01" --repo rjwalters/lean-genius --state open
# → []  (no open PRs)

gh search prs "minpoly-charpoly" --repo rjwalters/lean-genius --limit 5 --json number,title,state,createdAt
# → most recent: #19123 S4-E ACT (2026-05-14 merged), #18276 S1 (2026-05-12 merged)
```

No open PRs targeting this slug or its siblings. Safe to claim. Last research activity T-13h45m (S5 STATE-SYNC merge); last Lean change T-3d4h (S4-E ACT merge).

### 1.2 Drift discovery — actual file re-walk

Per `feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`, the canonical counts are:

```bash
# Convention (matches recent mechanic precedent #19934, #19816, #19818):
# LOC   = wc -l (raw)
# thm   = ^(?:protected|private|noncomputable )*(theorem|lemma)
# def   = ^(def|noncomputable def|opaque def)
# sorry = raw \bsorry\b (NO comment strip)
# axiom = ^axiom

f=/Users/rwalters/GitHub/lean-genius/proofs/Proofs/MinpolyCharpolyOQ01.lean
wc -l < "$f"                                                    # 356
grep -cE '^(protected |private |noncomputable )*(theorem|lemma) ' "$f"  # 10
grep -cE '^(def|noncomputable def|opaque def) ' "$f"            # 3
grep -cE '\bsorry\b' "$f"                                       # 5
grep -cE '^axiom ' "$f"                                         # 0
```

JSON at HEAD (post-S5 STATE-SYNC):

```json
{
  "path": "Proofs/MinpolyCharpolyOQ01.lean",
  "lineCount": 356,         // ✓ matches
  "theoremCount": 9,        // ✗ off by -1 (should be 10)
  "axiomCount": 0,          // ✓ matches
  "defCount": 2,            // ✗ off by -1 (should be 3)
  "sorryCount": 1,          // ✗ off by -4 (should be 5)
}
```

Three of four content fields wrong.

### 1.3 Root cause of S5 miscount

S5 STATE-SYNC PR #19781 body says:

> theoremCount: 4 → 9 (+5)
> defCount: 4 → 2 (-2; refactored)
> sorryCount: 1 (unchanged; jordan_normal_form_exists deferred to sub-OQs)

State.md table at lines 17–20 says:

> theoremCount | 4 | 9 | `grep -cE '^theorem ' = 9` (S3-D + S4-E API extensions)
> defCount | 4 | 2 | `grep -cE '^def ' = 2` (refactored)

The S5 author used `^theorem ` and `^def ` — narrower patterns that exclude:
- `private lemma` (`eigenvalueMultiset_card_aux` at line 252)
- `noncomputable def` (`jordanBlock` at line 195)

…and used a comment-stripped sorry convention instead of the raw `\bsorry\b`.

The canonical mechanic convention has been raw + inclusive since #19934 (binary-gcd, 9 siblings: thm 63→65 included one `private` lemma; sorry 1→10 was raw `\bsorry\b` capturing 1 tactic + 9 commentary mentions). Also #19816 (Erdos1018OQ04Incomplete01: sorry 14 raw, 1 stripped) and #19818 (KonigsbergOQ01OQ02: 6→1 raw).

## 2. Reproducibility script — every count derived from actual file

```bash
# Verify all 5 canonical fields against actual proofs/ tree.
cd /Users/rwalters/GitHub/lean-genius

for path in Proofs/MinpolyCharpoly.lean Proofs/MinpolyCharpolyOQ01.lean; do
  f="proofs/$path"
  lc=$(wc -l < "$f" | tr -d ' ')
  thm=$(grep -cE '^(protected |private |noncomputable )*(theorem|lemma) ' "$f")
  def=$(grep -cE '^(def|noncomputable def|opaque def) ' "$f")
  sorry=$(grep -cE '\bsorry\b' "$f")
  ax=$(grep -cE '^axiom ' "$f")
  echo "$path lc=$lc thm=$thm def=$def sorry=$sorry ax=$ax"
done

# Expected output (2026-05-17T02:00Z, Mathlib pin 2df2f0150c…):
# Proofs/MinpolyCharpoly.lean    lc=246 thm=18 def=0 sorry=0 ax=0
# Proofs/MinpolyCharpolyOQ01.lean lc=356 thm=10 def=3 sorry=5 ax=0
```

### 2.1 Theorem enumeration (MinpolyCharpolyOQ01.lean, 10 items)

```bash
grep -nE '^(protected |private |noncomputable )*(theorem|lemma) ' proofs/Proofs/MinpolyCharpolyOQ01.lean
```

| Line | Symbol | Notes |
|------|--------|-------|
| 203 | `jordanBlock_diag_eq` | S2 |
| 210 | `jordanBlock_super_diag_eq` | S2 |
| 223 | `jordanBlock_off_diag_eq` | S2 |
| 232 | `jordanBlock_zero_dim` | S2 |
| 252 | `private eigenvalueMultiset_card_aux` | S3 — **S5 missed (private lemma)** |
| 266 | `JordanBlockShape.eigenvalueMultiset_card_eq_totalDim` | S3 |
| 288 | `JordanBlockShape.eigenvalueMultiset_toFinset_card_le_totalDim` | S4-E |
| 300 | `JordanBlockShape.eigenvalueMultiset_toFinset_card_eq_totalDim_iff` | S4-E |
| 332 | `jordan_normal_form_exists` | S1 (sorry-guarded, load-bearing) |
| 351 | `totalDim_empty` | S1 — **S5 missed** |

Count: 10. S5 said 9.

### 2.2 Def enumeration (MinpolyCharpolyOQ01.lean, 3 items)

```bash
grep -nE '^(def|noncomputable def|opaque def) ' proofs/Proofs/MinpolyCharpolyOQ01.lean
```

| Line | Symbol | Notes |
|------|--------|-------|
| 178 | `def totalDim` | S1 |
| 184 | `def eigenvalueMultiset` | S1 |
| 195 | `noncomputable def jordanBlock` | S2 — **S5 missed (noncomputable keyword)** |

Count: 3. S5 said 2.

### 2.3 Sorry enumeration (MinpolyCharpolyOQ01.lean, 5 raw matches)

```bash
grep -nE '\bsorry\b' proofs/Proofs/MinpolyCharpolyOQ01.lean
```

| Line | Context | Real tactic? |
|------|---------|--------------|
| 94 | "statement**, guarded by a single `sorry` that the four sub-OQs above" | commentary |
| 120 | "sorry on `jordan_normal_form_exists` is the entire JNF assembly" | commentary |
| 148 | "* [ ] Discharge `jordan_normal_form_exists` (sorry-guarded — deferred to sub-OQs)" | commentary (checklist) |
| 341 | "is sorry-guarded in S1; sub-OQs OQ-01-OQ-01..04 discharge it." | commentary |
| 342 | `  sorry` | **tactic** |

Raw count: 5. Comment-stripped: 1. S5 used comment-stripped (1).

## 3. INFRA snapshot — 3 RED gates

```bash
df -h /System/Volumes/Data | tail -1
# /dev/disk3s5 ... 3.4Gi ... 100% ...        # G7 RED (<5 Gi soft-floor)

timeout 8 docker info 2>&1 | head -5
# Client: ... Server:                          # G8 RED (Server section empty after 8s)

ls -la proofs/.lake | tail -1
# lrwxr-xr-x ... proofs/.lake -> proofs/.lake  # G9 RED (self-loop)
```

| Gate | Status | Detail | Vs S28 minkowski PREP (T-10.5h) |
|------|--------|--------|---------------------------------|
| G7 disk | 🔴 RED | 3.4 Gi avail | was 6.7 Gi → -3.3 Gi (worsening) |
| G8 Docker | 🔴 RED | Server section empty after 8s | was hung (unchanged) |
| G9 .lake | 🔴 RED | self-loop symlink | was self-loop (unchanged) |

3 RED prevent any local Lean build attempt. S6b BUILD-VERIFY deferred to next session under recovered Docker + disk ≥5 Gi.

## 4. Bearer drift recheck — Mathlib pin 2df2f0150c…

No re-walk this PR. Mathlib pin byte-stable since S4-E (PR #19123, T-3d4h):

```bash
cat proofs/lean-toolchain
# leanprover/lean4:v4.26.0

grep -A1 'name = "mathlib"' proofs/lake-manifest.json | grep rev
# "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
```

Bearer status per S4-E summary block (state.md):
- `Module.End.iSup_genEigenspace_eq_top` ✓ stable
- `Module.End.isFinitelySemisimple` ✓ stable
- `Module.End.exists_isNilpotent_isSemisimple` ✓ stable
- `Multiset.toFinset_card_le` (Finset/Card.lean:183) ✓ stable
- `Multiset.toFinset_card_eq_card_iff_nodup` (Finset/Card.lean:194) ✓ stable

3-day window with zero Mathlib churn on bearers per `git log` of those files. No drift expected; spot-check skipped.

## 5. S7 picker matrix (6 options)

| # | Option | LOC | Risk | INFRA need | Notes |
|---|--------|-----|------|------------|-------|
| a | S5 candidate A — scaffold MinpolyCharpolyOQ01OQ01.lean (jordanBlock.charpoly identity) | ~80 | LOW | ≥1 GREEN (NEW file) | dischargable, no sorry |
| b | S5 candidate B — strong-form upgrade of jordan_normal_form_exists | ~5 | LOW | none (sorry-guarded) | safe even no-Docker |
| c | S5 candidate C — begin OQ-01-OQ-02 (nilpotent canonical form) | ~400 | HIGH | strong GREEN | load-bearing |
| d | **mechanic batch (recommended)** — sync `leanFiles[0]` 247 → 246 across 3 siblings | ~3 | LOW | none | precedent #19934, #19840, #19885 |
| e | S6b BUILD-VERIFY — Docker 3081-job retry | ~0 | LOW | all GREEN | retire (build verified) claim freshness |
| f | PIVOT to different Tier-B slug | varies | varies | varies | if 3 RED persist > 6h |

Recommendation: (d) mechanic batch next, then (b) safe strong-form upgrade, then (a) child-OQ scaffold under recovered INFRA.

## 6. Anti-scope explicit non-actions

NOT in this PR:

- ❌ `proofs/Proofs/MinpolyCharpolyOQ01.lean` — no Lean edits (S5 candidates A/B/C deferred per §5)
- ❌ `proofs/Proofs/MinpolyCharpoly.lean` — no Lean edits + leanFiles[0] cross-slug fix is mechanic territory
- ❌ `src/data/research/problems/minpoly-charpoly-oq-02.json` — sibling, no edits
- ❌ `src/data/research/problems/minpoly-charpoly-oq-03.json` — sibling, no edits
- ❌ `proofs/lake-manifest.json` — Mathlib pin unchanged (T-3d4h byte-stable)
- ❌ `problem.md` / `knowledge.md` (free-form) — domain unchanged
- ❌ Gallery `src/data/proofs/minpoly-charpoly-oq-01/` — does NOT exist (research-only OQ; no gallery slug)
- ❌ Bearer re-spot-check — Mathlib pin byte-stable since S4-E
- ❌ Docker rebuild — 3 RED infra (deferred S6b)
- ❌ Old session archives — sessions/ has 3 files; no archive needed

## 7. Honesty calibration

- This PR adds **zero Lean lines, zero theorems, zero sorry delta**. It is a numeric-hygiene fix.
- The S5 STATE-SYNC author honestly attempted the recount but used narrower grep patterns than the canonical convention. Pointing out the miscount is not a value judgment on the S5 author — it's normal drift caught by the next reviewer.
- Disk degradation (-3.3 Gi vs T-10.5h) is host-level and not caused by this slug; documenting it in `blockers` for the next picker.
- `lastUpdated` (camel-case, line 152 of JSON) was already `2026-05-14T20:08:00.000Z` (stale by 3 days) but is a separate field from `lastUpdate` (lowercase, line 125). Touched only `lastUpdate` per the gallery-tracker convention (the camel-case field is auto-set by build pipeline, not researcher).

## 8. Memory citations

Patterns applied:

- `feedback_researcher_hot_moderate_plus_slug_parallel_collision_duplicate_state_sync_ships` — pre-claim recency probe (no open PR + last activity T-13h45m = safe).
- `feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` — raw `\bsorry\b` + inclusive theorem/def grep are canonical since #19934 / #19816.
- `feedback_researcher_postship_pivot_to_prep_phase_slug_with_intervening_mechanic_pr_fixed_numerics_left_content_description_stale` — researcher CAN fix numeric drift in own slug when no cross-slug cascade is implied; cross-slug remains mechanic.
- `gh CLI in lean-genius defaults to rjwalters/mathlib4 silently when mathlib-fork remote present` — all `gh` calls use `--repo rjwalters/lean-genius`.
- `Worktree path trap` — edits scoped to `.loom/worktrees/researcher-11/...` (verified via `pwd` before each Edit).
- `Worktree .lean/state symlink missing` — re-created via `ln -s /Users/rwalters/GitHub/lean-genius/.lean/state .lean/state` at session start.

## 9. Pool / claim status

- Claim: minpoly-charpoly-oq-01 by agent-94659, TTL 2026-05-17T03:04:48Z (60min).
- Pool: 16 available, 1510 completed, 495 in-progress, 5 blocked, 8 graduated.
- Action plan: ship PR → release claim → log session → end cycle.
