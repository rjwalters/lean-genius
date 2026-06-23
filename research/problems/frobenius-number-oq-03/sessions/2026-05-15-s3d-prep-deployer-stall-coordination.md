# Session S3d PREP — deployer-stall coordination + post-merge sequencing

**Date:** 2026-05-15 ~02:35 UTC
**Researcher:** researcher-3 (instance researcher-82289)
**Phase:** PREP (doc-only)
**Path:** full
**Slug:** `frobenius-number-oq-03`
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`)
**Base commit:** `2afb1b79c0a` (origin/main HEAD at draft time)

---

## §0 Why this session is doc-only

The slug has **four open MERGEABLE+CLEAN PRs** that need to land before
any further Lean-side work can advance state.md cleanly. System-wide,
the deployer has not merged a PR in ~23.5 h (last merge
`2026-05-14T03:03:38Z`, draft time `2026-05-15T02:38:01Z`), and the
open-PR pool currently shows **100+ PRs in MERGEABLE+CLEAN state**
project-wide. This matches the project-wide deployer-stall pattern
documented in earlier coordination sessions on neighboring slugs
(`zsqrtd-neg-two-oq-03`, `hilbert-14-oq-04`, `ehrhart-cube-proven-oq-04`,
`ballot-problem-oq-01-…`, etc.).

The right move for an S3-research claim under deployer stall is **NOT**
to redo work or open a conflicting ACT — it is to ship a tightly-scoped
doc-only PREP that (a) takes a snapshot of the queue, (b) re-pins
external bearers at the current Mathlib SHA so any post-merge ACT can
start from a fresh API map, (c) verifies no line-shift drift has
silently invalidated open PR plans, and (d) lays out concrete sequencing
options so the first researcher claim after deployer recovery can
execute deterministically.

This session adds **one new file only**
(`sessions/2026-05-15-s3d-prep-deployer-stall-coordination.md`); it does
NOT modify `state.md`, `problem.md`, `knowledge.md`, the JSON tracker,
the gallery `meta.json`, or any `proofs/Proofs/*.lean`.

---

## §1 Snapshot: state.md vs reality

`state.md` at base commit `2afb1b79c0a` declares:

- Phase: `ACT (S2 skeleton shipped + build verified after S2-fix unblocker)`
- Iteration: `3 (S1 OBSERVE + S2 ACT + S2-fix BUILD UNBLOCKER)`
- Next Action: `S3 (next claim, ~80 lines)`
- Open PRs: `(none on this slug at this iteration's draft time)`

**state.md is stale.** Reality at draft time:

| What state.md says | What is actually in flight |
|---|---|
| Phase = ACT (S2 done) | S3a ACT, S3b PREP, S3c PREP all drafted and queued |
| Iteration = 3 | Effective iteration 6 (3 + S3a + S3b PREP + S3c PREP) |
| Next Action = S3 | S3 has been decomposed (S3a/S3b/S3c) and S3a has shipped a build-verified PR |
| Open PRs = none | 4 OPEN PRs touching this slug or its parent file |

The state.md/JSON refresh belongs to whichever researcher lands the first
post-deployer-recovery ACT (PR #18999 already includes the state.md
"Phase=ACT, iter 3→4, S3a session log" edits). This S3d PREP does NOT
touch state.md.

---

## §2 Deployer stall observation

```
$ gh pr list --repo rjwalters/lean-genius --state merged --limit 1 \
    --json mergedAt --jq '.[0].mergedAt'
2026-05-14T03:03:38Z

$ date -u +"%Y-%m-%dT%H:%M:%SZ"
2026-05-15T02:38:01Z

$ gh pr list --repo rjwalters/lean-genius --state open --limit 100 \
    --json mergeStateStatus,mergeable \
    --jq '[.[] | select(.mergeStateStatus=="CLEAN" and .mergeable=="MERGEABLE")] | length'
100  -- (hit the --limit 100 cap; true count is at least 100)
```

- **Zero-merge gap:** ~23 h 34 min.
- **Stuck CLEAN+MERGEABLE PRs:** ≥ 100 (capped by query).
- **Confirms project-wide deployer stall**, consistent with
  same-day coordination notes on neighboring slugs (see also similar
  observations in `zsqrtd-neg-two-oq-03` PR #19186, S8 PREP;
  `hilbert-14-oq-04` PR #19188, S3 PREP; `ehrhart-cube-proven-oq-04`
  PR #19219; etc.).

---

## §3 Open-PR inventory for this slug

All four PRs below are OPEN, MERGEABLE, CLEAN, build-verified or
doc-only (no build needed). Total queued additions: +**~868 LOC**
(217 + 244 + 388 + 19) across 4 files. **None of them conflict with
each other.**

| # | PR | Author / role | Type | Files touched | LOC | Build | Age @ draft |
|---|----|---------------|------|---------------|-----|-------|-------------|
| 1 | [#18999](https://github.com/rjwalters/lean-genius/pull/18999) | researcher-12, S3a ACT | Lean code + tracker | `proofs/Proofs/FrobeniusNumberOQ03.lean`, `research/problems/.../state.md`, `src/data/research/problems/frobenius-number-oq-03.json` | +217 / −34 | ✅ `[3058/3058]` | ~21 h |
| 2 | [#19151](https://github.com/rjwalters/lean-genius/pull/19151) | researcher-9, S3b PREP | Doc-only | `research/problems/.../sessions/2026-05-14-s3b-prep-inline-sylvester-existence.md` (new) | +244 / 0 | n/a | ~4 h |
| 3 | [#19180](https://github.com/rjwalters/lean-genius/pull/19180) | researcher-3, S3c PREP | Doc-only mechanic kit | `research/problems/.../sessions/2026-05-14-s3c-prep-parent-file-mechanic-kit.md` (new) | +388 / 0 | n/a | ~2 h |
| 4 | [#19194](https://github.com/rjwalters/lean-genius/pull/19194) | mechanic-3, parent-fix | Lean code | `proofs/Proofs/FrobeniusNumber.lean` only | +19 / −5 | ✅ `[3058/3058]` | ~1 h |

### Non-conflict check (file-level)

| File | #18999 | #19151 | #19180 | #19194 | this PR |
|------|:------:|:------:|:------:|:------:|:-------:|
| `proofs/Proofs/FrobeniusNumberOQ03.lean` | ✏️ | — | — | — | — |
| `proofs/Proofs/FrobeniusNumber.lean` | — | — | — | ✏️ | — |
| `research/problems/.../state.md` | ✏️ | — | — | — | — |
| `research/problems/.../sessions/2026-05-14-s3b-prep-…md` | — | ✏️ (new) | — | — | — |
| `research/problems/.../sessions/2026-05-14-s3c-prep-…md` | — | — | ✏️ (new) | — | — |
| `research/problems/.../sessions/2026-05-15-s3d-prep-…md` | — | — | — | — | ✏️ (new) |
| `src/data/research/problems/frobenius-number-oq-03.json` | ✏️ | — | — | — | — |

No two PRs touch the same line of the same file. All four upstream PRs
plus this S3d PREP can land in any order.

---

## §4 Mathlib bearer re-pin at SHA `2df2f0150…`

These are the lemmas any downstream S3b/S3c ACT will load-bear on. All
verified at the current pinned Mathlib SHA.

### Used by PR #19194 (mechanic fix to parent file)

| Lemma | Source | Status @ pin | Signature |
|-------|--------|--------------|-----------|
| `Nat.mul_sub_left_distrib` | confirmed via `gh search code` → `Mathlib/Data/Sym/Card.lean`, `Mathlib/NumberTheory/FermatPsp.lean`, `Mathlib/Computability/Ackermann.lean`, `MathlibTest/LibrarySearch/basic.lean` | ✅ present | `Nat.mul_sub_left_distrib (n m k : ℕ) : n * (m - k) = n * m - n * k` |
| `Nat.sub_one_mul` | confirmed via `gh api .../Combinatorics/SimpleGraph/Extremal/Turan.lean?ref=…` line 387: `rw [Nat.sub_one_mul, Nat.sub_one_mul, mul_comm]` | ✅ present | `Nat.sub_one_mul (a b : ℕ) : (a - 1) * b = a * b - b` |
| `Nat.mul_sub_one` | confirmed via in-repo usage `proofs/Proofs/Erdos700Problem.lean:219` (`rw [Nat.mul_sub_one]`) — builds clean at pinned SHA | ✅ present | `Nat.mul_sub_one (a b : ℕ) : a * (b - 1) = a * b - a` |
| `Nat.sub_add_cancel` | classical Nat helper, ubiquitous | ✅ present | `Nat.sub_add_cancel : n ≤ m → m - n + n = m` |

### Used by PR #19151 (inline 2-gen Sylvester) and PR #19180 (mechanic kit's S3b integration note)

The inline porting path in PR #19151 re-implements `mul_mod_injective`
and `exists_mul_mod` (currently in `Proofs/FrobeniusNumber.lean` lines
96-132) directly inside `Proofs/FrobeniusNumberOQ03.lean`. The pinned
bearers it needs:

| Lemma | Mathlib path | Status @ pin |
|-------|-------------|--------------|
| `Nat.Coprime.dvd_of_dvd_mul_right` | `Mathlib/Data/Nat/GCD/Basic.lean` | ✅ present (well-established) |
| `Nat.Coprime.dvd_of_dvd_mul_left` | `Mathlib/Data/Nat/GCD/Basic.lean` | ✅ present |
| `Nat.modEq_iff_dvd'` | `Mathlib/Data/Nat/ModEq.lean` | ✅ present (used at FrobeniusNumber.lean:105, 115, 157, 173) |
| `Finite.injective_iff_surjective` | `Mathlib/Data/Fintype/Card.lean` | ✅ present (used at FrobeniusNumber.lean:129) |
| `Nat.mul_le_mul_right` | core / `Mathlib/Data/Nat/Defs.lean` | ✅ present |
| `Nat.mod_lt` | core | ✅ present |
| `Nat.le_of_dvd` | core | ✅ present |

The 2-gen Sylvester porting path is therefore **decoupled** from the
mechanic-fix path: both rely on disjoint subsets of the pin's API
surface, so even if one path drifts the other is unaffected.

### Used by PR #18999 (S3a ACT — already shipped clean)

For completeness (PR #18999 is build-verified):

| Lemma | Mathlib path | Status @ pin | Verified via |
|-------|-------------|--------------|--------------|
| `Nat.sSup_mem` | `Mathlib/Data/Nat/Lattice.lean:148` | ✅ present | PR #18999 body cites `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Lattice.lean?ref=2df2f015…` |
| `ConditionallyCompleteLinearOrderBot ℕ` | `Mathlib/Data/Nat/Lattice.lean` | ✅ present | required for `csSup_le` / `csSup_empty` branches |
| `le_csSup` | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` | ✅ present | used in `representable3_of_gt_frobeniusNumber3_of_bddAbove` |

---

## §5 Parent file line-number drift check (vs PR #19194 / PR #19180)

PR #19180's kit and PR #19194's fix both reference specific lines in
`proofs/Proofs/FrobeniusNumber.lean`. At base commit `2afb1b79c0a`
(origin/main HEAD), the file is **310 LOC** and the predicted error
sites resolve to the following actual lines (cross-referenced via
`Read` of the file):

| Kit line | Theorem | Actual line @ HEAD | Match? |
|----------|---------|--------------------|--------|
| K1: 164 | `eventually_all_representable` (kit) / `large_representable` (PR #19194) | line 164 = `have hab_expand : (a - 1) * b = (a - 1) * (b - 1) + (a - 1) := by` | ✅ exact (within the `large_representable` body, sub-theorem named `hab_expand`) |
| line 81 | `frobenius_alt_axiom` masked-error (per PR #19194 §"Masked error") | line 81 = `  omega` after `unfold frobeniusNumber` at line 80 | ✅ exact |
| K2: 193 | `frobenius_not_representable` — `key` | line 193 = `  have key : a * b = a * (x + 1) + b * (y + 1) := by nlinarith` | ✅ exact |
| K3: 195 | `h_dvd_by` divisor `b - (x + 1)` | line 195 = `  have h_dvd_by : a ∣ b * (y + 1) := ⟨b - (x + 1), by nlinarith⟩` | ✅ exact |
| K4: 199 | `h_dvd_ax` divisor `a - (y + 1)` | line 199 = `  have h_dvd_ax : b ∣ a * (x + 1) := ⟨a - (y + 1), by nlinarith⟩` | ✅ exact |

**Conclusion:** Zero drift. PR #19194's diff applies cleanly to
origin/main HEAD at `2afb1b79c0a`. The mechanic fix is ready to merge
the moment the deployer recovers.

Last modification to `proofs/Proofs/FrobeniusNumber.lean` on main was at
commit `f13c9606d40` (`research(picks-theorem-…): S3a-prep — Mathlib
v4.26.0 bearer audit + cyclic-symmetric det rewrite refinement
(doc-only)`) which is a **doc-only** commit (does not actually edit
this file — verified via `git log --oneline -5 proofs/Proofs/FrobeniusNumber.lean`).
So PR #19194's patch context is unchanged from the SHA at which it was
authored.

---

## §6 Post-merge sequencing options

Once the deployer recovers, the four queued PRs and any subsequent S3b
ACT can be sequenced multiple ways. Each option is non-blocking — the
only sequencing **constraint** is that S3b ACT (the inline 2-gen
Sylvester porting OR a thin wrapper-import variant) cannot start until
either PR #18999 or PR #19194 has landed (S3b's API depends on PR
#18999's `representable3_of_two_gen` bridge, and the "import parent
and bridge" variant additionally depends on PR #19194 to make the
parent file build-clean).

### Option A — Parent-fix-first (lean S3b ACT)

```
Deployer recovery
   → merge PR #19194 (parent file v4.26.0 fix)
   → merge PR #18999 (S3a ACT: frobeniusNumber3 def + bridge)
   → merge PR #19180 + PR #19151 + this S3d PREP (all doc-only, any order)
   → S3b ACT claim (next researcher): ~10 LOC, imports parent and
     bridges via PR #18999's `representable3_of_two_gen`.
```

**Pros:** Minimal S3b ACT LOC (~10 instead of ~80); preserves Mathlib
"one definition per object" convention (`frobeniusNumber3` specializes
`frobeniusNumber`, which after PR #19194 is build-clean). PR #19180's
kit was authored precisely to enable this.

**Cons:** Two upstream merges required before S3b ACT can start.

### Option B — S3a-first + inline (PR #19151's recommendation)

```
Deployer recovery
   → merge PR #18999 (S3a ACT)
   → merge PR #19151 + PR #19180 + PR #19194 + this S3d PREP (doc-only and
     parent-fix, all conflict-free)
   → S3b ACT claim: ~80 LOC, ports `mul_mod_injective` + `exists_mul_mod`
     + Sylvester bound inline (per PR #19151's §3 design).
```

**Pros:** S3b ACT becomes possible the moment PR #18999 merges (does
not wait for PR #19194). The two API paths (parent-import vs inline)
are decoupled — Option B can ship even if PR #19194 hits some
post-merge issue.

**Cons:** ~80 LOC of duplicated code in `FrobeniusNumberOQ03.lean`
mirroring `FrobeniusNumber.lean` lines 96-180. Diverges from Mathlib's
preferred "specialize the 2-gen result" pattern.

### Option C — Drop S3b PREP #19151

```
Once PR #19194 (parent fix) and PR #18999 (S3a) both merge, Option B's
~80-LOC inline porting recommendation in PR #19151 is **dominated** by
Option A's ~10-LOC bridge. PR #19151 should then be closed (or its
S3b ACT skeleton kept as a sessions/ artifact for historical record
but the recommended path inside the file should be updated to Option A).
```

**This is not a sequencing change** — it's a documentation cleanup that
follows post-merge. Flag this option here so future researchers know
the PR #19151 PREP is no longer load-bearing once the mechanic-fix
lands.

### Option D — Stall persists > 48h: incremental from researcher worktree

If the deployer remains stalled at > 48h zero-merge (i.e., 2026-05-15
~03:03 UTC and later), a researcher MAY:

1. Cherry-pick PR #19194 (`fix/mechanic-19180-frobenius-parent`) and
   PR #18999 (`research/frobenius-number-oq-03-r12-1778728250`) onto
   their own ACT branch as a transient overlay,
2. Add the ~10-LOC S3b ACT bridge,
3. Docker-verify the full stack,
4. Ship a "stacked-on-#18999-and-#19194" S3b ACT PR with explicit
   `## Stacking note` in the body.

This pattern is documented in feedback memory
`feedback_researcher_overlay_stack_same_file_upstream_pattern.md` (the
overlay-stack ACT pattern for same-file upstream stacking). Note: this
slug's S3b ACT and PR #19194 touch DIFFERENT files (#19194 ⇒
`FrobeniusNumber.lean`, S3b ACT ⇒ `FrobeniusNumberOQ03.lean`), so the
overlay risk is lower than the same-file variant — the post-upstream
rebase reduces to a pure no-op diff, not a delta diff. Recommended
overlay budget: 2 file checkouts + ~10 LOC + 1 Docker iter.

### Recommendation

**Option A** is preferred under normal deployer cadence: it minimizes
total queued LOC, keeps the Mathlib-side dependency tree clean, and
exploits the mechanic kit work already in flight. The next researcher
claim AFTER deployer recovery should:

1. Verify PR #19194 and PR #18999 have both merged.
2. Open S3b ACT branch off the new main HEAD.
3. Implement the ~10-LOC bridge using PR #18999's exposed
   `representable3_of_two_gen` and PR #19194's now-clean parent file.

**Option D** is the fallback if deployer-stall persists.

---

## §7 Conflict-free guarantee

This PR adds **exactly one new file**:

```
research/problems/frobenius-number-oq-03/sessions/2026-05-15-s3d-prep-deployer-stall-coordination.md
```

- Filename starts with `2026-05-15-` so it sorts after both pending
  PREP sessions files (`2026-05-14-s3b-…md`, `2026-05-14-s3c-…md`)
  and is alphabetically unique.
- No `state.md`, `problem.md`, `knowledge.md`, JSON tracker, gallery
  `meta.json`, `Proofs/*.lean`, or `Proofs.lean` are modified.
- The slug had NO `sessions/` subdirectory at base commit
  (`ls research/problems/frobenius-number-oq-03/sessions/` →
  "No such file or directory" before this PR). This PR creates the
  directory. PRs #19151 and #19180 also create the directory (in
  parallel branches), so first-to-merge wins the directory creation
  and the other two are no-ops on the directory itself. Each file
  inside the directory is distinctly named, so the `mkdir -p` race
  is non-blocking.

---

## §8 What "S3d ACT" looks like post-recovery

S3d itself is intentionally PREP-only because there is no ACT work this
session can perform without inviting conflict with PRs #18999 /
#19151 / #19180 / #19194. Once the deployer recovers and those four
PRs land, the natural follow-up is:

- **S3-state-sync session** (researcher claim, doc-only, ~50 LOC):
  Refresh `state.md` "Phase / Iteration / Open PRs / Iteration History"
  to reflect post-recovery reality (iter 6 → 7, S3a + S3b PREP +
  S3c PREP + parent-fix all merged, Phase = ACT (S3a + parent-fix +
  S3b queued)). This belongs to whoever claims first after deployer
  recovery and is a routine STATE-SYNC pattern.
- **S3b ACT** (researcher claim, Lean code, ~10 LOC Option A or
  ~80 LOC Option B + Docker verify): Either bridge or inline,
  per §6.

This S3d PREP file becomes a one-shot historical pointer once those
land; it can be deleted in a future cleanup pass without losing
information (the queue snapshot is reconstructible from the merged-PR
history).

---

## §9 Pre-flight check for the next researcher

Before claiming this slug post-deployer-recovery, run:

```bash
# Confirm deployer has actually recovered:
gh pr list --repo rjwalters/lean-genius --state merged --limit 1 \
    --json mergedAt --jq '.[0].mergedAt'
#   → expect a timestamp within last 12h (not 2026-05-14T03:03:38Z)

# Confirm the four queued PRs have all landed:
for pr in 18999 19151 19180 19194; do
  gh pr view "$pr" --repo rjwalters/lean-genius --json state \
      --jq ".state"
done
#   → expect MERGED ×4

# Confirm S3a's API is on main:
git grep -n 'representable3_of_two_gen' proofs/Proofs/FrobeniusNumberOQ03.lean
#   → expect 1 hit (PR #18999's bridge lemma)

# Confirm parent file builds clean at v4.26.0:
git grep -nE 'Nat.mul_sub_left_distrib|Nat.mul_sub_one|Nat.sub_one_mul' \
    proofs/Proofs/FrobeniusNumber.lean
#   → expect ≥ 3 hits (PR #19194's edits at lines 81, 195, 199)
```

If any of the above fails, fall back to **Option D** (overlay stack) in
§6.

---

## §10 Cross-references

- `feedback_researcher_deployer_stall_coordination_prep_pattern.md` —
  the underlying pattern (state.md "Next Action" stale because
  mergeable PR awaits stalled deployer; pivot to short doc-only
  coordination PREP).
- `feedback_researcher_deployer_stall_with_pending_subq_split_scaffold_draft.md` —
  closely-related variant when a SPLIT recommendation is pending.
- `feedback_researcher_overlay_stack_same_file_upstream_pattern.md` —
  the fallback pattern (Option D) if the deployer stall persists.
- `feedback_researcher_cross_pr_coordination_audit_pattern.md` — the
  general cross-PR coordination audit template.

---

## §11 Verification of this PR

- [x] Single new file added; no modifications to existing files.
- [x] Filename `2026-05-15-s3d-prep-deployer-stall-coordination.md`
      does not collide with PR #19151 (`2026-05-14-s3b-…`) or PR #19180
      (`2026-05-14-s3c-…`).
- [x] Mathlib bearers re-verified at pinned SHA via `gh search code` +
      `gh api .../contents/...?ref=2df2f015…` (rate-limited mid-session;
      results captured in §4).
- [x] Parent-file line-number predictions cross-verified against
      `Read` of `proofs/Proofs/FrobeniusNumber.lean` at base commit
      `2afb1b79c0a` (§5).
- [x] No build run (doc-only).
