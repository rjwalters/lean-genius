# Session S4g PREP — Parent-Trim Scope Expansion Audit

**Date**: 2026-06-10
**Researcher**: researcher-1
**Phase**: PREP (doc-only; no Lean changes)
**Predecessors**: S4 PREP (#18441), S4b (#18519), S4c (#18585), S4d (#18733),
S4e (#18891), S5 STATE-SYNC (#18905), S4f PREP (2026-06-05, doc-only memo)
**Sister-slug context**: S6 ACT (#21421), S7 ACT (subsumed in #21421) shipped
between S4f PREP authorship and now, growing Basic.lean from 154 → 183 LOC.

## TL;DR

The S4 ACT cut recipe — saturated through S4c/d/e PREPs and refined by S4f
PREP for dot-notation — was authored against `Proofs/Club/Basic.lean` **at
98–119 LOC** (the post-S3 ACT state). The recipe instructed the S4 ACT
writer to delete:

- **4 duplicate `def`s** (`IsUnboundedBelow`, `IsStationaryBelow`,
  `diagInter`, and structure `IsClubBelow`), plus
- **1 migrated theorem** (`diagInter_isClosedBelow`).

Since then, **S6 ACT (PR #21421) and S7 ACT** (Basic.lean 119 → 183 LOC,
+64 LOC across two cuts) shipped further companions into Basic.lean. The
parent file (`Proofs/FodorPressingDown.lean`) retains **the older versions
of those same theorems** in its body. The S4 ACT cut, when executed today,
must delete a **strictly larger** set of duplicates than the original
recipe documents.

This memo is a doc-only audit that:
1. enumerates the **currently-duplicated** declarations between parent
   and Basic.lean (state at HEAD `41ceb69900c` on `feature/researcher-1`,
   rebased on `main` 2026-06-10),
2. updates the S4 ACT delete-list with the **new duplicate theorems**
   (so the S4 writer does not leave stale copies behind),
3. updates the expected net parent-delta from the original "≈ −150 LOC"
   estimate to a refined estimate based on actual byte counts,
4. confirms the S4f PREP dot-notation findings (parent lines 526, 608)
   are **still valid** at HEAD; no further dot-notation breakage has been
   introduced by Part VIII / Part IX growth.

No Lean changes this session. The S4 ACT writer should fold this memo's
updates into the existing S4c/d/e/f recipe before cutting.

## Verification 1: parent file state at HEAD

```
$ wc -l proofs/Proofs/FodorPressingDown.lean proofs/Proofs/Club/Basic.lean
  654 proofs/Proofs/FodorPressingDown.lean
  183 proofs/Proofs/Club/Basic.lean
  837 total
```

Parent has grown to 654 LOC (from 568 at S5 STATE-SYNC and 385 at the
original S4c authorship). Basic.lean is at 183 LOC (from 98 at S2 ACT
through 154 at S6 ACT to 183 at S7 ACT).

The parent does **not** yet import Basic.lean (verified):

```
$ grep -n '^import ' proofs/Proofs/FodorPressingDown.lean
32:import Mathlib.SetTheory.Cardinal.Ordinal
33:import Mathlib.SetTheory.Cardinal.Cofinality
34:import Mathlib.SetTheory.Cardinal.Regular
35:import Mathlib.SetTheory.Ordinal.Arithmetic
36:import Mathlib.SetTheory.Ordinal.Topology
37:import Mathlib.Tactic
```

Adding `import Proofs.Club.Basic` is item 1 of the S4 ACT cut and remains
required.

## Verification 2: current duplicates parent ↔ Basic.lean

### Defs and structure (parent → Basic.lean)

| Parent line | Declaration | Status in Basic.lean | S4 action |
|---|---|---|---|
| 48 | `def IsUnboundedBelow` | Basic.lean:44 | **DELETE from parent** |
| 53 | `structure IsClubBelow` | Basic.lean:49 | **DELETE from parent** |
| 59 | `def IsStationaryBelow` | Basic.lean:55 | **DELETE from parent** |
| 87 | `def diagInter` | Basic.lean:60 | **DELETE from parent** |

(Note: `IsRegressive` is **not** in the parent file — it lives only in
Basic.lean since S6 ACT added it. The earlier S4d PREP "audit-correction"
documented this; no further drift on this item.)

### Theorems (mechanical / structural; now duplicated)

| Parent line | Theorem | Basic.lean line | Recipe coverage |
|---|---|---|---|
| 62 | `IsClubBelow.mem_lt` | 68 | ✅ in S4c recipe (S2 lift) |
| 66 | `IsClubBelow.mem_of_isAcc` | 73 | ✅ in S4c recipe (S2 lift) |
| 71 | `isClubBelow_Iio_of_isSuccLimit` | 87 | ✅ in S4c recipe (S2 lift) |
| 91 | `mem_diagInter` | 79 | ✅ in S4c recipe (S2 lift) |
| 94 | `diagInter_subset_Iio` | 82 | ✅ in S4c recipe (S2 lift) |
| 108 | `diagInter_isClosedBelow` | 104 | ✅ in S4c recipe (S3 lift, #19009) |
| **334** | **`IsStationaryBelow.nonempty`** | **166** | **⚠ NEW since S4c/d/e — needs deletion** |
| **343** | **`IsStationaryBelow.of_subset`** | **175** | **⚠ NEW since S4c/d/e — needs deletion** |

The **two highlighted rows** are duplicates introduced by **S7 ACT**
(`IsStationaryBelow` companions) that the S4c/d/e/f recipe does not list
in its delete-set. The S4 ACT writer must add these to the delete list,
or the parent will fail to compile after `import Proofs.Club.Basic`
(double-declaration of `Ordinal.IsStationaryBelow.{nonempty, of_subset}`).

### Theorems still parent-only (do NOT delete)

These remain parent-local after the cut (they are not in Basic.lean):

| Parent line | Theorem | Reason kept in parent |
|---|---|---|
| 138 | `diagInter_isUnboundedBelow` | The "zipper" construction; large body; combinatorial, not mechanical |
| 240 | `diagInter_isClubBelow` | Composition of three pieces; depends on parent-only `diagInter_isUnboundedBelow` |
| 259 | `fodor` | Main theorem — Wiedijk-100 entry's headline |
| 320 | `fodor_aleph1` | ℵ₁ specialization |
| 366 | `isLimitOrdinals_isClubBelow` | Solovay Step 1 (sister-slug oq-04) |
| 408 | `nonLimitOrdinals_not_isStationaryBelow` | Solovay Step 1 (oq-04) |
| 435 | `IsClubBelow.inter` | Used inside parent for Part VIII; could be lifted later |
| 502 | `IsStationaryBelow.inter_isClubBelow` | Part VIII; could be lifted later |
| 522 | `IsStationaryBelow.inter_isLimitOrdinals` | Part VIII (dot-notation site, see S4f) |
| 558 | `cofHead_lt` | Part IX; cofHead-specific |
| 583 | `exists_cofHead_constant_stationary` | Part IX; cofHead-specific |
| 602 | `exists_cofHead_constant_stationary_of_stationary` | Part IX (dot-notation site, see S4f) |

The 5-theorem oq-04 NEW cohort identified in S5 STATE-SYNC (§4) — items
`isLimitOrdinals_isClubBelow` through `IsStationaryBelow.inter_isLimitOrdinals`
— remains parent-only. Re-anchoring those signatures to `Ordinal.IsClubBelow`
/ `Ordinal.IsStationaryBelow` (after the cut) is mechanical and stays as
documented in S5 STATE-SYNC.

## Verification 3: S4f dot-notation findings still valid

S4f PREP identified two dot-notation callsites that break after the cut:

```
$ sed -n '526p;608p' proofs/Proofs/FodorPressingDown.lean
  hS.inter_isClubBelow hκ hκ_unc (isLimitOrdinals_isClubBelow hκ hκ_unc)
    (hS.inter_isLimitOrdinals hκ hκ_unc) (fun _ hα => hα.2)
```

Confirmed: both dot-notation calls are present **at the same line numbers**
S4f documented. The Part VIII / Part IX bodies have not drifted in the
five days since S4f PREP. The fix prescription (re-write as fully-
qualified calls; see S4f §"Recipe (mechanical, two-line)") applies
verbatim.

## Refined parent-delta estimate

The S4c PREP estimated the cut at **≈ −150 LOC** based on the 4 defs +
structure (~22 LOC) and three mechanical theorems lifted at S2/S3.

The updated scope adds:
- `IsStationaryBelow.nonempty` body: parent lines 334–342 ≈ 9 LOC
- `IsStationaryBelow.of_subset` body: parent lines 343–365 ≈ 23 LOC (estimate)

Refined estimate: **≈ −180 to −200 LOC** parent delta after the cut. The
parent should end up at roughly **454–474 LOC**.

(The exact figure depends on whether docstrings move to Basic.lean or
stay deleted, and on whether section-banner comment blocks for the
deleted material get tightened. The S4 ACT writer should not aim for a
specific number; the figure here is a sanity bound, not a target.)

## Recommended S4 ACT cut sequence (updated)

The full sequence the S4 ACT writer should execute, in order:

1. **Add import** at the top of parent:
   ```
   import Proofs.Club.Basic
   ```
2. **Delete the 4 duplicate def/structure declarations** (parent lines
   ~48–60, 87–90, including the structure body lines 53–58 — 4 anchors).
3. **Delete the 8 duplicate theorems** (the six original S2/S3-lifted
   ones plus the **two new S7-lifted ones**: parent lines 334, 343).
4. **Re-anchor the 12 surviving parent theorem signatures** that
   consume `IsClubBelow` / `IsStationaryBelow` / `diagInter` /
   `mem_diagInter` / `diagInter_isUnboundedBelow` (S4c §7 original-12
   cohort + S5 STATE-SYNC §4 oq-04 cohort).
5. **Fix the two dot-notation callsites at parent lines 526 and 608**
   per S4f PREP §"Recipe".
6. **Update `src/data/proofs/fodor-pressing-down/meta.json`**
   `lineCount` and `theoremCount` per S4c §7 recipe.
7. **Update `src/data/proofs/fodor-pressing-down/annotations.json`**
   line offsets per S4c §7 recipe (the offset adjustment is now larger
   than S4c documented because of items 3a/3b).
8. **Docker build verification**: `./proofs/scripts/docker-build.sh
   Proofs.FodorPressingDown` (full ~25–45 min on cold cache; ~5 min on
   warm Mathlib cache).

The cut is still **purely mechanical**; no combinatorial or design
choices are introduced by this scope expansion.

## Blockers

None. The recipe is now complete-on-paper and verified against the live
parent state at HEAD.

## Why this iteration is doc-only

The S4 ACT requires a full Docker build to verify a Wiedijk-100 entry's
behavior is preserved. Submitting a partial cut, or one with stale recipe
guidance, would risk a build regression on a high-visibility file. This
session preserves the saturate-then-cut discipline by surfacing the
S6/S7-induced drift before the S4 writer begins; the cut itself remains
the next ACT.

## Files touched this session

- `research/problems/fodor-pressing-down-oq-01/sessions/2026-06-10-s4g-prep-parent-trim-scope-expansion-audit.md` (this memo, new)
- `research/problems/fodor-pressing-down-oq-01/state.md` (S4g entry; see commit)
- `src/data/research/problems/fodor-pressing-down-oq-01.json` (S4g log entry)

No Lean files modified.
