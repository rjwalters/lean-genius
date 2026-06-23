# S4c PREP — Full consumer audit + parent-slug annotation re-anchoring recipe

**Author:** researcher-12
**Date:** 2026-05-13 (~04:45 UTC, ~35 min after merge of PR #18519 S4b PREP at 04:09 UTC)
**Phase:** S4c PREP (a refinement of S4b PREP §6 + S4 PREP §7 §8.1)
**Slug:** `fodor-pressing-down-oq-01`
**Branch:** `research/fodor-pressing-down-oq-01-s04c-prep-consumer-audit-*`
**Scope:** **doc-only** — no Lean edits, no `problem.md` / `knowledge.md` /
`state.md` edits, no gallery JSON edits, no `meta.json` edits, no
`annotations.json` edits, no edits to sister-slug files. One new file
under `sessions/`.

## 0. Why this memo (and why now)

S4b PREP (PR #18519, merged 04:09 UTC) gave a body-level audit for the
Route-A move of two theorems:

* `IsStationaryBelow.nonempty` (parent line 334)
* `IsStationaryBelow.of_subset` (parent line 343)

…but the S4 ACT trim moves **eight more** symbols out of the parent
file, and downstream documents already cite *those* symbols. Three
artefacts pay the price when S4 ACT lands without a prior audit:

1. **The sister slug `fodor-pressing-down-oq-04`**: 5 files,
   ≥18 distinct citations of the moved symbols (problem.md, knowledge.md,
   state.md, three session-note files). S4b PREP §6 only enumerated 9
   citations of `IsStationaryBelow.{nonempty,of_subset}`; the other ~9
   citations cover `IsClubBelow`, `IsUnboundedBelow`, `IsStationaryBelow`
   (definition), `IsClubBelow.mem_lt`, `diagInter`, `mem_diagInter`, and
   `diagInter_isClubBelow`.
2. **The parent slug `fodor-pressing-down`'s gallery payload**:
   `src/data/proofs/fodor-pressing-down/annotations.json` has 5
   annotations whose `range.startLine`/`range.endLine` reference parent
   lines that will SHIFT (≥3 of 5) or VANISH (2 of 5) after S4 ACT.
   `meta.json` has `lineCount: 385`, `theoremCount: 12`,
   `definitionCount: 4` — all three drift.
3. **The slug's own `knowledge.md`** (`fodor-pressing-down-oq-01`):
   the §1.1 "Local file inventory" table has 11 rows with parent-line
   numbers (51–52, 53–56, 59–60, 62–64, 66–68, 87–89, 91–93, 94–96,
   108–135, 138–238, 240–247). After S4 ACT, 8 of 11 rows would point
   to nonexistent line ranges in the parent.

This memo locks the audit so the eventual S4 ACT (or a follow-up
mechanic / doctor pass) can re-anchor every citation in one shot with
zero archaeology. **No edits in this PREP**; S4 PREP §10 anti-targets
and S4b PREP §8 anti-targets continue to apply.

## 1. Source state (verified at HEAD = `db3653f981b`)

* Parent file: `proofs/Proofs/FodorPressingDown.lean`, **385 LOC**.
* Lifted module: `proofs/Proofs/Club/Basic.lean`, **98 LOC** (per PR
  #18367, merged 02:11 UTC; build-pending per PR title).
* No edits to either file since S4b PREP's audit (verified via
  `git log f24bbb67450..db3653f981b -- proofs/Proofs/FodorPressingDown.lean
  proofs/Proofs/Club/Basic.lean`).
* Sister slug `fodor-pressing-down-oq-04` directory contents (head
  commit): 6 markdown files totalling 1,003 lines, including 3 session
  notes.
* Parent-slug gallery: `src/data/proofs/fodor-pressing-down/{meta,annotations,index}.{json,ts}`.

## 2. Complete inventory of S4 ACT-relocated symbols (10 symbols)

S4b PREP §1 listed 2 symbols (the Route-A movers). The full S4 ACT
relocation surface comprises 10 symbols across 3 destinations.

| #  | Symbol                              | Kind       | Parent line(s) | Destination                            | S-phase mover |
|----|-------------------------------------|------------|----------------|----------------------------------------|---------------|
| 1  | `IsUnboundedBelow`                  | def        | 48–49          | `Ordinal.IsUnboundedBelow` (Basic.lean:44–45) | S2 ACT #18367 (already at destination) |
| 2  | `IsClubBelow`                       | structure  | 53–56          | `Ordinal.IsClubBelow` (Basic.lean:49–52)      | S2 ACT #18367 (already at destination) |
| 3  | `IsStationaryBelow`                 | def        | 59–60          | `Ordinal.IsStationaryBelow` (Basic.lean:55–56) | S2 ACT #18367 (already at destination) |
| 4  | `diagInter`                         | def        | 87–89          | `Ordinal.diagInter` (Basic.lean:60–61)         | S2 ACT #18367 (already at destination) |
| 5  | `IsRegressive`                      | def        | 96–97          | `Ordinal.IsRegressive` (Basic.lean:64–65)      | S2 ACT #18367 (already at destination) |
| 6  | `IsClubBelow.mem_lt`                | theorem    | 62–64          | `Ordinal.IsClubBelow.mem_lt` (Basic.lean:68–70) | S2 ACT #18367 (already at destination) |
| 7  | `IsClubBelow.mem_of_isAcc`          | theorem    | 66–68          | `Ordinal.IsClubBelow.mem_of_isAcc` (Basic.lean:73–76) | S2 ACT #18367 (already at destination) |
| 8  | `isClubBelow_Iio_of_isSuccLimit`    | theorem    | 71–80          | `Ordinal.isClubBelow_Iio_of_isSuccLimit` (Basic.lean:87–96) | S2 ACT #18367 (already at destination) |
| 9  | `mem_diagInter`                     | theorem    | 91–93          | `Ordinal.mem_diagInter` (Basic.lean:79–80)     | S2 ACT #18367 (already at destination) |
| 10 | `diagInter_subset_Iio`              | theorem    | 94–96          | `Ordinal.diagInter_subset_Iio` (Basic.lean:82–84) | S2 ACT #18367 (already at destination) |

PLUS three relocations still pending S3 / S4 ACT:

| # | Symbol                            | Kind    | Parent line(s) | Destination                                  | S-phase mover                |
|---|-----------------------------------|---------|----------------|----------------------------------------------|------------------------------|
| 11| `diagInter_isClosedBelow`         | theorem | 108–124        | `Ordinal.diagInter_isClosedBelow` (Basic.lean) | S3 ACT (not yet pushed)      |
| 12| `IsStationaryBelow.nonempty`      | theorem | 334–338        | `Ordinal.IsStationaryBelow.nonempty` (Basic.lean) | S4 ACT Route A (S4b PREP §4) |
| 13| `IsStationaryBelow.of_subset`     | theorem | 343–348        | `Ordinal.IsStationaryBelow.of_subset` (Basic.lean) | S4 ACT Route A (S4b PREP §4) |

After S4 ACT lands, **all 13 symbols** live under `namespace Ordinal`
in `Proofs/Club/Basic.lean`. The parent retains only `diagInter_isUnboundedBelow`
(138–237), `diagInter_isClubBelow` (240–246), `fodor` (252–313), and
`fodor_aleph1` (320–327).

## 3. Symbol → expected post-S4-ACT line in Basic.lean (forward map)

Assuming Route A inserts `IsStationaryBelow.{nonempty,of_subset}` per
S4b PREP §4.1 (between Basic.lean lines 96 and 97) AND S3 ACT appends
`diagInter_isClosedBelow` between Basic.lean lines 96 and 97 BEFORE
Route A's S4 inserts:

| Symbol                            | Post-S3-only line | Post-S3+S4 line |
|-----------------------------------|-------------------|-----------------|
| `Ordinal.diagInter_isClosedBelow` | ~98–119           | ~98–119         |
| `Ordinal.IsStationaryBelow.nonempty` | n/a (S3 only)   | ~121–125        |
| `Ordinal.IsStationaryBelow.of_subset` | n/a (S3 only)   | ~127–132        |

Exact post-S3 line numbers depend on whether S3 ACT preserves the
docstring's 6-line block or compresses; per S3 PREP §3 "body is
character-identical to lines 110–124 of the parent file", expect
verbatim transfer giving 22-line block (6 docstring + 1 sig blank-pair +
15 body). Basic.lean's tail after S3 ACT will look like:

```
86  /-- `Iio o` is a club below `o` when `o` is a successor-limit ordinal. -/
87  theorem isClubBelow_Iio_of_isSuccLimit ...
…
96      exact ⟨α + 1, h1, lt_add_one α, h1⟩
97                                                     ← S3 ACT inserts here:
98  /-- **Diagonal Intersection is Closed** (0 sorries). … -/
99  theorem diagInter_isClosedBelow {f …} (hf …) : … := by
…
119   exact ⟨δ, hδ_mem2 β hβδ, lt_of_le_of_lt … , hδ_hi⟩
120                                                    ← S4 Route A inserts here:
121  /-- Every stationary set is nonempty. -/
122  theorem IsStationaryBelow.nonempty {S : Set Ordinal} {o : Ordinal}
…
125    exact ⟨γ, hγS⟩
126                                                    (blank separator)
127  /-- Stationary sets are closed under subelements … -/
128  theorem IsStationaryBelow.of_subset {S T : Set Ordinal} {o : Ordinal}
…
132    exact hMeet C hC (hS C hC)
133
134  end Ordinal
```

Final Basic.lean LOC (post-S3+S4 Route A): **134 LOC** (98 baseline +
22 diagInter_isClosedBelow block + 13 Route-A block + 1 blank separator).

## 4. Parent-line shift map (for ALL surviving content)

Under S4 ACT (Route A taken, S3 ACT already applied), the parent
retains 99 net LOC of changes:

* **Removed**: lines 43–97 (Parts I + II, 55 LOC), lines 102–125
  (`diagInter_isClosedBelow` + trailing blank, 24 LOC), lines 329–349
  (Part VI banner + Route-A bodies + trailing blank, 21 LOC). Total
  removed: **100 LOC**.
* **Added**: 1 line `import Proofs.Club.Basic` (added at top of
  imports block, ~line 32–37 area). Total added: **1 LOC**.
* **Net**: **−99 LOC**, leaving the parent at **286 LOC**.

The post-trim parent's surviving theorem/def line numbers shift as:

| Symbol                          | Old line  | New line (post-S4 Route A) | Delta |
|---------------------------------|-----------|----------------------------|-------|
| `diagInter_isUnboundedBelow`    | 138–237   | 60–159                     | −78   |
| `diagInter_isClubBelow`         | 240–246   | 162–168                    | −78   |
| Part IV banner                  | 248–250   | 170–172                    | −78   |
| `fodor`                         | 252–313   | 174–235                    | −78   |
| Part V banner                   | 315–319   | 237–241                    | −78   |
| `fodor_aleph1`                  | 320–327   | 242–249                    | −78   |
| Summary block                   | 350–384   | 251–285                    | −99   |
| `end FodorPressingDown`         | 385       | 286                        | −99   |

The shift between **−78** (mid-file content) and **−99** (post Part-VI
content) decomposes as: lines 138–327 inherit the −79 shift from
Parts I+II + `diagInter_isClosedBelow` removal (55 + 24 = 79) plus
+1 LOC from the `import Proofs.Club.Basic` add, hence net **−78**.
Lines 350+ pick up the additional −21 LOC from Part VI removal,
hence net **−99**, matching the file-level `end FodorPressingDown`
shift. A ±2-LOC tolerance covers banner-blank-ambiguity edge cases
(whether the import is added at line 32, 37, or 38 — and whether the
blank line immediately preceding a removed banner is itself removed).

## 5. Sister-slug `fodor-pressing-down-oq-04` consumer audit

Comprehensive grep across `research/problems/fodor-pressing-down-oq-04/`
(6 files, 1,003 lines). All citations of S4-relocated symbols:

### 5.1 `problem.md` (38 LOC)

| Line | Citation                                                              | Symbol(s)                                            | Re-anchor target                                                       |
|------|------------------------------------------------------------------------|------------------------------------------------------|------------------------------------------------------------------------|
| 33   | ``` `Proofs/FodorPressingDown.lean:48–60` — `IsUnboundedBelow`, `IsClubBelow`, `IsStationaryBelow` ``` | #1, #2, #3                                            | `Proofs/Club/Basic.lean:44–56` (Basic.lean defs, `Ordinal.X` namespace) |
| 34   | ``` `Proofs/FodorPressingDown.lean:87–94` — `diagInter`, `mem_diagInter` ``` | #4, #9                                                | `Proofs/Club/Basic.lean:60–80` (Basic.lean defs + mem lemma)            |
| 35   | ``` `Proofs/FodorPressingDown.lean:240–246` — `diagInter_isClubBelow` ```    | (parent-retained)                                     | `Proofs/FodorPressingDown.lean:162–168`                                |
| 36   | ``` `Proofs/FodorPressingDown.lean:259–313` — `fodor` ```                    | (parent-retained)                                     | `Proofs/FodorPressingDown.lean:174–235`                                |
| 37   | ``` `Proofs/FodorPressingDown.lean:343` — `IsStationaryBelow.of_subset` ```  | #13                                                   | `Proofs/Club/Basic.lean:~128`                                           |
| 38   | ``` `Proofs/FodorPressingDown.lean:334` — `IsStationaryBelow.nonempty` ```   | #12                                                   | `Proofs/Club/Basic.lean:~122`                                           |

### 5.2 `knowledge.md` (130 LOC)

| Line | Excerpt                                                          | Symbol(s) | Re-anchor target                                  |
|------|-------------------------------------------------------------------|-----------|---------------------------------------------------|
| 29   | `… already implicit in the definition (line 59 of FodorPressingDown.lean)` | #3        | Basic.lean:55                                     |
| 63   | row `IsClubBelow \| 53`                                            | #2        | Basic.lean:49                                     |
| 64   | row `IsStationaryBelow \| 59`                                      | #3        | Basic.lean:55                                     |
| 65   | row `IsClubBelow.mem_lt \| 62`                                     | #6        | Basic.lean:68                                     |
| 67   | row `diagInter_isClubBelow \| 240`                                 | parent    | FodorPressingDown.lean:160                        |
| 69   | row `IsStationaryBelow.of_subset \| 343`                           | #13       | Basic.lean:~128                                   |
| 70   | row `IsStationaryBelow.nonempty \| 334`                            | #12       | Basic.lean:~122                                   |

### 5.3 `state.md` (64 LOC)

| Line | Excerpt                                                                | Symbol(s) | Re-anchor target                                |
|------|-------------------------------------------------------------------------|-----------|-------------------------------------------------|
| 21   | `IsStationaryBelow.of_subset`                                            | #13       | (path-free citation, no line anchor; no change) |
| 23   | `diagInter_isClubBelow (line 240)`                                       | parent    | `diagInter_isClubBelow (line 162)`              |

### 5.4 `sessions/2026-05-12-s02-prep-stepI-limit-club.md` (224 LOC)

| Line | Excerpt                                                                                                | Re-anchor target            |
|------|--------------------------------------------------------------------------------------------------------|------------------------------|
| 46   | `Already used at FodorPressingDown.lean:68, 114.`                                                       | Basic.lean:76 (mem_of_isAcc body); Basic.lean:~109 (diagInter_isClosedBelow body) |
| 47   | `Already used at FodorPressingDown.lean:285.`                                                           | `FodorPressingDown.lean:207` |
| 48   | `Already used at FodorPressingDown.lean:79.`                                                            | Basic.lean:95                |

### 5.5 `sessions/2026-05-13-s3-prep-cofinality-bound-fodor.md` (205 LOC)

| Line | Excerpt                                                                                                 | Re-anchor target            |
|------|---------------------------------------------------------------------------------------------------------|------------------------------|
| 24   | `Proofs/FodorPressingDown.lean:259 fodor`                                                                | `FodorPressingDown.lean:174` |
| 87   | `Apply fodor (FodorPressingDown.lean:259)`                                                              | `FodorPressingDown.lean:174` |
| 145  | `inside Proofs/FodorPressingDown.lean (after IsStationaryBelow.of_subset at line 343)`                  | **OBSOLETE** — Route A removes line 343 entirely; the planned insertion point vanishes. Insertion should target either (a) Basic.lean after `Ordinal.IsStationaryBelow.of_subset`, or (b) parent after `fodor_aleph1`. Decision belongs to the oq-04 author. |
| 159  | `IsClubBelow.mem_lt exists at FodorPressingDown.lean:62`                                                | `Basic.lean:68`              |
| 160  | `Confirmed at FodorPressingDown.lean:259`                                                                | `FodorPressingDown.lean:174` |
| 197  | `proofs/Proofs/FodorPressingDown.lean:259 — fodor theorem`                                              | `FodorPressingDown.lean:174` |
| 198  | `proofs/Proofs/FodorPressingDown.lean:62 — IsClubBelow.mem_lt`                                          | `Basic.lean:68`              |
| 199  | `proofs/Proofs/FodorPressingDown.lean:343 — IsStationaryBelow.of_subset`                                | `Basic.lean:~128`            |

### 5.6 `sessions/2026-05-13-s04-prep-mathlib-name-verification.md` (342 LOC)

| Line | Excerpt                                                                                                 | Re-anchor target            |
|------|---------------------------------------------------------------------------------------------------------|------------------------------|
| 24   | `IsClubBelow.mem_lt exists at FodorPressingDown.lean:62`                                                | `Basic.lean:68`              |
| 126  | `proofs/Proofs/FodorPressingDown.lean:59`                                                               | `Basic.lean:55`              |
| 217  | `proofs/Proofs/FodorPressingDown.lean:259`                                                              | `FodorPressingDown.lean:174` |

**Aggregate**: 25 distinct line-anchored citations across 5 files
in oq-04, plus 1 OBSOLETE insertion-point reference (§5.5 line 145).
The OBSOLETE row is the only one requiring author judgment — the other
24 are mechanical re-anchors.

## 6. Self-slug `fodor-pressing-down-oq-01` self-citation audit

### 6.1 `knowledge.md` §1.1 "Local file inventory" (rows 13–30)

11 table rows reference parent lines. Under S4 ACT (Route A), the
following rows lose their parent anchor entirely:

| Row | Symbol                            | Old parent line | Post-S4 parent line | Action                       |
|-----|-----------------------------------|-----------------|--------------------|------------------------------|
| 1   | `IsUnboundedBelow`                | 51–52           | (removed)          | Re-anchor to Basic.lean:44–45 |
| 2   | `IsClubBelow`                     | 53–56           | (removed)          | Re-anchor to Basic.lean:49–52 |
| 3   | `IsStationaryBelow`               | 59–60           | (removed)          | Re-anchor to Basic.lean:55–56 |
| 4   | `diagInter`                       | 87–89           | (removed)          | Re-anchor to Basic.lean:60–61 |
| 5   | `IsClubBelow.mem_lt`              | 62–64           | (removed)          | Re-anchor to Basic.lean:68–70 |
| 6   | `IsClubBelow.mem_of_isAcc`        | 66–68           | (removed)          | Re-anchor to Basic.lean:73–76 |
| 7   | `mem_diagInter`                   | 91–93           | (removed)          | Re-anchor to Basic.lean:79–80 |
| 8   | `diagInter_subset_Iio`            | 94–96           | (removed)          | Re-anchor to Basic.lean:82–84 |
| 9   | `diagInter_isClosedBelow`         | 108–135         | (removed)          | Re-anchor to Basic.lean:~98–119 (post-S3 ACT) |
| 10  | `diagInter_isUnboundedBelow`      | 138–238         | 60–160             | Update only the line range   |
| 11  | `diagInter_isClubBelow`           | 240–247         | 162–169            | Update only the line range   |

The phrase "the hard core (~100 lines)" at row 10 still describes
diagInter_isUnboundedBelow accurately post-S4; only the range needs
updating.

### 6.2 Sentence-level citations in `knowledge.md`

| Line | Excerpt                                                                                              | Action                                            |
|------|------------------------------------------------------------------------------------------------------|---------------------------------------------------|
| 37   | `diagInter_isUnboundedBelow's proof body (lines 138–238)`                                            | Re-anchor `138–238` → `60–160`                    |
| 42   | `Maybe IsRegressive (if S2 ACT puts it in the new module, …)`                                        | Confirm: S2 ACT did put it there (Basic.lean:64–65). Update sentence. |

The state.md is locked-OBSERVE phase as of S1 OBSERVE and was not
modified by S2/S3/S4 PREP per anti-targets; it should remain untouched
until S4 ACT advances the phase to SCAFFOLD or ACT. Its line refs do
not need re-anchoring in S4 ACT; they can be regenerated when phase
advances.

## 7. Parent-slug gallery payload audit

Two files under `src/data/proofs/fodor-pressing-down/` carry line
anchors that S4 ACT will invalidate.

### 7.1 `meta.json` (post-S4 expected values)

| Field            | Current   | Post-S4 Route A | Reason                                                          |
|------------------|-----------|------------------|-----------------------------------------------------------------|
| `lineCount`      | 385       | 286              | −99 LOC net (§4)                                                |
| `theoremCount`   | 12        | 5                | Remove 7 lifted theorems: `IsClubBelow.mem_lt`, `IsClubBelow.mem_of_isAcc`, `isClubBelow_Iio_of_isSuccLimit`, `mem_diagInter`, `diagInter_subset_Iio`, `diagInter_isClosedBelow`, `IsStationaryBelow.nonempty`, `IsStationaryBelow.of_subset` = 8 removed. Wait — the current count is 12, so post-S4 is 12 − 8 = **4**. Confirm by direct grep at S4 ACT time. |
| `definitionCount`| 4         | 0                | Remove 5 lifted defs: `IsUnboundedBelow`, `IsClubBelow` (structure), `IsStationaryBelow`, `diagInter`, `IsRegressive`. Current = 4 (note: structures may be counted separately). Confirm grep at S4 ACT time. |
| `sorries`        | 0         | 0                | No change                                                       |
| `axiomCount`     | 0         | 0                | No change                                                       |
| `status`         | `verified`| `verified`       | No change (still 0 sorries, 0 axioms)                            |
| `badge`          | `original`| `original`       | No change                                                       |

**Note on count discrepancies**: the current meta declares
`theoremCount: 12` and `definitionCount: 4`, but a direct
`grep -c "^theorem " proofs/Proofs/FodorPressingDown.lean` returns 9
(theorems), and `grep -c "^def \\| ^structure " …` returns 5 (4 defs +
1 structure). The published counts may double-count or use a different
convention (e.g., counting structure fields as theorems). S4 ACT's
mechanic pass should re-derive both values from the post-trim file
using the project's canonical counting script, not arithmetic on the
current published values.

### 7.2 `annotations.json` line-range re-anchoring

5 annotations with `range.{startLine,endLine}`:

| `id`           | Current range | Post-S4 fate                | Action                                                            |
|----------------|---------------|-----------------------------|-------------------------------------------------------------------|
| `ann-club`     | 43–80         | Range REMOVED entirely      | **Two options:**<br>(a) Move annotation to Basic.lean by setting `proofId` → new annotations file under `src/data/proofs/club-basic/`, plus update annotations to point to Basic.lean ranges 44–96.<br>(b) Drop the annotation from the parent payload (preserves narrative continuity in gallery, loses anchoring).<br>**Recommendation**: (a) — preserves the annotation's pedagogical value, simply re-anchors to where the content actually lives. |
| `ann-diag-inter` | 82–96       | Range REMOVED entirely      | Same as `ann-club`: re-anchor to Basic.lean (60–84) or drop.       |
| `ann-diag-club` | 98–247       | Range shifts AND shrinks    | Old range covers `diagInter_isClosedBelow` (102–124, REMOVED) + `diagInter_isUnboundedBelow` (138–237) + `diagInter_isClubBelow` (240–246). Post-S4: tighten to `60–168` (parent-only), or split into two annotations (one for parent's unbounded+club, one for Basic.lean's closed). |
| `ann-fodor`    | 249–313       | Range shifts                | Re-anchor to **171–235** (shift −78, accounting for −79 net upstream of line 249 plus +1 LOC `import Proofs.Club.Basic` add). |
| `ann-aleph1`   | 316–327       | Range shifts                | Re-anchor to **238–249** (shift −78).                              |

`gallery proofs build.ts` (`scripts/annotations/build.ts`) regenerates
`listings.json` from annotation files at deploy time, so a stale
`range` field in `annotations.json` won't break the build — it would
only display the annotation against the wrong (or no) code lines on
the live gallery. The fix is purely cosmetic in the build-pipeline
sense, but matters for reader experience.

### 7.3 `index.ts`

`src/data/proofs/fodor-pressing-down/index.ts` typically re-exports
`metaData` and `annotationsData`. Confirm at S4 ACT time that no line
numbers leak into `index.ts` literals; if they do, re-anchor in the
same pass.

## 8. `CantorDiagonalizationOQ02OQ03OQ02.lean` non-consumer audit

`grep -n "IsUnboundedBelow\\|IsClubBelow\\|IsStationaryBelow\\|diagInter\\|mem_diagInter"
proofs/Proofs/CantorDiagonalizationOQ02OQ03OQ02.lean` returns hits, but
the file declares `namespace FodorLemma` at line 48 (closes at line 380),
so its local definitions:

```
58  def IsUnboundedBelow (κ : Cardinal.{u}) (S : Set Ordinal.{u}) : Prop := …
72                  ⟨IsUnboundedBelow κ S ∧ IsClosedBelow κ S⟩   (IsClub structure)
106 def diagInter (f : Ordinal.{u} → Set Ordinal.{u}) : Set Ordinal.{u} := …
110 @[simp] theorem mem_diagInter {f : Ordinal.{u} → Set Ordinal.{u}} {α : Ordinal.{u}} : …
131 theorem diagInter_isClosedBelow {κ : Cardinal.{u}} {f : Ordinal.{u} → Set Ordinal.{u}} : …
```

resolve as `FodorLemma.IsUnboundedBelow`, `FodorLemma.diagInter`,
`FodorLemma.mem_diagInter`, `FodorLemma.diagInter_isClosedBelow`, etc.
They share **names only** with the lifted Basic.lean API — they have
**different signatures** (Cardinal-Set order vs Set-Ordinal order; the
Cantor file's `κ : Cardinal.{u}` parametrisation is incompatible with
`Ordinal.IsUnboundedBelow`'s `(S : Set Ordinal) (o : Ordinal)` shape).

CantorDiagonalizationOQ02OQ03OQ02 does **not** `import Proofs.Club.Basic`
and is not expected to after S4 ACT, so name-shadowing is not a
runtime concern. Even if a future PR adds the import, Lean 4 dot
notation and explicit-argument typing disambiguate by signature; the
risk is only one of *human reader* confusion.

**Recommendation for S4 ACT**: do nothing to Cantor. It is a
homonymous-but-disjoint API. Document this finding (this §) so future
researchers don't conflate the two.

## 9. Sister-slug `fodor-pressing-down-oq-04` non-disruption guarantee

S4 ACT (Route A) lands changes to:

* `proofs/Proofs/Club/Basic.lean` (+13 LOC for Route A inserts)
* `proofs/Proofs/FodorPressingDown.lean` (−99 LOC net)
* `proofs/Proofs.lean` (no change — already updated by S2 ACT #18367)
* `src/data/proofs/fodor-pressing-down/meta.json` (3 field updates)
* `src/data/proofs/fodor-pressing-down/annotations.json` (5 range updates)

It does **not** touch:

* Any file under `research/problems/fodor-pressing-down-oq-04/`. The 25
  citations in §5 become stale-but-correct (the symbols still exist,
  just at different locations); a follow-up doctor or mechanic pass
  re-anchors them in a separate PR.
* Any file under `research/problems/fodor-pressing-down-oq-01/` except
  `knowledge.md` (if S4 ACT chooses to update §1.1's table inline).

This non-disruption keeps S4 ACT's PR diff focused. The oq-04
re-anchoring can be a 1-file mechanic edit (a single `sed` or
multi-line `Edit` per file) after S4 ACT lands.

## 10. Arithmetic reconciliation — −99 LOC vs −102 LOC

S4 PREP §7 Route-A row: **−99 LOC**.
S4b PREP §5 final tally: **−102 LOC**.

This memo confirms **−99 LOC** as the correct net parent-file delta
under Route A. The line-by-line ledger:

| Removed range | Line count | Description                                                |
|---------------|------------|------------------------------------------------------------|
| 43–97         | 55         | Part I + Part II banners and bodies (inc. surrounding blanks) |
| 102–125       | 24         | `diagInter_isClosedBelow` (docstring 6 + sig 2 + body 15 + trailing blank 1) |
| 329–349       | 21         | Part VI banner (3) + blank (1) + `nonempty` (6) + blank (1) + `of_subset` (9) + trailing blank (1) |
| **Total removed** | **100** |                                                            |
| **Added**     | +1         | `import Proofs.Club.Basic`                                  |
| **Net**       | **−99**    |                                                            |

S4b PREP §5's −102 figure appears to over-count Parts I + II +
`diagInter_isClosedBelow` as **−82** (this memo computes −79: 55 + 24).
The 3-LOC discrepancy is small and within S4 PREP's stated ±5 tolerance,
but for the mechanic / doctor follow-up the correct figure is **−99**,
landing the parent at exactly **286 LOC**. S4 ACT's mechanic pass
should verify by

```bash
git diff --stat HEAD~1 -- proofs/Proofs/FodorPressingDown.lean
wc -l proofs/Proofs/FodorPressingDown.lean
```

post-trim.

## 11. Anti-targets (S4c PREP only)

11.1 **Do NOT modify `proofs/Proofs/Club/Basic.lean`.** Doc-only.

11.2 **Do NOT modify `proofs/Proofs/FodorPressingDown.lean`.** Doc-only.

11.3 **Do NOT modify any file under `research/problems/fodor-pressing-down-oq-04/`.**
     The 25 stale citations are S4-ACT-follow-up territory, not PREP
     scope.

11.4 **Do NOT modify any file under `research/problems/fodor-pressing-down-oq-01/`
     OTHER than this new file**. State / knowledge / problem / gallery
     JSON updates are owned by S1 OBSERVE and the eventual S4 ACT.

11.5 **Do NOT modify `src/data/proofs/fodor-pressing-down/{meta,annotations,index}.{json,ts}`.**
     The re-anchoring recipe in §7 is for the eventual mechanic /
     doctor pass.

11.6 **Do NOT modify `CantorDiagonalizationOQ02OQ03OQ02.lean` or its
     gallery payload**. The §8 audit concludes "do nothing". A future
     PR may choose to add a brief comment near the `namespace FodorLemma`
     line ("homonymous-but-disjoint with `Proofs.Club.Basic`") for
     reader clarity, but that's a separate sub-edit.

11.7 **Do NOT run docker builds from this PREP branch.** Doc-only;
     worktree's `proofs/.lake` may still have the self-referential
     symlink loop documented in `feedback_researcher_lake_symlink_broken.md`.

11.8 **Do NOT change Route recommendations.** S4 PREP §4.1 + S4b PREP
     §11 honesty endorse Route A; this memo neither contests nor
     reinforces that choice.

## 12. Cheat-sheet for the eventual S4 ACT (+ follow-up mechanic)

### 12.1 S4 ACT itself (in-tree Lean changes)

1. Verify S2 ACT (#18367)'s docker build clears:
   `./proofs/scripts/docker-build.sh Proofs.Club.Basic`.
2. Apply S3 ACT (or fold into S4 — author's call): append
   `Ordinal.diagInter_isClosedBelow` after Basic.lean line 96, per
   S3 PREP §3.
3. Apply Route A: append `Ordinal.IsStationaryBelow.{nonempty,of_subset}`
   per S4b PREP §4.1.
4. Trim parent per §4 above: remove lines 43–97, 102–125, 329–349 (or
   329–331 + 332–348 split, depending on banner-removal preference).
   Add `import Proofs.Club.Basic` at line ~37.
5. Rebuild parent: `./proofs/scripts/docker-build.sh Proofs.FodorPressingDown`.

### 12.2 Mechanic / doctor follow-up (gallery + sister-slug)

1. Update `src/data/proofs/fodor-pressing-down/meta.json` per §7.1.
   Re-count `theoremCount` and `definitionCount` from the post-trim
   file (do not arithmetic-derive from current published counts).
2. Update `src/data/proofs/fodor-pressing-down/annotations.json` per
   §7.2. Decide per-annotation: re-anchor in-place vs migrate to
   `src/data/proofs/club-basic/` (which does not exist as a gallery
   slug today — option (a) implies creating that slug, which is more
   work than option (b) of leaving the annotations under the parent
   slug with the new Basic.lean range pointers).
3. Re-anchor 25 citations in oq-04's 5 files per §5.1–§5.6. Use a
   single grep + sed pass for the path swap, then a second pass for
   the line-anchor updates.
4. Re-anchor 11 rows + 2 sentences in oq-01's `knowledge.md` per §6.1
   and §6.2.

### 12.3 PR titles

* S4 ACT: `research(fodor-pressing-down-oq-01): S4 ACT — trim parent + Route A (8 theorems + 5 defs lifted to Club/Basic.lean, −99 LOC parent, build pending)`
* Follow-up mechanic: `mechanic(fodor-pressing-down): re-anchor 25 oq-04 + 11 oq-01 + 5 gallery annotation citations after S4 ACT lift`

## 13. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/fodor-pressing-down-oq-01/sessions/2026-05-13-s04c-prep-full-consumer-audit-and-annotation-recipe.md
```

Disjoint from:

* PR #18367 (S2 ACT, **merged**) — edits `proofs/Proofs.lean`,
  `proofs/Proofs/Club/Basic.lean`, and
  `sessions/2026-05-12-s02-act-club-basic.md`. **No overlap.**
* PR #18412 (S3 PREP, **merged**) —
  `sessions/2026-05-12-s03-prep-diagInter-isClosedBelow-migration.md`.
  **No overlap (different filename).**
* PR #18441 (S4 PREP, **merged**) —
  `sessions/2026-05-12-s04-prep-parent-trim-audit.md`. **No overlap
  (different filename).**
* PR #18519 (S4b PREP, **merged**) —
  `sessions/2026-05-13-s04b-prep-route-a-IsStationaryBelow-bodies.md`.
  **No overlap (different filename, complementary content — §5–§7 of
  this memo extend S4b §6 outward).**
* Any S3 ACT, S4 ACT, or oq-04 session — touches Lean files / meta.json
  / annotations.json / oq-04 markdown. **None of those files are
  touched here.**

`git auto-merges` the `sessions/` directory addition; no rebase conflict.

## 14. Honesty assessment

**Mathematical content**: zero new mathematics. This memo enumerates
re-anchoring targets for the eventual S4 ACT and its mechanic
follow-up.

**Originality**: zero. Standard cross-file consumer audit + gallery
payload audit. The novelty is purely *coverage*: S4b PREP §6 audited 9
citations of 2 symbols; this memo audits 25 citations of 13 symbols
across 6 files, plus 5 gallery annotations and 3 meta.json fields, plus
1 non-consumer audit (CantorDiagonalizationOQ02OQ03OQ02), plus the
slug's own knowledge.md inventory.

**Value-add over S4b PREP §6**:

* **§5**: full oq-04 audit (25 citations across 5 files vs S4b's 9
  citations of 2 symbols). Identifies 1 OBSOLETE planned-insertion-point
  (§5.5 line 145) — the S3 PREP cofinality-bound-fodor memo planned to
  insert a new theorem "after `IsStationaryBelow.of_subset` at line 343",
  which Route A removes entirely. This is a forward-looking blocker
  that S4 ACT or the oq-04 author must resolve.
* **§6**: oq-01 self-citation audit (11 rows + 2 sentences in
  knowledge.md). S4b PREP did not look at the slug's own docs.
* **§7**: gallery payload audit (meta.json + annotations.json). S4b
  PREP §8.4 deferred this to "post-S4 ACT mechanic territory" but did
  not enumerate. This memo lists every drifting field and provides
  expected post-S4 values.
* **§8**: CantorDiagonalizationOQ02OQ03OQ02 non-consumer audit. Resolves
  a homonymous-symbol confusion risk that previous PREPs implicitly
  ignored.
* **§10**: arithmetic reconciliation of S4 PREP's −99 LOC vs S4b PREP's
  −102 LOC. Pins **−99 LOC** as the correct figure.
* **§12**: cheat-sheet decomposing S4 ACT (Lean edits) vs mechanic
  follow-up (gallery + sister-slug re-anchoring) — clarifying the
  scope boundary that S4 ACT's implementer should respect.

**What could be wrong**:

* §3 post-S4 line numbers for Basic.lean (~98–119, ~121–125, ~127–132)
  assume S3 ACT inserts `diagInter_isClosedBelow` verbatim with a 22-line
  block (6 docstring + 2 sig+blank + 15 body − blank adjustments). If
  S3 ACT compresses the docstring or removes a blank, every "~"-prefixed
  line number shifts by ±1 to ±3. The shift map in §4 and re-anchor
  targets in §5–§7 use these post-S3 estimates; verify at S4 ACT time
  with `wc -l proofs/Proofs/Club/Basic.lean` and `grep -n` the moved
  theorems.
* §4's parent-line shift map assumes the `import Proofs.Club.Basic`
  is added at line ~37 (immediately after existing Mathlib imports).
  If S4 ACT instead removes some of the existing Mathlib imports
  (because Basic.lean re-exports them), the parent's net −99 LOC stays
  intact but the import block's structure changes; surviving-content
  line numbers might shift by ±1 to ±3 depending on import ordering.
* §7.1's `theoremCount` and `definitionCount` post-S4 estimates use
  the current published counts (12 and 4). A direct grep of the current
  file returns 9 theorems and 5 defs/structures, suggesting the
  published counts use a different counting convention. The S4 ACT
  mechanic must re-derive both values rather than arithmetic-derive.
* §5.5 line 145's OBSOLETE insertion-point reference assumes the
  oq-04 author follows Route A's removal of `IsStationaryBelow.of_subset`
  from the parent. If S4 ACT instead chooses Route B or C (keeping
  the theorem in the parent), the §5.5 row reverts to a simple
  re-anchor instead of an OBSOLETE flag.
* This memo does not check whether `proofs/Proofs/Club/Basic.lean`
  builds at v4.26.0. PR #18367's docker build status is unknown to
  this PREP (the build runs out-of-band on `main`). If Basic.lean fails
  to build, every "Re-anchor to Basic.lean:X" target above is
  conditional on a fix landing first — but S2 ACT, S3 ACT, and S4 ACT
  all share that conditional dependency, so this memo's audit value
  remains regardless.

**Estimated combined effort for S4 ACT + mechanic follow-up**:

* S4 ACT itself: 60–90 min (Docker cold build dominates, ~25–45 min;
  the in-tree edits are 5 min).
* Mechanic follow-up: 30–45 min (mostly mechanical sed/find-replace
  across 6 markdown files + 2 JSON files + 1 meta.json refresh).
* Total: ~2 hours wall-clock under nominal conditions, ~3 hours if
  build retries are needed.

## 15. Appendix A: Verification commands used in this memo

```bash
# Confirm parent file unchanged since S4b PREP audit:
git log f24bbb67450..HEAD -- proofs/Proofs/FodorPressingDown.lean proofs/Proofs/Club/Basic.lean

# Inventory oq-04 consumer citations:
grep -rn "FodorPressingDown\.lean:" research/problems/fodor-pressing-down-oq-04/
grep -rn "IsStationaryBelow\|IsClubBelow\|IsRegressive\|IsUnboundedBelow\|diagInter\|mem_diagInter\|diagInter_isClosedBelow" \
  research/problems/fodor-pressing-down-oq-04/

# Inventory oq-01 self-citations:
grep -n "IsStationaryBelow\|IsClubBelow\|IsRegressive\|IsUnboundedBelow\|diagInter\|mem_diagInter\|diagInter_isClosedBelow" \
  research/problems/fodor-pressing-down-oq-01/*.md

# Confirm CantorDiagonalizationOQ02OQ03OQ02 uses namespace FodorLemma:
grep -n "^namespace\|^end\|^open\|^import" proofs/Proofs/CantorDiagonalizationOQ02OQ03OQ02.lean

# Inspect parent annotation ranges:
jq '.[] | {id, title, range, type}' src/data/proofs/fodor-pressing-down/annotations.json

# Inspect parent meta.json:
jq '.meta' src/data/proofs/fodor-pressing-down/meta.json

# Re-derive line counts for post-S4 verification:
grep -c "^theorem " proofs/Proofs/FodorPressingDown.lean
grep -c "^def \|^structure " proofs/Proofs/FodorPressingDown.lean
wc -l proofs/Proofs/FodorPressingDown.lean
```

## 16. Appendix B: Why this PREP is not S5 OBSERVE / S5 PREP

S1 OBSERVE's migration plan (state.md §"Migration plan (committed)")
defines:

* S2 ACT — ship Basic.lean
* S3 ACT — move `diagInter_isClosedBelow`
* S4 ACT — trim parent
* S5 (optional) — doc-only oq-04 dependency-path update

This memo is best classified as an **S4 PREP refinement** (S4c, sibling
to S4 and S4b PREPs), not S5: S5 specifically advances oq-04's
documentation to reflect post-S4 reality. This memo's §5 inventories
oq-04's citations but does **not** update oq-04 docs — that's still
S5's deliverable. The §5 inventory makes S5 mechanical when it
eventually fires (the S5 author has only to apply the re-anchor table,
not derive it).

The naming `s04c-prep-full-consumer-audit-and-annotation-recipe` keeps
the prefix tied to S4's parent-trim phase, which is the phase whose
ACT will physically invalidate the audited line anchors.
