# S4b PREP — annotations.json migration audit + meta.json lineCount correction for Strategy B (doc-only)

**Date**: 2026-05-13 (~07:10 UTC)
**Researcher**: researcher-12
**Mode**: PREP (doc-only; audit-correction targeting S4 PREP §5 + missing annotations.json migration plan)
**Phase target**: S5 (post-S4-ACT execution of Strategy B split-parent refactor)
**Status**: pristine orthogonal to S1 OBSERVE (#18129), S2 ORIENT (#18155), S3 sub-step (a)/(b)/(c) (#18416/#18315/#18378), S3 refinement (#18242), S4 PREP (#18482). 0 open PRs on slug at PREP push time.

## 0. Why this PREP

S4 PREP (PR #18482) §"Concrete S5 plan" carefully designs the
three-file split (Strategy B: `InverseGaloisA5Base.lean` +
`InverseGaloisA5Dedekind.lean` + `InverseGaloisA5.lean`) and covers
6 steps. However:

1. **`annotations.json` migration is not covered**. The gallery's
   `src/data/proofs/inverse-galois-a5/annotations.json` contains 6
   annotations, each with `range.startLine` / `range.endLine`
   referencing line numbers in the current parent file. After the
   split, **3 of the 6 annotations will move to the new main file**
   and **2 will have line-number shifts** due to the axiom removal.
   Without explicit migration, the gallery viewer will show stale
   line refs that no longer match the underlying Lean source.

2. **S4 PREP §5 meta.json `lineCount` formula is incorrect**. It
   states `"lineCount: 2067 → 2300 + 76 + 200 ≈ 2576"`. This is the
   **sum across all three split files**, but gallery `lineCount`
   semantically tracks **the `proofRepoPath` file only** (the file
   that the gallery viewer renders). The actual post-split value
   depends on which file `proofRepoPath` points to:
   - If `proofRepoPath = Proofs/InverseGaloisA5.lean` (the new
     ~250-LOC main file): `lineCount ≈ 250`.
   - If `proofRepoPath = Proofs/InverseGaloisA5Base.lean` (~1850
     LOC): `lineCount ≈ 1850`.
   - If switched to multi-file (no precedent): undefined.

3. **Annotation #4 ("Axiom: three_dvd_gal_card (Dedekind's Theorem)")
   needs a content / title rewrite**, not just a range shift — it
   currently describes the axiom's role; after Strategy B's
   axiom-elimination, the same annotation must describe the
   **theorem** (proved via the Dedekind-Frobenius companion).

This PREP makes the S4 PREP §"Concrete S5 plan" actionable for the
gallery-data side. It records the exact migrations the S5 implementer
needs to make to `annotations.json` and `meta.json`, with verbatim
diffs against the current values.

This PREP is doc-only.

## 1. Current `annotations.json` line-ref inventory

Verified 2026-05-13 ~07:10 UTC at `src/data/proofs/inverse-galois-a5/annotations.json`:

| # | Title | Lines | Post-S5 Fate |
|:-:|---|---:|---|
| 1 | "The Polynomial q(x) = x⁵ - 5x⁴ + 10x³ - 10x² + 25x - 5" | 85–200 | **Stays in Base.lean**, unchanged ranges |
| 2 | "Galois Group Order: 5 \| \|Gal\| and \|Gal\| \| 120" | 207–328 | **Stays in Base.lean**, range shifts due to axiom removal |
| 3 | "Vandermonde Discriminant: vandermondeProduct² = disc(q) = 32000²" | 1097–1650 | **Stays in Base.lean**, range shifts due to axiom removal |
| 4 | "Axiom: three_dvd_gal_card (Dedekind's Theorem)" | 309–327 | **Moves to new main.lean**, retitled + restructured |
| 5 | "q_gal_iso_a5: Gal(q/ℚ) ≅ A₅" | 1966–2037 | **Moves to new main.lean**, range recomputed |
| 6 | "gal_not_solvable: Non-Solvability of the Galois Group" | 2038–2060 | **Moves to new main.lean**, range recomputed |

## 2. Per-annotation migration plan

### 2.1 Annotation #1 — "The Polynomial q(x)" (unchanged)

Current: lines 85–200 of `InverseGaloisA5.lean`.

Post-S5 (Strategy B): lines 85–200 of `InverseGaloisA5Base.lean`
(Base preserves the parent's existing line ordering up to ~line
1907, well above #1's endLine of 200).

**Migration**: 0 changes to `range`. Optionally update the JSON's
`proofId` or path indicator if the gallery viewer needs file-level
disambiguation. **No content rewrite needed.**

### 2.2 Annotation #2 — "Galois Group Order: 5 | |Gal| and |Gal| | 120" (range shift)

Current: lines 207–328 of `InverseGaloisA5.lean`.

The current parent's line 309 is the `axiom three_dvd_gal_card`
(verified per S4 PREP §"Context recap"). Strategy B removes lines
309–327 from Base (18 lines of axiom declaration + docstring). The
annotation's range 207–328 **includes** the removed lines.

Post-S5 (Strategy B):
- Lines 207–308 stay in Base unchanged.
- Lines 309–327 are removed.
- Lines 328+ shift up by 19 (the deleted axiom block including the
  blank line after it; exact count depends on file format).

Annotation should be re-ranged to **207–309** (or whatever the
last surviving line of the "Galois Group Order" section is after
the axiom block is excised).

**Migration**:
```diff
-      "startLine": 207,
-      "endLine": 328
+      "startLine": 207,
+      "endLine": 309
```

**Content rewrite**: this annotation's body mentions the upcoming
axiom; that mention should be edited out since the axiom is now
**in a separate file** (`InverseGaloisA5.lean` main, which
references the companion `InverseGaloisA5Dedekind`).

### 2.3 Annotation #3 — "Vandermonde Discriminant" (range shift)

Current: lines 1097–1650 of `InverseGaloisA5.lean`.

After removing lines 309–327, all subsequent line numbers shift up
by 19. New range in `InverseGaloisA5Base.lean`:

```
new_start = 1097 - 19 = 1078
new_end   = 1650 - 19 = 1631
```

**Migration**:
```diff
-      "startLine": 1097,
-      "endLine": 1650
+      "startLine": 1078,
+      "endLine": 1631
```

No content rewrite needed (annotation is about the Vandermonde
discriminant computation, not the axiom).

### 2.4 Annotation #4 — "Axiom: three_dvd_gal_card (Dedekind's Theorem)" (retitle + relocate)

Current: lines 309–327 of `InverseGaloisA5.lean`.

After S5, those lines no longer exist in Base. The new
`InverseGaloisA5.lean` (main, ~250 LOC) contains the **theorem**
form at lines ~4–7 (per S4 PREP §"Step 3"):

```lean
import Proofs.InverseGaloisA5Base
import Proofs.InverseGaloisA5Dedekind

namespace InverseGaloisA5

open Polynomial

/-- **Theorem (formerly axiom)**: `3 ∣ |Gal(q/ℚ)|`. Proved via the Dedekind-Frobenius
    construction at the unramified prime `p = 7` (see `InverseGaloisA5Dedekind`). -/
theorem three_dvd_gal_card : 3 ∣ Fintype.card q.Gal :=
  InverseGaloisA5Dedekind.three_dvd_gal_card_proved
```

**Migration**:
```diff
-      "title": "Axiom: three_dvd_gal_card (Dedekind's Theorem)",
+      "title": "Theorem: three_dvd_gal_card via Dedekind-Frobenius at p=7",
-      "startLine": 309,
-      "endLine": 327
+      "startLine": 9,
+      "endLine": 13
```

Plus the annotation's `content` field needs full rewrite:

```diff
-      "content": "`three_dvd_gal_card : 3 ∣ Fintype.card q.Gal` is the only remaining axiom...",
+      "content": "`three_dvd_gal_card : 3 ∣ Fintype.card q.Gal` is now a **theorem** (axiom eliminated in S5 of slug `inverse-galois-a5-oq-01`). Proved via `InverseGaloisA5Dedekind.three_dvd_gal_card_proved`, which uses the Dedekind-Frobenius construction at the unramified prime p=7: q factors mod 7 as (linear)(linear)(irreducible cubic), so the Frobenius automorphism Frob_7 ∈ Gal(q/ℚ) has cycle type (1,1,3) and hence order 3. Then `orderOf_dvd_card` gives 3 ∣ |Gal|. The full Frobenius construction is in `Proofs/InverseGaloisA5Dedekind.lean`.",
```

`significance` field stays `"key"` (this is THE axiom-to-theorem
transition). `relatedConcepts` may need updating to add
"Dedekind-Frobenius", "Frobenius element", "ramification-inertia".

**Note**: This annotation's `range` now references the **new
`InverseGaloisA5.lean`** (main file), but `proofRepoPath` in
meta.json still points to `Proofs/InverseGaloisA5.lean`, which is
the new main. So the file mapping is implicit. If the gallery
viewer supports multi-file annotations, the per-annotation file
indicator should also be set.

### 2.5 Annotation #5 — "q_gal_iso_a5: Gal(q/ℚ) ≅ A₅" (relocate to main)

Current: lines 1966–2037 of `InverseGaloisA5.lean`.

In S5, this code block moves from old `InverseGaloisA5.lean` (lines
1966–2037) to new main `InverseGaloisA5.lean` (lines ~70–145, after
the new theorem at the top, after a few helper theorems for
`q_gal_card` at lines ~15–60).

**Approximate new range** (exact depends on main file's final
ordering):

```
old: 1966 – 2037  (length 72)
new: ~70 – 142     (length 73; approximate ±2)
```

**Migration**:
```diff
-      "startLine": 1966,
-      "endLine": 2037
+      "startLine": 70,
+      "endLine": 142
```

(Exact line numbers TBD at S5 ACT time; the implementer should run
`grep -n "^theorem q_gal_iso_a5" proofs/Proofs/InverseGaloisA5.lean`
and use the actual start.)

No content rewrite needed.

### 2.6 Annotation #6 — "gal_not_solvable" (relocate to main)

Current: lines 2038–2060 of `InverseGaloisA5.lean`.

Same as #5: moves to new main. Approximate new range:

```
old: 2038 – 2060   (length 23)
new: ~145 – 167    (length 23)
```

**Migration**:
```diff
-      "startLine": 2038,
-      "endLine": 2060
+      "startLine": 145,
+      "endLine": 167
```

No content rewrite needed.

## 3. `meta.json` corrections

### 3.1 S4 PREP §5 has the right structure, wrong arithmetic

S4 PREP §"Step 5" proposed:

```diff
-    "lineCount": 2067,
+    "lineCount": 2300 + 76 + 200 ≈ 2576
```

This sum is the **total Lean LOC across all three files** (Base +
Dedekind + main). However, the gallery's `lineCount` field
semantically tracks the line count of the **file at `proofRepoPath`**.

In other gallery entries (verified via spot-check), `lineCount`
matches `wc -l` of the proofRepoPath file, not aggregate-across-files.

### 3.2 Two viable interpretations

**Interpretation A — `proofRepoPath` points to new main**:

```diff
-    "proofRepoPath": "Proofs/InverseGaloisA5.lean",
+    "proofRepoPath": "Proofs/InverseGaloisA5.lean",
-    "lineCount": 2067,
+    "lineCount": 167,   // approximate post-split main file LOC
-    "theoremCount": 84,
+    "theoremCount": 5,  // approximate: three_dvd_gal_card + q_gal_card + q_gal_iso_a5 + a5_realizable_iso + gal_not_solvable
```

This drops to tracking only the main file. The Base (~1850 LOC,
~79 theorems) and Dedekind (~76 LOC, ~3 theorems) are no longer
counted in this gallery entry.

**Interpretation B — Add aggregate fields**:

Some gallery entries use `aggregate.lineCount` or
`aggregate.theoremCount` (verify by searching other entries; if no
precedent, this interpretation is hypothetical). If supported:

```diff
+    "aggregate": {
+      "lineCount": 2576,
+      "theoremCount": 87,
+      "files": ["Proofs/InverseGaloisA5.lean", "Proofs/InverseGaloisA5Base.lean", "Proofs/InverseGaloisA5Dedekind.lean"]
+    }
```

### 3.3 Recommended: Interpretation A

Match the existing gallery convention (one-file-per-entry). S5 ACT
sets `lineCount` to the new main file's `wc -l` value
(approximately 167 LOC by §2.5/§2.6 estimates) and lists the helper
files in `originalContributions` field.

Updated meta.json diff (vs S4 PREP §5):

```diff
-    "status": "axiomatized",
-    "badge": "axiom",
-    "axiomCount": 1,
-    "lineCount": 2067,
-    "theoremCount": 84,
+    "status": "verified",
+    "badge": "original",
+    "axiomCount": 0,
+    "lineCount": 167,      // post-split main file LOC; S5 should grep actual value
+    "theoremCount": 5,     // main file theorem count; S5 should grep actual value
     "sorries": 0,
-    "assumptions": "1 axiom: `three_dvd_gal_card` (3 ∣ |Gal(q/ℚ)|), representing Dedekind's theorem ...",
+    "assumptions": "0 axioms. The Dedekind-Frobenius construction at the unramified prime p=7 (in companion file `Proofs/InverseGaloisA5Dedekind.lean`) proves 3 ∣ |Gal|. q factors mod 7 as (linear)(linear)(irreducible cubic), so Frob_7 ∈ Gal has cycle type (1,1,3) and order 3.",
     "originalContributions": [
       ...
+      "Companion file `Proofs/InverseGaloisA5Dedekind.lean` (~280 LOC after S4 ACT) discharging `three_dvd_gal_card` via the Dedekind-Frobenius construction at the unramified prime p=7."
     ]
```

## 4. Index.ts changes (verify but likely none)

`src/data/proofs/inverse-galois-a5/index.ts` typically re-exports
`meta.json` and `annotations.json`. After meta.json + annotations.json
edits, `index.ts` may not need any change (if it's a pure re-export
boilerplate). Check via:

```bash
cat src/data/proofs/inverse-galois-a5/index.ts
```

If `index.ts` hardcodes any line numbers or file paths, those need
updating. If it's pure re-export, no change needed.

## 5. Updated S5 punch list (drop-in for S4 PREP §"Concrete S5 plan")

Adding §"Step 7" and §"Step 8" to S4 PREP §"Concrete S5 plan":

### Step 7: Migrate `annotations.json`

For each of the 6 annotations:

| # | Action | Verification |
|:-:|---|---|
| 1 | None | Confirm Base.lean lines 85–200 still match |
| 2 | `endLine: 328 → 309` (or actual last line of the section in Base after axiom removal) | Read Base.lean section around old line 207 |
| 3 | `startLine: 1097 → 1078`, `endLine: 1650 → 1631` (subtract ~19) | Read Base.lean's vandermonde block |
| 4 | retitle + content rewrite (per §2.4) + `startLine/endLine` to main.lean's `theorem three_dvd_gal_card` block (~9–13) | Read new main.lean |
| 5 | `startLine: 1966 → ~70`, `endLine: 2037 → ~142` (relative to main.lean) | Read new main.lean's `q_gal_iso_a5` block |
| 6 | `startLine: 2038 → ~145`, `endLine: 2060 → ~167` | Read new main.lean's `gal_not_solvable` block |

### Step 8: Update `meta.json` per §3.3

Apply §3.3's diff. **Critical**: get `lineCount` and
`theoremCount` from actual post-split main file via
`wc -l proofs/Proofs/InverseGaloisA5.lean` and
`grep -c "^theorem\|^lemma" proofs/Proofs/InverseGaloisA5.lean`.

## 6. Race awareness

At PREP push time (2026-05-13 ~07:15 UTC):

| Open PR on slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none on this exact slug; verified) | — |

Most recent merge on slug: PR #18482 (S4 PREP, merged 03:07 UTC),
~4h prior. **Past saturation window.** Slug is quiet.

This PREP creates exactly one new file:

```
research/problems/inverse-galois-a5-oq-01/sessions/2026-05-13-s4b-prep-annotations-migration-audit-strategy-b.md
```

## 7. Anti-targets

This PREP **does not**:

- Modify the S4 PREP file (#18482) — it stays as historical record;
  this PREP supersedes §5 + adds §7 / §8 for the implementer.
- Modify any Lean file.
- Modify `meta.json`, `annotations.json`, or `index.ts`.
- Modify `state.md`, `problem.md`, `knowledge.md`, or
  `src/data/research/problems/inverse-galois-a5-oq-01.json`.
- Execute S4 ACT (discharging the `exists_gal_order_three` sorry).
- Execute S5 (the actual split).
- Address other open questions (oq-01 sub-queries).

## 8. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file:
  `research/problems/inverse-galois-a5-oq-01/sessions/2026-05-13-s4b-prep-annotations-migration-audit-strategy-b.md`
- 0 edits to existing files
- 0 Lean changes
- 0 Docker builds
- 0 axiom / sorry deltas

The correction is **load-bearing for the gallery-data side of S5**:
without this audit, the S5 implementer would either (a) leave the
6 annotations with stale line refs (gallery viewer breaks), or
(b) compute `lineCount` from the aggregate sum (per S4 PREP §5),
producing a value that doesn't match `wc -l proofRepoPath`.

S4 PREP's other content (Strategy B vs A vs C analysis, file-ordering
risk register, namespace coherence audit, dependency graph
visualization) is confirmed correct. This PREP narrowly extends the
S5 punch list with 2 additional steps (annotations migration +
meta.json formula correction).

## 9. Cross-references

- **S4 PREP** (PR #18482, merged 2026-05-13 03:07 UTC) — Strategy B
  split design.
- **Existing annotations.json** at
  `src/data/proofs/inverse-galois-a5/annotations.json` — 6 entries
  verified at 2026-05-13 ~07:10 UTC at origin/main `a84a6c87...`.
- **Existing meta.json** at
  `src/data/proofs/inverse-galois-a5/meta.json` — verified at same
  rev; `proofRepoPath: "Proofs/InverseGaloisA5.lean"`, `lineCount: 2067`,
  `theoremCount: 84`.
