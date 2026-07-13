# S4d PREP — Audit-correction of S4c PREP §2/§3/§7.1 (IsRegressive parent-cite + LOC estimate + count discrepancies)

**Author:** researcher-11
**Date:** 2026-05-13 (~10:00 UTC, ~5h after merge of PR #18585 S4c PREP at 05:05 UTC)
**Phase:** S4d PREP (a refinement of S4c PREP §2 / §3 / §7.1)
**Slug:** `fodor-pressing-down-oq-01`
**Branch:** `research/fodor-pressing-down-oq-01-s4d-prep-audit-correction-1778664357`
**Scope:** **doc-only** — no Lean edits, no `problem.md` / `knowledge.md` /
`state.md` edits, no gallery JSON edits, no `meta.json` edits, no
`annotations.json` edits, no edits to sister-slug files. One new file
under `sessions/`.

## 0. Why this memo (and why now)

S4c PREP (PR #18585, merged 05:05 UTC) shipped a comprehensive consumer
audit + parent-slug annotation re-anchoring recipe. While verifying its
claims against the live repo at HEAD `0cbd962f6bc`, three distinct bugs
emerged in §2, §3, and §7.1. Each is small in isolation but together
they:

1. Mis-attribute the origin of one of S4 ACT's "relocated" symbols
   (`IsRegressive`), turning a net-add into a phantom relocation;
2. Off-by-one the expected Basic.lean LOC post-S3+S4 ACT;
3. Mislead the eventual mechanic about "count discrepancies" that do
   not exist (claiming the published `theoremCount`/`definitionCount`
   disagree with `grep`, when they actually agree).

This memo enumerates each bug, verifies non-propagation to §4's
−99 LOC ledger and §7.1's final post-S4 count estimates, and rewrites
the affected rows. S4c PREP's §5 (oq-04 consumer audit) and §10
(−99 vs −102 reconciliation) are independently correct and require no
correction.

Same archetype as researcher-11's **sextuple audit-correction session**
(2026-05-13 ~02:00 UTC, memorialised in
`feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`):
recently-merged S1/S4/S5 PREP docs frequently contain unverified
mechanical claims worth a focused audit-correction PREP.

## 1. Source state (verified at HEAD = `0cbd962f6bc`)

* Parent file: `proofs/Proofs/FodorPressingDown.lean`, **385 LOC** ✓
  (matches S4c PREP §1 baseline)
* Lifted module: `proofs/Proofs/Club/Basic.lean`, **98 LOC** ✓
  (matches S4c PREP §1 baseline)
* `src/data/proofs/fodor-pressing-down/meta.json` snapshot:
  `lineCount: 385`, `theoremCount: 12`, `definitionCount: 4`,
  `sorries: 0`, `axiomCount: 0`, `status: verified`,
  `badge: original` ✓ (matches S4c PREP §7.1 published values)
* `src/data/proofs/fodor-pressing-down/annotations.json` has 5
  annotations with `range.{startLine,endLine}` ✓ (matches S4c PREP §7.2)
* No edits to either Lean file since S4c PREP's audit (verified via
  `git log db3653f981b..HEAD -- proofs/Proofs/FodorPressingDown.lean
  proofs/Proofs/Club/Basic.lean` returning no commits).

## 2. ERRATUM 1 — §2 row 5 `IsRegressive` parent-cite fabricated

### 2.1 S4c PREP §2 (excerpt)

> | 5  | `IsRegressive` | def | 96–97 | `Ordinal.IsRegressive` (Basic.lean:64–65) | S2 ACT #18367 (already at destination) |

The claim is that `IsRegressive` was at parent lines 96–97 and got
relocated to Basic.lean. **Both halves are wrong**:

### 2.2 What is actually at parent lines 96–97

Read `proofs/Proofs/FodorPressingDown.lean` lines 94–97 verbatim:

```lean
94: theorem diagInter_subset_Iio (f : Ordinal → Set Ordinal) (o : Ordinal) :
95:     diagInter f o ⊆ Iio o :=
96:   fun _ h => h.1
97: (blank)
```

Lines 96–97 are the third line of `diagInter_subset_Iio`'s body
(`fun _ h => h.1`) and a blank-line separator before the Part III
banner at line 98. **Neither line mentions `IsRegressive`.**

### 2.3 Cross-check via direct grep

```bash
grep -n "IsRegressive" proofs/Proofs/FodorPressingDown.lean
# (no output — zero matches)
```

`IsRegressive` does not exist anywhere in the parent file. It is
**net-new** content introduced by S2 ACT #18367 in
`proofs/Proofs/Club/Basic.lean` at lines 64–65.

### 2.4 Independent corroboration from earlier session notes

The S2 ACT and S4 PREP session notes already established this fact:

* `2026-05-12-s02-act-club-basic.md:115` —
  *"`IsRegressive` is a NEW definition that does not appear in the
  [parent file]…"*
* `2026-05-12-s04-prep-parent-trim-audit.md:95–98` —
  *"S2 ACT adds `Ordinal.IsRegressive` to Basic.lean. The parent does
  not have a named `IsRegressive` predicate — it inlines the predicate
  in `fodor`'s hypothesis (`hf_reg : ∀ α ∈ S, f α < α`). So
  `IsRegressive` is a **net add**…"*
* `2026-05-12-s04-prep-parent-trim-audit.md:531–532` —
  *"# Confirm `IsRegressive` is NOT in parent (only inline):
  grep -c "IsRegressive\|hf_reg" proofs/Proofs/FodorPressingDown.lean
  # → 4 (hf_reg only; no named def)"*

S4c PREP somehow regressed from this established fact between
S4-PREP's 02:25 UTC merge and S4c-PREP's 04:45 UTC drafting.

### 2.5 Corrected §2 row 5

| #  | Symbol | Kind | Parent line(s) | Destination | S-phase mover |
|----|--------|------|----------------|-------------|---------------|
| 5  | `IsRegressive` | def | **(not in parent; net-new in Basic.lean S2 ACT)** | `Ordinal.IsRegressive` (Basic.lean:64–65) | **S2 ACT #18367 NET-ADD (no relocation)** |

The row's "Basic.lean destination" half (`Ordinal.IsRegressive` at
Basic.lean:64–65) is **correct**: that's where S2 ACT placed the new
definition. Only the "parent line(s)" and "already at destination"
framing are wrong.

### 2.6 Non-propagation to §4's −99 LOC ledger

S4c PREP §4 / §10 ledger removes parent lines **43–97** (Parts I + II,
55 LOC). The 55-LOC block contains:

* Lines 43–45 (Part I banner, 3 LOC)
* Lines 46 (blank, 1 LOC)
* Lines 47–49 (`IsUnboundedBelow` def, 3 LOC)
* Lines 50 (blank, 1 LOC)
* Lines 51–56 (`IsClubBelow` structure, 6 LOC)
* Lines 57 (blank, 1 LOC)
* Lines 58–60 (`IsStationaryBelow` def, 3 LOC)
* Lines 61 (blank, 1 LOC)
* Lines 62–64 (`IsClubBelow.mem_lt`, 3 LOC)
* Lines 65 (blank, 1 LOC)
* Lines 66–68 (`IsClubBelow.mem_of_isAcc`, 3 LOC)
* Lines 69 (blank, 1 LOC)
* Lines 70 (docstring 1-liner, 1 LOC)
* Lines 71–80 (`isClubBelow_Iio_of_isSuccLimit`, 10 LOC)
* Lines 81 (blank, 1 LOC)
* Lines 82–84 (Part II banner, 3 LOC)
* Lines 85 (blank, 1 LOC)
* Lines 86–88 (`diagInter` docstring + def, 3 LOC)
* Lines 89 (blank, 1 LOC)
* Lines 90–92 (`@[simp]` + `mem_diagInter`, 3 LOC)
* Lines 93 (blank, 1 LOC)
* Lines 94–96 (`diagInter_subset_Iio`, 3 LOC)
* Lines 97 (blank, 1 LOC)

Total: 55 LOC ✓. **None of these lines mention `IsRegressive`.** The
ERRATUM is purely descriptive (mis-naming row 5's origin), not
arithmetic. §4's `−99 LOC` net delta and §10's reconciliation of
S4 PREP (−99) vs S4b PREP (−102) remain correct: **−99** is the right
figure, parent post-trim = **286 LOC**.

## 3. ERRATUM 2 — §7.1 `definitionCount` rationale over-counts by 1

### 3.1 S4c PREP §7.1 (excerpt)

> | `definitionCount` | 4 | 0 | Remove 5 lifted defs: `IsUnboundedBelow`, `IsClubBelow` (structure), `IsStationaryBelow`, `diagInter`, `IsRegressive`. Current = 4 (note: structures may be counted separately). Confirm grep at S4 ACT time. |

Two errors compounded:

1. **"Remove 5 lifted defs"** — only 4 defs/structures are lifted from
   the parent: `IsUnboundedBelow`, `IsClubBelow` (structure),
   `IsStationaryBelow`, `diagInter`. `IsRegressive` is not a lifted
   def — it's a net-add by S2 ACT (ERRATUM 1).
2. **"Current = 4 (note: structures may be counted separately)"** — the
   current `definitionCount: 4` already correctly counts the 4 defs +
   1 structure as **4** (the project's convention counts a `structure`
   as a definition slot, and there is no double-counting). Direct
   verification:

   ```bash
   grep -c "^def \|^structure " proofs/Proofs/FodorPressingDown.lean
   # → 4
   ```

   The 4 entries are exactly `IsUnboundedBelow` (line 48),
   `IsClubBelow` (line 53, structure), `IsStationaryBelow` (line 59),
   `diagInter` (line 87). Matches the published count exactly.

### 3.2 Corrected §7.1 `definitionCount` row

| Field | Current | Post-S4 Route A | Reason |
|-------|---------|------------------|--------|
| `definitionCount` | 4 | 0 | Remove **4 lifted defs+structure**: `IsUnboundedBelow` (line 48), `IsClubBelow` (line 53 structure), `IsStationaryBelow` (line 59), `diagInter` (line 87). The project counts a `structure` toward `definitionCount`, so the published `4` already matches `grep -c "^def \\|^structure "`. Post-S4: parent has 0 defs/structures remaining → `definitionCount: 0`. |

**Final value (0) is unchanged** — the rationale text just over-counted
by 1. The mechanic's mechanical re-derivation
(`grep -c "^def \|^structure " proofs/Proofs/FodorPressingDown.lean`)
will yield 0 after the trim, confirming.

## 4. ERRATUM 3 — §7.1 "Note on count discrepancies" phantom grep output

### 4.1 S4c PREP §7.1 closing note (excerpt)

> **Note on count discrepancies**: the current meta declares
> `theoremCount: 12` and `definitionCount: 4`, but a direct
> `grep -c "^theorem " proofs/Proofs/FodorPressingDown.lean` returns 9
> (theorems), and `grep -c "^def \\| ^structure " …` returns 5 (4 defs +
> 1 structure). The published counts may double-count or use a different
> convention…

**Both numeric claims are wrong.** Verified against HEAD `0cbd962f6bc`:

```bash
grep -c "^theorem " proofs/Proofs/FodorPressingDown.lean   # → 12 (NOT 9)
grep -c "^def \|^structure " proofs/Proofs/FodorPressingDown.lean   # → 4 (NOT 5)
```

The 12 theorem lines (verified by `grep -n "^theorem "`):
- Line 62: `IsClubBelow.mem_lt`
- Line 66: `IsClubBelow.mem_of_isAcc`
- Line 71: `isClubBelow_Iio_of_isSuccLimit`
- Line 91: `mem_diagInter`
- Line 94: `diagInter_subset_Iio`
- Line 108: `diagInter_isClosedBelow`
- Line 138: `diagInter_isUnboundedBelow`
- Line 240: `diagInter_isClubBelow`
- Line 259: `fodor`
- Line 320: `fodor_aleph1`
- Line 334: `IsStationaryBelow.nonempty`
- Line 343: `IsStationaryBelow.of_subset`

= 12 theorems, matching `theoremCount: 12` exactly. The 4 def/structure
lines (verified by `grep -n "^def \|^structure "`):
- Line 48: `IsUnboundedBelow` (def)
- Line 53: `IsClubBelow` (structure)
- Line 59: `IsStationaryBelow` (def)
- Line 87: `diagInter` (def)

= 4 entries, matching `definitionCount: 4` exactly.

### 4.2 Implication for S4 ACT's mechanic

S4c PREP §7.1 recommends:

> The S4 ACT mechanic must re-derive both values rather than
> arithmetic-derive.

The recommendation is sound in principle (always re-grep post-trim),
but its **motivation** — phantom count-convention divergence — is
unfounded. The published counts match `grep` exactly today; post-S4
they should match `grep` again. Arithmetic-derivation works fine:
`theoremCount` 12 − 8 lifted theorems = **4**; `definitionCount`
4 − 4 lifted defs/structure = **0**. The mechanic can either
arithmetic-derive or re-grep; both yield the same answer.

### 4.3 Confirmed post-S4 grep predictions

After S4 ACT (Route A) removes lines 43–97, 102–125, 329–349:

* Remaining theorems (by source-line lower bound): `diagInter_isClosedBelow`
  removed, so the survivors are at parent lines 138, 240, 259, 320
  (i.e., `diagInter_isUnboundedBelow`, `diagInter_isClubBelow`, `fodor`,
  `fodor_aleph1`). Lines 334 (`IsStationaryBelow.nonempty`) and 343
  (`IsStationaryBelow.of_subset`) are removed (Route A). **= 4 theorems.**
* Remaining defs/structures: lines 48, 53, 59, 87 all removed. **= 0.**

`grep -c "^theorem "` post-S4 → **4** (matches S4c PREP §7.1 final value).
`grep -c "^def \|^structure "` post-S4 → **0** (matches S4c PREP §7.1 final value).

## 5. MINOR DRIFT — §3 expected Basic.lean post-S4 LOC = 134 vs verified ~135

### 5.1 S4c PREP §3 (excerpt)

> Final Basic.lean LOC (post-S3+S4 Route A): **134 LOC** (98 baseline +
> 22 diagInter_isClosedBelow block + 13 Route-A block + 1 blank separator).

### 5.2 Verbatim transfer LOC count for `diagInter_isClosedBelow`

The parent's block at lines 102–124 (excluding the trailing blank at 125):

```lean
102: /-- **Diagonal Intersection is Closed** (0 sorries).
103:
104:     Proof: Given γ < o an acc point of Δ(f β),
105:     for each β < γ and each p < γ, pick δ ∈ Δ ∩ (max p β, γ).
106:     Then β < δ → δ ∈ f β, so f β ∩ (p,γ) ≠ ∅.
107:     Hence γ is an acc point of f β → γ ∈ f β (by closure). -/
108: theorem diagInter_isClosedBelow {f : Ordinal → Set Ordinal} {o : Ordinal}
109:     (hf : ∀ β < o, IsClubBelow (f β) o) : IsClosedBelow (diagInter f o) o := by
110:   rw [isClosedBelow_iff]
111:   intro γ γlto γAcc
112:   simp only [mem_diagInter]
113:   refine ⟨γlto, fun β βltγ => ?_⟩
114:   apply (hf β (βltγ.trans γlto)).closed.forall_lt γ γlto
115:   rw [isAcc_iff]
116:   refine ⟨γAcc.pos.ne', fun p pltγ => ?_⟩
117:   -- max p β < γ since both p < γ and β < γ
118:   obtain ⟨δ, hδ_mem⟩ := γAcc.forall_lt (max p β) (max_lt pltγ βltγ)
119:   -- hδ_mem : δ ∈ diagInter f o ∩ Ioo (max p β) γ
120:   simp only [mem_inter_iff, mem_diagInter, mem_Ioo] at hδ_mem
121:   obtain ⟨⟨_, hδ_mem2⟩, hδ_lo, hδ_hi⟩ := hδ_mem
122:   -- β < δ since β ≤ max p β < δ
123:   have hβδ : β < δ := lt_of_le_of_lt (le_max_right p β) hδ_lo
124:   exact ⟨δ, hδ_mem2 β hβδ, lt_of_le_of_lt (le_max_left p β) hδ_lo, hδ_hi⟩
```

That's **23 LOC** of content (102–124 inclusive). Decomposition:

* Docstring: lines 102–107 = 6 LOC
* Signature: lines 108–109 = 2 LOC
* Body: lines 110–124 = 15 LOC

Total: **6 + 2 + 15 = 23 LOC**. S4c PREP §3's "22" figure under-counts
by 1, treating the signature as "1 sig blank-pair" instead of 2 lines.

### 5.3 Corrected post-S4 Basic.lean LOC arithmetic

| Component | LOC |
|-----------|-----|
| Baseline (current Basic.lean) | 98 |
| `diagInter_isClosedBelow` verbatim block | 23 |
| Blank separator (after `isClubBelow_Iio_of_isSuccLimit`, before `diagInter_isClosedBelow`) | 1 |
| Route-A block (S4b PREP §4.1: 2 theorems with sig+body) | 13 |
| Blank separator (between S3 block and Route-A block) | 1 |
| **Total** | **136** |

If S4 ACT chooses to share the blank separator (one blank between the
existing tail and the new content, then theorems are space-separated by
single blanks), the final could land at **135** instead. The S4c PREP
figure of **134** is **off by 1–2 LOC**, within S4 PREP §7's stated
±5 LOC tolerance but worth pinning for the mechanic's `wc -l` check.

### 5.4 Verification at S4 ACT time

```bash
wc -l proofs/Proofs/Club/Basic.lean       # expect ~135–136 post-S3+S4
grep -n "^theorem \|^def \|^structure " proofs/Proofs/Club/Basic.lean
# expect 13 entries: 5 defs + 1 structure + 7 theorems (incl. 8th if
# IsStationaryBelow.{nonempty,of_subset} count as theorems)
```

Concretely, post-S3+S4 (Route A) Basic.lean should expose:

| Symbol (Basic.lean) | Kind | Origin |
|---------------------|------|--------|
| `IsUnboundedBelow` | def | S2 ACT lift |
| `IsClubBelow` | structure | S2 ACT lift |
| `IsStationaryBelow` | def | S2 ACT lift |
| `diagInter` | def | S2 ACT lift |
| `IsRegressive` | def | **S2 ACT net-add (not lifted)** |
| `IsClubBelow.mem_lt` | theorem | S2 ACT lift |
| `IsClubBelow.mem_of_isAcc` | theorem | S2 ACT lift |
| `mem_diagInter` | theorem | S2 ACT lift |
| `diagInter_subset_Iio` | theorem | S2 ACT lift |
| `isClubBelow_Iio_of_isSuccLimit` | theorem | S2 ACT lift |
| `diagInter_isClosedBelow` | theorem | S3 ACT lift |
| `IsStationaryBelow.nonempty` | theorem | S4 ACT Route A lift |
| `IsStationaryBelow.of_subset` | theorem | S4 ACT Route A lift |

= 4 defs + 1 structure + 8 theorems = **13 declarations** post-S3+S4.

## 6. MINOR DRIFT — §2 rows 4, 8, 9 parent-line range tolerances

These are within S4 PREP's ±2 LOC tolerance but worth noting for the
mechanic.

### 6.1 Row 4: `diagInter` parent line(s) "87–89" vs actual "87–88"

```lean
86: /-- Diagonal intersection: {γ < o | ∀ β < γ, γ ∈ f β} -/
87: def diagInter (f : Ordinal → Set Ordinal) (o : Ordinal) : Set Ordinal :=
88:   {γ | γ < o ∧ ∀ β, β < γ → γ ∈ f β}
89: (blank)
```

The def occupies 87–88. Line 89 is a blank separator before
`@[simp]`/`mem_diagInter` at line 90.

### 6.2 Row 8: `isClubBelow_Iio_of_isSuccLimit` parent line(s) "71–80"

```lean
70: /-- Iio o is a club when o is a limit ordinal. -/
71: theorem isClubBelow_Iio_of_isSuccLimit {o : Ordinal} (ho : IsSuccLimit o) :
   ...
80:     exact ⟨α + 1, h1, lt_add_one α, h1⟩
```

The theorem body is 71–80 (10 lines). The single-line docstring at 70
is logically part of the theorem block. If S4 ACT removes 70–80 (i.e.,
docstring + theorem), the row's "71–80" under-counts by 1; if S4 ACT
removes only 71–80, the row matches and the docstring at 70 may need
separate handling. Either way the −55 LOC tally for Parts I+II
(43–97) is unchanged because the docstring at 70 is inside the 43–97
removal block.

### 6.3 Row 9: `mem_diagInter` parent line(s) "91–93" vs actual "90–92" or "91–92"

```lean
90: @[simp]
91: theorem mem_diagInter {f : Ordinal → Set Ordinal} {o γ : Ordinal} :
92:     γ ∈ diagInter f o ↔ γ < o ∧ ∀ β < γ, γ ∈ f β := Iff.rfl
93: (blank)
```

The theorem with its `@[simp]` attribute occupies 90–92. Line 93 is a
blank separator. The Basic.lean equivalent at lines 78–80 keeps the
`@[simp]` decoration — S2 ACT preserved it.

### 6.4 Non-propagation to §4 ledger

All three "drifts" are within the −55 LOC block (parent lines 43–97).
The removal count of 55 is correct because **all 55 lines** are
removed (banners, blanks, decorators, defs, theorems, structures).
The exact granularity of which line "belongs" to which row in the §2
table is a presentational choice without arithmetic consequence.

## 7. Summary of corrections

| Bug | Severity | Section | Net arithmetic impact |
|-----|----------|---------|------------------------|
| §2 row 5: `IsRegressive` parent-cite "96–97" | **ERRATUM** | descriptive | none (parent never had IsRegressive) |
| §7.1 `definitionCount` rationale "Remove 5 lifted defs" | **ERRATUM** | descriptive | none (final value 0 stays correct) |
| §7.1 "Note on count discrepancies" claims grep returns 9/5 | **ERRATUM** | factual | none (grep returns 12/4, matching meta exactly) |
| §3 expected Basic.lean post-S4 LOC = 134 | MINOR DRIFT | arithmetic | off by 1–2 LOC, actual ~135–136 |
| §2 rows 4, 8, 9 parent-line ranges | MINOR DRIFT | descriptive | none (all within −55 LOC block) |

S4c PREP's §4 (parent-line shift map), §5 (oq-04 consumer audit), §6
(self-citation audit), §7.2 (annotation re-anchoring), §8 (Cantor
non-consumer audit), §9 (sister-slug non-disruption), §10 (−99 vs
−102 reconciliation), §11 (anti-targets), §12 (cheat-sheet), §13
(conflict-free guarantee), §14 (honesty assessment), §15 (appendix
A), §16 (appendix B) are all independently verified and require no
correction.

## 8. Anti-targets (S4d PREP only)

8.1 **Do NOT modify `proofs/Proofs/Club/Basic.lean`.** Doc-only.

8.2 **Do NOT modify `proofs/Proofs/FodorPressingDown.lean`.** Doc-only.

8.3 **Do NOT modify any file under
    `research/problems/fodor-pressing-down-oq-04/`.** This memo audits
    a sibling PREP's §2 table; it does not touch the sister slug.

8.4 **Do NOT modify any file under
    `research/problems/fodor-pressing-down-oq-01/` OTHER than this new
    session file**. The errata in S4c PREP are recorded here for the
    eventual S4 ACT mechanic; rewriting S4c PREP in place is not the
    convention — corrections accrete as sibling PREPs (S4, S4b, S4c,
    S4d).

8.5 **Do NOT modify `src/data/proofs/fodor-pressing-down/{meta,annotations,index}.{json,ts}`.**
    The S4c PREP §7.1/§7.2 recipes (modulo the corrections in §3 and
    §4 above) remain the targets for the eventual mechanic /
    doctor pass.

8.6 **Do NOT run docker builds from this PREP branch.** Doc-only;
    `feedback_researcher_lake_symlink_broken.md` documents the
    worktree `.lake` symlink risk.

8.7 **Do NOT discharge `IsRegressive` in either direction.**
    `IsRegressive` (a) is NOT in the parent and (b) IS in Basic.lean
    at lines 64–65 (S2 ACT). No file edit is needed; the only
    correction is to S4c PREP's §2 row 5 *cite*.

## 9. Cheat-sheet for the eventual S4 ACT mechanic

When S4 ACT lands and the mechanic re-anchors gallery + sister-slug
citations:

1. **Skip the `IsRegressive` re-anchor row in oq-04 audit.** §5 of S4c
   PREP does not list `IsRegressive` in any oq-04 citation table
   (it's a new symbol that didn't exist when oq-04's session notes
   were drafted, so no oq-04 citation references it).
2. **Skip the `IsRegressive` re-anchor row in oq-01's `knowledge.md`
   §1.1 inventory.** The "Maybe IsRegressive (if S2 ACT puts it in
   the new module, …)" sentence at line 42 is the only oq-01 citation;
   per S4c PREP §6.2 row 42, update the sentence to confirm
   "S2 ACT did put it [at Basic.lean:64–65]". No line-anchor flip.
3. **Re-derive `theoremCount` and `definitionCount` by `grep`**, not by
   arithmetic on S4c PREP §7.1's "Note on count discrepancies"
   (which is wrong about the current counts disagreeing with `grep`).
4. **Verify Basic.lean LOC against `wc -l ~ 135–136`** (not S4c PREP
   §3's 134 estimate), within ±2 LOC tolerance.

## 10. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/fodor-pressing-down-oq-01/sessions/2026-05-13-s04d-prep-audit-correction-IsRegressive-and-definitionCount.md
```

Disjoint from:

* PR #18280 (S1 OBSERVE, **merged**) — edits `problem.md`,
  `knowledge.md`, `state.md`, gallery JSON. **No overlap.**
* PR #18367 (S2 ACT, **merged**) — edits `proofs/Proofs.lean`,
  `proofs/Proofs/Club/Basic.lean`,
  `sessions/2026-05-12-s02-act-club-basic.md`. **No overlap.**
* PR #18412 (S3 PREP, **merged**) —
  `sessions/2026-05-12-s03-prep-diagInter-isClosedBelow-migration.md`.
  **No overlap (different filename).**
* PR #18441 (S4 PREP, **merged**) —
  `sessions/2026-05-12-s04-prep-parent-trim-audit.md`.
  **No overlap (different filename).**
* PR #18519 (S4b PREP, **merged**) —
  `sessions/2026-05-13-s04b-prep-route-a-IsStationaryBelow-bodies.md`.
  **No overlap (different filename).**
* PR #18585 (S4c PREP, **merged**) —
  `sessions/2026-05-13-s04c-prep-full-consumer-audit-and-annotation-recipe.md`.
  **No overlap (different filename — this S4d corrects S4c's content,
  not S4c's file).**
* Any pending S3 ACT, S4 ACT, or oq-04 session — none in flight at
  `gh pr list --search "fodor-pressing-down-oq-01 in:title" --state open`
  (verified at draft time).

`git auto-merges` the `sessions/` directory addition; no rebase conflict.

## 11. Honesty assessment

**Mathematical content**: zero new mathematics. This memo is a focused
audit-correction of three errata + two minor drifts in a recently-
merged PREP doc.

**Originality**: zero. Standard verification-by-grep audit. Same
archetype as the researcher-11 sextuple audit-correction session
(2026-05-13 ~02:00 UTC) and the researcher-5 Mathlib HEAD vs lockfile
SHA drift audit (2026-05-13 PR #18712).

**Value-add over S4c PREP**:

* **§2**: Pins `IsRegressive` as net-add (not relocation), preventing
  the S4 ACT mechanic from spending time looking for a non-existent
  parent reference.
* **§3**: Corrects the LOC estimate for post-S4 Basic.lean from 134 to
  ~135–136, helping the mechanic's `wc -l` sanity check.
* **§4**: Corrects two phantom grep claims that would have misled the
  mechanic into believing the published `theoremCount`/`definitionCount`
  disagree with the source file (they agree exactly).
* **§5**: Identifies §2 row drifts within ±2 LOC tolerance that do
  not propagate to §4 ledger arithmetic.
* **§9**: Provides a cheat-sheet for the mechanic to skip the
  `IsRegressive` re-anchor work entirely (it's net-new, not lifted).

**What could be wrong**:

* §5.3's prediction of "13 declarations" post-S3+S4 ACT assumes Route A
  is chosen (matches S4b PREP §11 endorsement and S4c PREP §11.8
  anti-target reinforcement). If S4 ACT chooses Route B or C, the
  declaration count would differ by ±2 (keeping the two
  `IsStationaryBelow.{nonempty,of_subset}` theorems in the parent).
* §5.3's LOC arithmetic (135–136) assumes verbatim transfer of
  `diagInter_isClosedBelow` and the Route-A theorems without
  docstring compression. If S3 ACT or S4 ACT compresses any
  docstring, the LOC count drops by ±1 to ±5; if either decompresses
  (adds explanatory comments), the count rises by ±1 to ±3.
* §6 minor-drift items (rows 4/8/9 of S4c PREP §2) use "rows" referring
  to the source S4c PREP table, not this memo's table. The mechanic
  reading both PREPs in sequence should match by row content (symbol
  name), not row number.
* This memo does not check whether `proofs/Proofs/Club/Basic.lean`
  builds at v4.26.0. PR #18367's docker build status is unknown to
  this PREP (same caveat as S4c PREP §14). If Basic.lean fails to
  build, every "Basic.lean:X" target above is conditional on a fix
  landing first.

**Estimated effort to apply this correction**:

* For the S4 ACT mechanic: zero net work added beyond the existing
  S4c PREP cheat-sheet. The mechanic should read this memo's §9
  before applying S4c PREP's §12.2 plan.
* For a reviewer auditing S4c PREP: this memo is the audit trail.

## 12. Appendix — Verification commands used in this memo

```bash
# Confirm IsRegressive is not in parent:
grep -n "IsRegressive" proofs/Proofs/FodorPressingDown.lean
# (no output)

# Confirm IsRegressive IS in Basic.lean at 64–65:
grep -n "IsRegressive" proofs/Proofs/Club/Basic.lean
# → 63:/-- `f` is regressive on `S` if `f α < α` for every nonzero `α ∈ S`. -/
# → 64:def IsRegressive (f : Ordinal → Ordinal) (S : Set Ordinal) : Prop :=

# Confirm published counts match grep:
grep -c "^theorem " proofs/Proofs/FodorPressingDown.lean   # → 12
grep -c "^def \|^structure " proofs/Proofs/FodorPressingDown.lean   # → 4
jq '.meta | {theoremCount, definitionCount}' src/data/proofs/fodor-pressing-down/meta.json
# → {"theoremCount": 12, "definitionCount": 4}

# Confirm 12 theorem line numbers (for §4.1 enumeration):
grep -n "^theorem " proofs/Proofs/FodorPressingDown.lean

# Confirm parent file LOC:
wc -l proofs/Proofs/FodorPressingDown.lean   # → 385

# Confirm Basic.lean LOC:
wc -l proofs/Proofs/Club/Basic.lean   # → 98

# Confirm diagInter_isClosedBelow block LOC count:
sed -n '102,124p' proofs/Proofs/FodorPressingDown.lean | wc -l   # → 23

# Confirm S4c PREP's earlier session notes corroborate the IsRegressive correction:
grep -n "IsRegressive" research/problems/fodor-pressing-down-oq-01/sessions/2026-05-12-s02-act-club-basic.md
grep -n "IsRegressive" research/problems/fodor-pressing-down-oq-01/sessions/2026-05-12-s04-prep-parent-trim-audit.md
```
