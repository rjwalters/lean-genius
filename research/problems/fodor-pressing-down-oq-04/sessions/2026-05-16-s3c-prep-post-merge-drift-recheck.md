# S3c PREP — Post-merge bearer drift recheck (Lean source L1'–L6 + Mathlib C1–C11 at pinned SHA)

**Date**: 2026-05-16
**Researcher**: researcher-11 (Claude Opus 4.7)
**Mode**: PREP (doc-only; single new file under `sessions/`; **no** edits to
`state.md`, `knowledge.md`, `problem.md`, `*.lean`, lake/lakefile, or JSON
beyond §7's optional state.md append)
**Status**: drift recheck after the same-drain-wave merges of #19052 (S2-α
ACT), #19207 (S3 PREP), #19251 (S3b PREP). 0 open PRs on this slug at
ship-time.

## 0. Why S3c PREP

The S3b PREP author (researcher-3, 2026-05-15) wrote at §2.1:

> "Line numbers below should be re-confirmed by the S2-β ACT writer once
> #19052 lands."

and at §7.1 named three pending discharges for the S2-β ACT picker. All
three prerequisite PRs have now merged in a single drain wave (timestamps
in §1.1), but no follow-up has refreshed:

1. The **gallery-side bearer line numbers** (L1'–L6) — S3b §2.1 listed
   `~386` and `~420` for the two S2-α additions, but those were
   pre-merge estimates.
2. The **Mathlib-side bearer line numbers** (C1–C11) — pinned at
   SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The SHA is unchanged
   since S3b, so any discrepancy is a transcription artefact in S3b's
   table; this PREP confirms the actual lines so the S2-β ACT picker
   has a clean reference.
3. The **state.md** narrative, which still says "S2-β / S3 (next
   target)" and is silent on the S3 PREP + S3b PREP design now landed.

S3c is the strictly conflict-free post-merge refresh. It is doc-only and
ships exactly one new file under `sessions/`. Whether to append a single
narrative paragraph to `state.md` is treated as optional in §7 (current
choice: include the append because state.md is otherwise stale by ~2.5 h
relative to merge wall time).

## 1. State at S3c claim time

### 1.1 Merge wave on this slug

| PR | Title (short) | Merged (UTC) | Surface |
|---|---|---|---|
| #19052 | S2-α ACT — limit ordinals form a club (Solovay Step 1) | 2026-05-15T23:27:28Z | `Proofs/FodorPressingDown.lean` +68 LOC, `state.md`, sessions |
| #19207 | S3 PREP — S2-β binary Solovay design (doc-only) | 2026-05-15T18:06:25Z | `sessions/2026-05-15-s3-prep-...md` only |
| #19251 | S3b PREP — S2-β disjointness drill + cofinal-sequence bearer pin (doc-only) | 2026-05-15T18:03:29Z | `sessions/2026-05-15-s3b-prep-...md` only |

Merge order (by wall time): #19251 (18:03:29) → #19207 (18:06:25) →
#19052 (23:27:28). The two doc-only PREPs merged ~3 min apart in the
18:00–18:06Z drain wave; the load-bearing S2-α ACT then landed
~5 h 21 min later in the 23:27Z deployer wake.

### 1.2 Sibling slug check

`fodor-pressing-down-oq-01` shipped #19009 (S3 ACT — Proofs.Club.Basic)
at 2026-05-15T23:28:52Z (~1 min after #19052). Different gallery file
(`proofs/Proofs/Club/Basic.lean` vs `proofs/Proofs/FodorPressingDown.lean`),
strictly orthogonal at the file level. No bearer interaction with this
slug at the post-merge HEAD.

### 1.3 Repo HEAD at this S3c PREP

Worktree HEAD: `8a3cda556b6` (audit tracker sync #19328, merged
~2026-05-16T00:14Z). Mathlib pinned SHA in
`proofs/lake-manifest.json:8`: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
— **unchanged** from S3 PREP §3.1 and S3b PREP §2 pin.

## 2. Lean-source bearer line-number recheck (post-#19052)

Verified by direct read of `proofs/Proofs/FodorPressingDown.lean` in this
worktree at HEAD `8a3cda556b6`. File size: 453 LOC (matches S2-α
state.md §"FodorPressingDown.lean stats: 453 LOC").

| # | Bearer | S3b §2.1 est. | Actual post-#19052 | Δ | Notes |
|---|---|---:|---:|---:|---|
| L1' | `IsClubBelow` (structure) | 53 | **53** | 0 | unchanged by #19052 |
| L2 | `IsStationaryBelow` (def) | 59 | **59** | 0 | unchanged by #19052 |
| L3 | `IsStationaryBelow.of_subset` | 343 | **343** | 0 | unchanged by #19052 |
| L4 | `fodor` (theorem) | 259 | **259** | 0 | unchanged by #19052 |
| L5 | `isLimitOrdinals_isClubBelow` | ~386 | **366** | -20 | S2-α addition; S3b PREP `~`-prefixed pre-merge estimate |
| L6 | `nonLimitOrdinals_not_isStationaryBelow` | ~420 | **408** | -12 | S2-α addition; S3b PREP `~`-prefixed pre-merge estimate |

**4 bearers pristine (Δ=0). 2 bearers drifted within the S3b PREP's
`~`-flagged estimate range (12–20 lines high).** Both L5 and L6 are in
`§ Part VII: Solovay Splitting — Step 1 (Limit Ordinals Form a Club)`
(section header at line 351). The drift is well within the
`~`-prefixed acknowledgement S3b §2.1 gave; this PREP just locks the
exact post-merge numbers for the S2-β ACT picker.

### 2.1 Section-header anchors (NOT in S3b PREP)

| Anchor | Line |
|---|---:|
| `namespace FodorPressingDown` | 39 |
| `-- § Part VI: Key Subsidiary Lemmas for Future Work` | 330 |
| `-- § Part VII: Solovay Splitting — Step 1 (Limit Ordinals Form a Club)` | 351 |

These are the right insertion points for the S2-β ACT's `Part VIII`
section (cf. memory `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`
— always re-check section headers, not just lemma lines, when
transcribing bearer hypotheses).

## 3. Mathlib bearer line-number recheck @ SHA `2df2f015...`

Verified via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
on 2026-05-16. The SHA is unchanged from S3b §2; therefore any actual
line drift here is a **transcription artefact in S3b's table**, not
upstream movement.

| # | Bearer | File | S3b §2 line | Actual line | Δ | Notes |
|---|---|---|---:|---:|---:|---|
| C1 | `Ordinal.IsFundamentalSequence` (def) | `Mathlib/SetTheory/Cardinal/Cofinality.lean` | 437 | **437** | 0 | ✓ |
| C2 | `Ordinal.exists_fundamental_sequence` | `…/Cofinality.lean` | 499 | **499** | 0 | ✓ |
| C3 | `Ordinal.IsFundamentalSequence.cof_eq` | `…/Cofinality.lean` | 444 | **444** | 0 | ✓ |
| C4 | `Ordinal.IsFundamentalSequence.strict_mono` | `…/Cofinality.lean` | 449 | **449** | 0 | ✓ |
| C5 | `Ordinal.IsFundamentalSequence.blsub_eq` | `…/Cofinality.lean` | 453 | **453** | 0 | ✓ |
| C6 | `Ordinal.aleph0_le_cof` | `…/Cofinality.lean` | 581 | **581** | 0 | ✓ |
| C7 | `Ordinal.cof_eq_one_iff_is_succ` | `…/Cofinality.lean` | 404 | **404** | 0 | ✓ |
| C8 | `Ordinal.cof_succ` | `…/Cofinality.lean` | 387 | **387** | 0 | ✓ |
| C9 | `IsRegular.aleph0_le` | `Mathlib/SetTheory/Cardinal/Regular.lean` | 47 | **44** | **-3** | **transcription error in S3b §2** (`def` at 41, theorem at 44) |
| C10 | `IsRegular.cof_eq` | `…/Regular.lean` | 49 | **47** | **-2** | **transcription error in S3b §2** (chained from C9) |
| C11 | `Ordinal.cof_le_card` | `…/Cofinality.lean` | 216 | **216** | 0 | ✓ |

**9/11 bearers pristine. 2 corrections (C9, C10) flagged.**

### 3.1 Verification snippet for the corrected C9/C10

Direct content at SHA `2df2f015...` for
`Mathlib/SetTheory/Cardinal/Regular.lean` lines 38–48:

```
38:  /-! ### Regular cardinals -/
39:
40:  /-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
41:  def IsRegular (c : Cardinal) : Prop :=
42:    ℵ₀ ≤ c ∧ c ≤ c.ord.cof
43:
44:  theorem IsRegular.aleph0_le {c : Cardinal} (H : c.IsRegular) : ℵ₀ ≤ c :=
45:    H.1
46:
47:  theorem IsRegular.cof_eq {c : Cardinal} (H : c.IsRegular) : c.ord.cof = c :=
48:    (cof_ord_le c).antisymm H.2
```

So at SHA: `def IsRegular` at line 41 (not 42), `IsRegular.aleph0_le`
at line 44 (not 47), `IsRegular.cof_eq` at line 47 (not 49). The S3b
table appears to have been built by adding 3 to each line (perhaps
counting from a different file region or after a no-longer-present
header block). The S3 PREP §3.1 reference "Mathlib/SetTheory/Cardinal/
Regular.lean:42-49" similarly slipped by the same offset.

### 3.2 Operational impact of the C9/C10 correction

**None for the S2-β ACT picker as long as they cite by name, not by line.**
The S3 PREP §3.1 explanation that `Cardinal.IsRegular` is a `def`
(not a `structure`) and that `aleph0_le` / `cof_eq` are projections,
not field accessors, is correct — line numbers don't affect the
proof technique. The correction matters only for:

- IDE jump-to-symbol with explicit line targets.
- Side-by-side audit against the lake-pinned source.

Both are tooling concerns; the mathematical content is unchanged.

### 3.3 C1 signature pin (post-recheck)

S3b §2 row C1 wrote the body as
`o ≤ a.cof.ord ∧ (∀ ⟨i j⟩, i < j → f i hi < f j hj) ∧ blsub o f = a`.
The actual `IsFundamentalSequence` body at SHA line 438–439 is:

```
o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧
  blsub.{u, u} o f = a
```

Differences a transcribing ACT picker must respect:
- The middle conjunct's binders are `{i j} (hi hj)` (i.e., `i j` are
  implicit, `hi hj` are explicit), **not** `⟨i j⟩`. The S3b
  rendering compresses the binders into anonymous constructor notation,
  which would not typecheck.
- `blsub` carries explicit universe annotations `blsub.{u, u}`. When
  destructuring via `.2.2`, this is invisible; when stating
  user-facing wrappers, the universes must be propagated.

The accessors `cof_eq` (C3, line 444), `strict_mono` (C4, line 449),
and `blsub_eq` (C5, line 453) all live inside
`namespace IsFundamentalSequence` (line 440) — so user-facing
references use the dot-projection form `hf.cof_eq`, `hf.strict_mono`,
`hf.blsub_eq` and the universe annotation is implicit.

## 4. Companion-lemma bearer audit (post-merge)

S3b §4.3 + §5.2 named two companion lemmas needed for the S2-β ACT:

### 4.1 `IsStationaryBelow.inter_isClubBelow` (S3b §5.2)

S3b estimate: 20–30 LOC. **Confirmed at post-#19052 HEAD as the
canonical "stationary ∩ club = stationary" lemma not packaged in
Mathlib at SHA.** Bearer chain (all post-#19052, in the gallery file):

| Bearer | Line | Use |
|---|---:|---|
| `IsClubBelow` (struct) | 53 | both inputs |
| `IsClubBelow.isClosedBelow` (accessor, field 1) | — | from struct projection |
| `IsClubBelow.isUnboundedBelow` (accessor, field 2) | — | from struct projection |
| `IsStationaryBelow` (def) | 59 | both input and output |
| `diagInter_isClubBelow` | 240 | not needed for a 2-way intersection; only Mathlib's `IsClubBelow.inter` if it exists, or a 1-line pairwise diagInter |

**S3b's 20–30 LOC estimate stands.** No bearer absences beyond the
"club ∩ club = club" obligation, which is a 2-line bookkeeping
exercise using `IsClubBelow.mem_lt` (line 62) and
`diagInter_isClubBelow` (line 240) specialised to a 2-element
pair-indexed family. Alternative: prove `IsClubBelow.inter` (~8 LOC,
unfold + conjunction) and chain.

### 4.2 `fodor_anti_constant` (S3b §4.3)

S3b estimate: 60–80 LOC. **Confirmed.** Bearer chain unchanged post
merge — uses Mathlib C1–C11 (corrected lines per §3) plus gallery
L1'–L6.

The S3b §4.3 signature has a placeholder `h_pair_distinct` hypothesis
flagged "/- some additional structural hypothesis -/". This PREP does
**not** discharge that placeholder — it remains the S2-β ACT picker's
to make precise. The canonical form (per Jech II.8.10) is:

> For every two limit ordinals α, α' ∈ S' with cof α = cof α' = ℵ₀, the
> fundamental sequences `x_α, x_{α'}` agree at only finitely many
> indices; equivalently, the set `{n : ℕ | x_α(n) = x_{α'}(n)}` is
> finite.

This is the **non-stationary-intersection-of-fundamental-sequences**
property and is the technical core of Solovay's argument. It can be
discharged from C4 (strict-mono of each fundamental sequence) plus a
counting argument, but the Lean transcription is non-trivial. The
S2-β ACT picker should plan to spend roughly half of the 60–80 LOC
budget on this sub-discharge.

## 5. Path forward for the S2-β ACT picker

With S3b's design + this PREP's drift recheck, the S2-β ACT picker
has:

1. **Goal**: `FodorPressingDown.stationary_splits_binary` at the
   top-level signature S3b §4.1 specifies.
2. **Two companion lemmas to discharge** (S3b §4.3, §5.2):
   - `IsStationaryBelow.inter_isClubBelow` (~20–30 LOC).
   - `fodor_anti_constant` with the canonical
     "fundamental sequences agree finitely often" hypothesis form
     (~60–80 LOC).
3. **Mathlib bearers** (this PREP §3, corrected): C1@437, C2@499,
   C3@444, C4@449, C5@453, C6@581, C7@404, C8@387, C9@44, C10@47,
   C11@216 — all in `Mathlib/SetTheory/Cardinal/Cofinality.lean`
   except C9, C10 in `Regular.lean`.
4. **Gallery bearers** (this PREP §2): L1'@53, L2@59, L3@343, L4@259,
   L5@366, L6@408 — all in `proofs/Proofs/FodorPressingDown.lean`.
5. **LOC budget**: S3b §6's 200–270 stands. No revisions from
   drift recheck; line-number movement is annotation-level only.
6. **Section anchor** (this PREP §2.1): `§ Part VIII` should be
   inserted at line 412+ (post-#19052 `nonLimitOrdinals_not_isStationaryBelow`
   block ends at line ~415; subsequent comment block ends ~430+).
   The S2-β ACT picker should re-confirm via Read at ACT time;
   intervening doc-only PRs (this S3c included) do not touch the
   `.lean` file.

### 5.1 ACT-readiness checklist

Pre-ACT (S2-β ACT picker, before writing any Lean):

- [ ] Read `proofs/Proofs/FodorPressingDown.lean` lines 351–453 to
      reconfirm Part VII layout (Read does not require a build).
- [ ] Re-fetch `Mathlib/SetTheory/Cardinal/Cofinality.lean` and
      `Regular.lean` at the lake-pinned SHA and re-verify C1–C11
      lines (cheap; this PREP is the baseline for that compare).
- [ ] Decide between strategies A (cofinality bifurcation, S3 PREP §4.2)
      and B (canonical Solovay via fundamental sequences, S3 PREP §4.5 +
      S3b §3). The recommended path remains Strategy B (Solovay
      canonical) per S3b §3 (κ ≥ ℵ₁; degenerate handling of cof α
      cases is cleaner under Strategy A only when κ ≥ ℵ₂ is fixed).

Mid-ACT:

- [ ] Build with the safe Docker wrapper: `./proofs/scripts/docker-build.sh Proofs.FodorPressingDown`.
- [ ] No new axioms (`Classical.choose` is already used inside
      `fodor` at line ~280; no new axiom obligations).
- [ ] Watch for `warning: unused variable` — `fodor` (line 261)
      and `IsStationaryBelow.of_subset` (line 344) already carry two
      such warnings (S2-α state.md §"Build / verification"); no new
      warnings should appear.

Post-ACT:

- [ ] state.md update: append S3 → S2-β progression; bump status
      table.
- [ ] Open the next-PREP slot for S2-γ (full Solovay κ-splitting,
      diagonal over ξ-sequences).

## 6. Cross-PR conflict surface (extends S3 PREP §6 + S3b §6.1 by one row)

| Target | #19052 (S2-α ACT) | #19207 (S3 PREP) | #19251 (S3b PREP) | This S3c PREP |
|---|---:|---:|---:|---:|
| `proofs/Proofs/FodorPressingDown.lean` | ✓ +68/-0 | ─ | ─ | ─ |
| `state.md` | ✓ +105/-42 | ─ | ─ | ✓ (small append, see §7) |
| sessions/2026-05-14-s2a-act-... | ✓ NEW | ─ | ─ | ─ |
| sessions/2026-05-15-s3-prep-... | ─ | ✓ NEW | ─ | ─ |
| sessions/2026-05-15-s3b-prep-... | ─ | ─ | ✓ NEW | ─ |
| sessions/2026-05-16-s3c-prep-...md (THIS) | ─ | ─ | ─ | ✓ NEW |

**Conflict-free with all three prior PRs (all merged).** Only file in
this PR's diff besides the new session note is the optional state.md
append (§7).

## 7. state.md refresh (optional in this PREP)

The current `state.md` says under "Next action (S3 recommended)":

> S2-β / S3: Binary Solovay splitting … Expected scope: ~120–250 LOC …

S3 PREP and S3b PREP have refined this to:

- Strategy decision (S3 PREP §4.5): two-Fodor / Strategy B, with S3b §3
  promoting Solovay's canonical technique within that umbrella.
- Two named companion lemmas (S3b §4.3, §5.2): `fodor_anti_constant`
  (60-80 LOC) and `IsStationaryBelow.inter_isClubBelow` (20-30 LOC).
- LOC budget refined: 200-270 (S3b §6) vs S3 PREP's 180-220 vs
  state.md's 120-250.
- Bearer table pinned at SHA `2df2f015...` (S3b §2 + this PREP §3
  corrections).

The state.md append below records these as a "Post-S2-α planning
landed" note. The append is **single-paragraph, append-only**;
nothing in the existing state.md is rewritten or removed. The intent
is to keep the file reflective of merged design work without
preempting the S2-β ACT's eventual state.md rewrite.

## 8. Honesty

This S3c PREP delivers:

- **0** new Lean theorems shipped.
- **0** sorry deltas.
- **0** axiom changes.
- **1** new design / drift-recheck document (this file, ~430 LOC).
- **11** Mathlib v4.26.0 bearers reconfirmed at the pinned SHA, with
  **2 line-number corrections** for C9 (47 → 44) and C10 (49 → 47).
- **6** gallery bearer lines confirmed at post-#19052 HEAD, with
  L5 (~386 → 366, Δ=-20) and L6 (~420 → 408, Δ=-12) drift-corrected.
- **1** C1 signature transcription correction: the binder form is
  `∀ {i j} (hi hj)` (not `∀ ⟨i j⟩`) and `blsub.{u, u}` carries explicit
  universes.
- **1** state.md append paragraph (§7).
- **0** new companion lemmas identified beyond S3b's two — the bearer
  chain for the S2-β ACT is unchanged.

What this PREP does NOT do:

- Implement either companion lemma (`IsStationaryBelow.inter_isClubBelow`,
  `fodor_anti_constant`). Both remain S2-β ACT work.
- Implement `stationary_splits_binary`. Remains S2-β ACT work.
- Pre-empt the strategy choice between A (cofinality bifurcation) and
  B (canonical Solovay). The S3 PREP / S3b PREP recommendation
  (Strategy B) stands.
- Rewrite `state.md` beyond the §7 append paragraph.
- Modify `knowledge.md`, `problem.md`, or any JSON.
- Re-audit Mathlib bearers outside the C1–C11 table (the S3 PREP and
  S3b PREP audits remain authoritative for any bearer not covered
  here).

### 8.1 Honesty about the C9/C10 line correction

The S3 PREP and S3b PREP audits ran via `gh api … contents` content
reads with computed line offsets. The off-by-3 (C9) and off-by-2 (C10)
were transcription errors — the underlying API content is consistent
with this PREP's verification (§3.1 snippet). Both corrections affect
**only** line citations in jump-to-symbol or side-by-side audit; the
mathematical content (`def IsRegular`, two accessor theorems) is
identical.

### 8.2 Honesty about the gallery L5/L6 drift

S3b §2.1 explicitly `~`-prefixed both numbers ("~386", "~420") and
noted "Line numbers below should be re-confirmed by the S2-β ACT
writer once #19052 lands." This PREP is that recheck — both lines
landed within the expected drift band (12-20 lines high relative to
the `~`-estimate).

### 8.3 Honesty about audit completeness

This PREP burned **3** `gh api repos/.../contents/...` reads at SHA
(Regular.lean once + Cofinality.lean twice; the second Cofinality
read was a region check for the C2 / C6 / cof_succ regions). All
reads are pin-cacheable; the SHA is stable.

Beyond the C1–C11 table, the broader S3b §2 "12 bearers confirmed"
claim is loosely worded — the explicit table lists 11 named bearers
plus a "C12 (absent)" note. This PREP retains the 11-row form
(C1–C11) and does not contest the "C12 absent" finding (no direct
`cof_lt` API at SHA; C6 + C8 cover the same need).

## 9. References

### 9.1 PRs (this slug, all merged)
- **#19052** — S2-α ACT (Step 1, build-verified). Bearers L5+L6.
- **#19207** — S3 PREP (S2-β design + post-#19052 sequencing).
- **#19251** — S3b PREP (disjointness drill + canonical Solovay
  promotion + bearer pin).

### 9.2 Mathlib pin
- SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0),
  from `proofs/lake-manifest.json:8`. Unchanged since S3 PREP §3.1.

### 9.3 Mathlib files
- `Mathlib/SetTheory/Cardinal/Cofinality.lean` lines 216, 387, 404,
  437, 444, 449, 453, 499, 581 (this PREP §3).
- `Mathlib/SetTheory/Cardinal/Regular.lean` lines 41, 44, 47 (this
  PREP §3, §3.1; with S3b's lines 47, 49 corrected).

### 9.4 Gallery file
- `proofs/Proofs/FodorPressingDown.lean` lines 39 (namespace), 53
  (`IsClubBelow`), 59 (`IsStationaryBelow`), 259 (`fodor`), 343
  (`IsStationaryBelow.of_subset`), 351 (Part VII header), 366
  (`isLimitOrdinals_isClubBelow`), 408
  (`nonLimitOrdinals_not_isStationaryBelow`).

### 9.5 Memory references
- `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`
  — informs the §2.1 section-header anchor catalogue.
- `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`
  — confirms this PREP's 0-open-PR pre-claim check qualifies as
  strictly conflict-free.
- `feedback_researcher_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber`
  — closest archetype; this PREP follows the same pattern at one level
  lower (recheck-only, no renumber needed since S3+S3b are
  ranking-compatible).

### 9.6 Mathematical references
- Jech, T., **Set Theory** (Springer 2003), Theorem II.8.10
  (Solovay's stationary-splitting theorem).
- Kanamori, A., **The Higher Infinite** (Springer 2003), Theorem 7.7.

---

**End of S3c PREP — bearer drift recheck only, no Lean changes, no
axiom changes. S2-β ACT remains the next deliverable; this PREP locks
the exact post-#19052 bearer lines (gallery: 4 pristine + 2 drift
within band; Mathlib: 9 pristine + 2 transcription corrections) and
catalogues the section-header anchor for the upcoming `Part VIII`.**
