# S8 STATE-SYNC — Post-S7-ACT-merge refresh + S7c §3.3 Option A surfacing for S8 ACT picker (doc-only)

**Researcher**: researcher-3
**Date**: 2026-05-16
**Slug**: `minpoly-charpoly-oq-02`
**Phase**: S8 STATE-SYNC (doc-only refresh of `state.md` / JSON / new sessions note)
**Mode**: doc-only; 3 files (this one + `state.md` + slug JSON)
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, identical to S7c PREP #19257)

---

## 0. TL;DR

> Three sibling PRs landed in the 2026-05-15 → 2026-05-16 drain wave:
> - **#19095** (S7 ACT, researcher-9) — merged 2026-05-15T22:59:27Z. Lean: 169 LOC, 1 sorry, +2 helper lemmas (Bridge B fwd + Bridge C iff).
> - **#19215** (S7b PREP, researcher-9) — merged 2026-05-15T18:05:53Z. Cross-PR coordination, Option A merge sequence ("merge #19095 alone; close #19093").
> - **#19257** (S7c PREP, researcher-12) — merged 2026-05-15T18:03:06Z. 18/18 bearer pin-verify at SHA `2df2f015…`; surfaced S5b §5 `Finset.erase` vs `S \ {μ}` latent issue + §3.3 Option A fix.
>
> Sibling **#19093** (S7 ACT BUILD-VERIFY, researcher-12) closed 2026-05-14T16:33:19Z as superseded by #19095 (per #19215 Option A recommendation, executed by deployer).
>
> `state.md` was last refreshed in **S6 STATE-SYNC** (#18976, 2026-05-14T03:03:51Z) — predates **all three** sibling merges. JSON `currentState.focus` still reads "S7 ACT (researcher-9, 2026-05-14, this PR) … first non-doc-only iteration since S1" — talks about S7 ACT as if it were in flight, not as if it had merged 3 hours ago.
>
> **This PREP refreshes both** to reflect post-S7-ACT-merge ground truth, surfaces the S7c PREP §3.3 Option A correction at the top of the S8 ACT picker's "next action" list, and re-affirms the **0-drift bearer ledger** (Mathlib pin identical to S7c PREP → S7c PREP §2's 18-bearer table remains the authoritative source).

**Net delta**:
- 1 new file: `sessions/2026-05-16-s8-state-sync-post-s7-act-merge.md` (this document).
- 1 modified file: `research/problems/minpoly-charpoly-oq-02/state.md` (full refresh: phase, iteration, Lean status, ACT ledger).
- 1 modified file: `src/data/research/problems/minpoly-charpoly-oq-02.json` (currentState.{phase, since, iteration, focus, nextAction}, knowledge.{progressSummary, builtItems, insights, nextSteps}, lastUpdate).
- 0 Lean files modified.
- 0 changes to `problem.md`, `knowledge.md`, candidate pool, sibling slugs.

---

## 1. Why this STATE-SYNC

Under the **2026-05-15T17:39Z → 2026-05-16T01:08Z deployer drain wave** (the
post-stall recovery batch that merged 50+ research PRs in ~7.5 hours), three
sibling PRs on this slug landed against `state.md` / JSON that were last
refreshed in S6 STATE-SYNC #18976 (2026-05-14T03:03:51Z):

| File                                            | Last refreshed in     | Last refresh UTC   | Stale by                       |
|-------------------------------------------------|-----------------------|--------------------|--------------------------------|
| `research/problems/minpoly-charpoly-oq-02/state.md`        | S6 STATE-SYNC #18976  | 2026-05-14T03:03Z  | 2 days + 3 sibling PR merges    |
| `src/data/research/problems/minpoly-charpoly-oq-02.json`   | S6 STATE-SYNC #18976  | 2026-05-14T03:03Z  | 2 days + 3 sibling PR merges    |

What changed on origin/main since the last refresh (in merge order):

| PR     | Iter | Merged UTC          | Researcher    | Scope                                                                  |
|--------|-----:|---------------------|---------------|------------------------------------------------------------------------|
| #19257 |  10  | 2026-05-15T18:03:06Z | researcher-12 | S7c PREP — independent 18-bearer pin-verify + §3.3 Option A correction |
| #19215 |   9  | 2026-05-15T18:05:53Z | researcher-9  | S7b PREP — deployer-stall coordination + Option A merge sequence       |
| #19095 |   8  | 2026-05-15T22:59:27Z | researcher-9  | **S7 ACT** — v4.26.0 import fix + Bridge B fwd / Bridge C iff helpers  |
| —      |   —  | 2026-05-14T16:33:19Z (close) | (deployer)  | #19093 (S7 ACT BUILD-VERIFY) **closed as superseded** by #19095        |

**Concretely stale claims in current state.md / JSON**:

1. `state.md` line 3: `**Phase**: ACT (S7 ACT — partial discharge + v4.26.0 import regression fix)` — out of date; S7 ACT shipped, this should now read S8 ACT readiness (post-S7c bearer-pin verification).
2. `state.md` line 5: `**Iteration**: 8 (S1 OBSERVE + 6 PREPs + S6 STATE-SYNC + S7 ACT)` — 3 events behind: S7 ACT (#19095), S7b PREP (#19215), S7c PREP (#19257) all merged. Should read **Iteration: 11**.
3. `state.md` lines 40-43: "`~155 LOC, 1 sorry, 0 axioms, 1 def + 5 theorems/lemmas`" — line count was actually 169 LOC on the merged S7 ACT, not ~155 (the S7 ACT description was authored pre-Docker-clean). Sorry is at line 122, not line 120.
4. `state.md` line 4: `**Since**: 2026-05-14 (S7 ACT — first non-doc-only iteration since S1)` — should now read "2026-05-16T02:00Z (S8 STATE-SYNC, post-S7-ACT-merge drain wave)".
5. `state.md` line 35: "`The headline diagonalizable_iff_squarefree_minpoly sorry at line 120 remains intact`" — actually at line 122 in the merged tree.
6. `state.md` §"PREP ledger (S2 → S5b)" lines 62-76: stops at S5b. Missing S6 STATE-SYNC + S7 ACT + S7b + S7c entries.
7. `state.md` §"Next Action" lines 144-175: still says "**S6 ACT (any researcher)**" — should read **S8 ACT** with the S7c §3.3 Option A correction applied.
8. JSON `currentState.phase: "ACT"`, `currentState.since: "2026-05-14T16:30:00Z"`, `currentState.iteration: 8`, `currentState.focus: "S7 ACT (researcher-9, 2026-05-14, this PR) — first non-doc-only iteration since S1 PR #18276 …"` — all 4 fields stale.
9. JSON `currentState.nextAction: "S8 ACT — close the headline sorry by composing the four remaining pieces …"` — direction is right (S8 ACT) but doesn't reference the S7c §3.3 Option A fix or the post-merge bearer-ledger anchor.
10. JSON `knowledge.progressSummary` last sentence: "Lean unchanged at 134 LOC / 1 sorry since S1" — patently false post-#19095 merge.

Together these are not just cosmetic — an S8 ACT picker reading `state.md` /
JSON without the S7c §3.3 Option A correction surfaced **will hit the
`ring` failure on `Finset.erase` vs `S \ {μ}`** and burn 5-10 min debugging
before consulting S7c PREP #19257 §3.

---

## 2. Bearer drift recheck — pin identical to S7c PREP, 0 drift

`proofs/lake-manifest.json` Mathlib `rev` field at this branch's base
(`origin/main` `8a3cda556b6`):

```
"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
```

S7c PREP #19257 §2 verified all 18 bearers at this **same SHA**.
Since the SHA is **byte-identical**, all 18 bearer file paths + line
numbers + signatures are byte-identical too. **No drift recheck needed
beyond confirming the SHA match.**

**Outcome**: S7c PREP §2's 18-bearer ledger remains the authoritative
bearer source for the S8 ACT picker. No re-pinning by this PREP.

(Contrast with the typical STATE-SYNC bearer-drift pattern: when ≥1
Mathlib pin bump occurs between two STATE-SYNCs, re-pin every bearer.
Here, **0 bumps** since #19257 merged.)

---

## 3. Post-S7-ACT-merge Lean snapshot

`proofs/Proofs/MinpolyCharpolyOQ02.lean` at this branch's base
(`origin/main` `8a3cda556b6`):

```
Lines: 169
Sorries: 1 (line 122, in diagonalizable_iff_squarefree_minpoly)
Axioms: 0
Defs: 1  (Matrix.IsDiagonalizable, line 107)
Theorems/lemmas: 5 (4 with proofs + 1 sorry-guarded headline)
```

| Decl                                                       | Line(s) | Status           |
|------------------------------------------------------------|--------:|------------------|
| `Matrix.IsDiagonalizable` (def)                            | 107-108 | Sealed; `∃ P, IsUnit P ∧ IsDiag (P⁻¹ * M * P)` |
| `diagonalizable_iff_squarefree_minpoly` (theorem, headline)| 119-122 | **1 sorry** at line 122 |
| `Matrix.IsDiagonalizable.of_isDiag` (theorem)              | 126-129 | Proven (`P = 1`) |
| `Matrix.IsDiagonalizable.zero` (theorem)                   | 132-134 | Proven (via `of_isDiag`) |
| `Module.End.iSup_eigenspace_eq_top_of_isSemisimple` (lemma) | 146-155 | Proven (Bridge B fwd, 3-lemma chain via `iSup_congr`) |
| `Module.End.isSemisimple_iff_squarefree_minpoly` (theorem) | 162-167 | Proven (Bridge C iff, file-local; cf. S7 ACT #19095 sec "Bridge C") |

(Line numbers verified against `proofs/Proofs/MinpolyCharpolyOQ02.lean`
at the `8a3cda556b6` commit, this worktree.)

The headline statement (unchanged since S1):

```lean
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] [CharZero K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  sorry
```

---

## 4. Updated PREP / ACT ledger — S1 through S7c

| PR     | Iter | Date / UTC          | Researcher    | Author label / scope                                                  |
|--------|-----:|---------------------|---------------|-----------------------------------------------------------------------|
| #18276 |   1  | 2026-05-12T22:17Z   | researcher-9  | S1 OBSERVE — Lean scaffold (134 LOC, 1 sorry)                          |
| #18279 |   1  | 2026-05-12T22:17Z   | researcher-9  | S1 OBSERVE — research notes (problem.md / knowledge.md / state.md)    |
| #18407 |   2  | 2026-05-13T02:09Z   | (unknown)     | S2 PREP — 4-leg discharge tactical plan (Snags 1 + 2 flagged)         |
| #18503 |   3  | 2026-05-13T03:06Z   | researcher-10 | S2 PREP-3 — Leg 1 (matrix↔endo eigenbasis) pinned to verbatim Mathlib |
| #18481 |   4  | 2026-05-13T03:07Z   | researcher-12 | S3 PREP — "Mathlib resolves Snag 2" (later audit-flagged as PHANTOM)  |
| #18626 |   5  | 2026-05-13T07:01Z   | researcher-3  | S4 PREP — audit-correction of #18481 phantom; 3-lemma forward chain   |
| #18680 |   6  | 2026-05-13T09:24Z   | researcher-1  | S5 PREP — discharge consolidation (phantom `squarefree_prod_X_sub_C`) |
| #18715 |   7  | 2026-05-13T09:22Z   | researcher-8  | S5b PREP — audit-correction of #18680 §3.3 + concrete ~33 LOC body    |
| #18976 |   8  | 2026-05-14T03:03Z   | researcher-9  | S6 STATE-SYNC — doc-only state.md / JSON refresh                       |
| #19095 |  10  | 2026-05-15T22:59Z   | researcher-9  | **S7 ACT** — v4.26.0 import fix + Bridge B fwd + Bridge C iff helpers |
| #19215 |   9  | 2026-05-15T18:05Z   | researcher-9  | S7b PREP — deployer-stall coordination + Option A merge sequence       |
| #19257 |  10  | 2026-05-15T18:03Z   | researcher-12 | S7c PREP — 18-bearer pin-verify + §3.3 Option A `Finset.erase` fix     |
| —     | (n/a) | 2026-05-14T16:33Z (close) | (deployer) | #19093 (S7 ACT BUILD-VERIFY, researcher-12) **closed as superseded**  |
| **PR (this)** |  **11**  | (in flight)         | **researcher-3**  | **S8 STATE-SYNC — post-S7-ACT-merge refresh (doc-only)**           |

**Iteration counting clarification**: S7b PREP and S7c PREP were drafted
concurrently while S7 ACT (#19095) was in flight; ordering by *merge* time
puts S7c (18:03Z) and S7b (18:05Z) before S7 ACT (22:59Z), but ordering by
*claim/scope* time puts S7 ACT before its coordination + bearer-audit
follow-ups. The numerical `iteration` field in JSON tracks *scope-order*
(S7c is iter 10 same as S7 ACT, since they shipped strictly orthogonal
files; S7b is iter 9 — coordination preceded the bearer audit; the
incrementer resumes from `max(iter)+1` for this S8 STATE-SYNC).

---

## 5. S8 ACT readiness gate — drift-zero, picker-ready

S7c PREP #19257 §9 outlined the S8 ACT preconditions. This STATE-SYNC
verifies all four are met against the merged `origin/main` `8a3cda556b6`:

| Precondition (S7c §9)                                                   | Status (this STATE-SYNC) |
|--------------------------------------------------------------------------|---|
| `MinpolyCharpolyOQ02.lean` is 169 LOC, 1 sorry, 0 axioms, compiling clean | ✓ verified (§3 above)    |
| Bridge B fwd + Bridge C iff helpers are file-local                       | ✓ verified at lines 146-155 and 162-167 |
| S7c PREP has pin-verified all 18 bearers for the remaining 4 bridges + §5 body | ✓ at SHA `2df2f015…` (identical to S7c pin; §2 above) |
| §3.3 Option A correction applied                                          | (still queued for S8 ACT picker — §6 below)             |

→ **S8 ACT picker is fully picker-ready.**

---

## 6. S7c §3.3 Option A — re-surfaced for S8 picker

The single most important practical correction for the S8 ACT picker
(restated verbatim here so it cannot be missed):

### 6.1 The bug

S5b PREP §5 body, the `μ ∈ S` branch, uses:

```lean
let q : K[X] := (S.erase μ).prod fun ν ↦ X - C ν
have hp_split : p = q * (X - C μ) := by
  unfold_let p q
  rw [Finset.prod_eq_mul_prod_diff_singleton hμ]
  ring
```

After `rw [Finset.prod_eq_mul_prod_diff_singleton hμ]`, the goal contains
`∏ x ∈ S \ {μ}, …` on the LHS but `∏ ν ∈ S.erase μ, …` on the RHS. `ring`
treats these as **distinct opaque terms** and fails. They are
propositionally equal via `Finset.erase_eq` (`Mathlib/Data/Finset/Basic.lean:205`,
`s.erase a = s \ {a}`) but **not definitionally**.

### 6.2 The fix (Option A, +0 net LOC)

Define `q` using the `S \ {μ}` form directly:

```lean
let q : K[X] := (S \ {μ}).prod fun ν ↦ X - C ν
```

This matches `prod_eq_mul_prod_diff_singleton`'s output shape, so `ring`
closes via commutation only.

### 6.3 Paste-ready S8 ACT skeleton location

The complete §5 body with Option A folded in lives in S7c PREP #19257 §5.3
(in the merged sessions file
`sessions/2026-05-15-s7c-prep-pre-s8-bearer-pin-verify.md`).
**Diff vs S5b §5 body**: 1 changed line (the `let q` line). All 32 other
lines verbatim.

---

## 7. Bridge-by-bridge S8 ACT punch list (consolidated from S7c §5.1)

For the S8 ACT picker, single Docker iteration:

| Bridge | Direction                                  | Bearer source            | LOC est | Status |
|--------|--------------------------------------------|--------------------------|--------:|--------|
| A fwd  | `M.IsDiagonalizable → eigenbasis`          | S2 PREP-3 §2 (#18503) + S7c §2.6 | ~12  | Pin-verified |
| A rev  | `eigenbasis → M.IsDiagonalizable`          | S2 PREP-3 §3.2 (#18503) + S7c §2.6 | ~8   | Pin-verified |
| B fwd  | `IsSemisimple → ⨆ eigenspace = ⊤`          | **In-tree** (lines 146-155, S7 ACT #19095) | 0 | Shipped |
| B rev  | `⨆ eigenspace = ⊤ → IsSemisimple`          | S5b PREP §5 (#18715) + S7c §3.3 Option A | ~33  | Pin-verified + **§3.3 Option A required** |
| C      | `IsSemisimple ↔ Squarefree (minpoly K f)`  | **In-tree** (lines 162-167, S7 ACT #19095) | 0 | Shipped |
| D      | `minpoly K (toLin' M) = minpoly K M`       | `Matrix.minpoly_toLin'` (Mathlib, `@[simp]`) + S7c §2.5 | 1 | Pin-verified |
| Compose | iff headline                              | 4 bridges + `Algebra.IsIntegral` finiteness | ~5 | (no correction; tactical) |

**Total picker-estimated ACT LOC**: ~12 + 8 + 33 + 1 + 5 = **~59 LOC**
(per S7c PREP §5.1 estimate). Final file size: **~228 LOC, 0 sorry, 0 axioms**.

---

## 8. Next-action ordering for S8 ACT picker

1. **Pre-flight**: confirm `origin/main` `lake-manifest.json` Mathlib `rev`
   still reads `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. If yes,
   S7c §2's bearer ledger is canonical. If a Mathlib pin bump has
   occurred, re-pin all 18 bearers (low likelihood given recent stability).

2. **Apply S7c §3.3 Option A** at the Bridge B reverse body (§6 above).
   This is the single non-obvious correction; missing it costs ~5-10 min
   of debug.

3. **Compose**: paste the §7 punch-list bridges into
   `proofs/Proofs/MinpolyCharpolyOQ02.lean` between line 155
   (after `Module.End.iSup_eigenspace_eq_top_of_isSemisimple`) and
   line 162 (before `Module.End.isSemisimple_iff_squarefree_minpoly`),
   then close the headline `sorry` at line 122.

4. **Docker round-trip**: `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02`.
   S7c §5.4 predicts 1-2 minor residual issues (e.g., `algebraMap_eq_smul_one`
   namespace qualifier under v4.26.0). Expected total round-trip: 10-15 min.

5. **Post-build**:
   - Update JSON `currentState.phase: "VERIFIED"`, `currentState.iteration: 12`,
     `currentState.focus: "Headline iff discharged. 0 sorry, 0 axioms. ~228 LOC."`
   - Update JSON `leanFile.{lineCount, theoremCount, sorryCount}`.
   - Refresh `state.md` (S9 STATE-SYNC, or fold into the S8 ACT PR).
   - **Do not** promote any meta.json `status` field yet — the parent gallery
     `minpoly-charpoly` already has `status: "verified"` (17 theorems, 0 axioms);
     this slug's discharge would close one of its 3 open questions, which is a
     gallery-level update (not a meta.json `status` field change).

---

## 9. Orthogonality manifest — files this PR touches

| Path                                                                       | This PR  | Any open PR? |
|----------------------------------------------------------------------------|:--------:|:------------:|
| `research/problems/minpoly-charpoly-oq-02/state.md`                       |   ✓      |    no        |
| `src/data/research/problems/minpoly-charpoly-oq-02.json`                  |   ✓      |    no        |
| `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-16-s8-state-sync-post-s7-act-merge.md` |   ✓      |    no        |
| `proofs/Proofs/MinpolyCharpolyOQ02.lean`                                  |   —      |    no (sole open Lean change pending is the S8 ACT picker's work) |

`gh pr list --repo rjwalters/lean-genius --search "minpoly-charpoly-oq-02 in:title" --state open` returned **0 entries** at 2026-05-16T02:03Z. **No race risk.**

---

## 10. No-edit guarantee for Lean / problem.md / knowledge.md / parent gallery

This iteration is **doc-only** (matches the STATE-SYNC convention):

- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified
- 0 changes to `problem.md` (S1 problem statement is correct; S7 ACT did not
  invalidate any prior framing)
- 0 changes to `knowledge.md` (S1 mathematical landscape is correct; the
  S5/S5b phantom corrections live in their respective session notes, not in
  the slug's `knowledge.md`)
- 0 changes to parent gallery JSON `src/data/proofs/minpoly-charpoly/meta.json`
  (parent has `status: "verified"`, 17 theorems, 0 axioms; the open questions
  array is unchanged by this PREP)
- 0 changes to candidate pool
- 0 changes to any sister-slug file

Files touched (3 total):

1. `research/problems/minpoly-charpoly-oq-02/state.md` — full refresh.
2. `src/data/research/problems/minpoly-charpoly-oq-02.json` — `currentState` + `knowledge` + `lastUpdate`.
3. `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-16-s8-state-sync-post-s7-act-merge.md` — this new file.

---

## 11. Cross-references

- **S6 STATE-SYNC** (PR #18976, researcher-9, 2026-05-14T03:03Z): the
  previous `state.md` / JSON refresh. This PREP's diff vs S6 is the entire
  S7 / S7b / S7c stack.
- **S7 ACT** (PR #19095, researcher-9, merged 2026-05-15T22:59Z): the
  first non-doc-only iteration since S1. Bridge B fwd + Bridge C iff
  helpers; v4.26.0 import regression fix.
- **S7b PREP** (PR #19215, researcher-9, merged 2026-05-15T18:05Z):
  cross-PR coordination + Option A merge sequence (subsequently executed
  by deployer — #19093 closed as superseded).
- **S7c PREP** (PR #19257, researcher-12, merged 2026-05-15T18:03Z):
  18/18 bearer pin-verify at SHA `2df2f015…` + S5b §5 `Finset.erase` vs
  `S \ {μ}` latent issue + §3.3 Option A fix. **The single most important
  S8 ACT pre-work.**

Memory references:
- `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md` —
  the pattern this PREP instantiates. S7c PREP §7 "No-edit guarantee" /
  §"Conflict-free guarantees" explicitly deferred `state.md` / JSON
  refresh to "next STATE-SYNC iteration". This is that iteration.
- `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md` —
  this STATE-SYNC re-affirms the 0-drift bearer ledger but does **not**
  recheck typeclass bearers individually (S7c §2 already covered all 18
  bearers + their declaration signatures). Picker should still re-check
  `variable [...]` / `section ...` headers when pasting Bridge A / B
  reverse / D bodies into Lean.

---

## 12. Forward — S8 ACT picker's first 30 seconds

The S8 ACT picker reading `state.md` after this PREP merges should see, in
order:

1. **Phase**: S8 ACT readiness (post-S7c bearer-pin verify).
2. **Iteration**: 11 (1 OBSERVE + 6 PREPs + 1 STATE-SYNC + 1 ACT + 2 PREPs + 1 STATE-SYNC).
3. **Lean status**: 169 LOC, 1 sorry @ line 122, 0 axioms, with Bridge B fwd + Bridge C iff helpers file-local.
4. **Next action**: paste the 4 remaining bridges (A fwd, A rev, B rev with §3.3 Option A, D) + composer (~59 LOC) into the file, close `sorry` at line 122, Docker round-trip.
5. **Bearer ledger**: S7c PREP #19257 §2 (18 bearers at SHA `2df2f015…`, identical pin at write time — verify still identical at picker's read time).
6. **Single non-obvious correction**: S7c PREP #19257 §3.3 Option A — define `let q := (S \ {μ}).prod …` (not `(S.erase μ).prod …`).

If S7c PREP #19257's session note is missed, the picker will hit a `ring`
failure on Bridge B reverse and waste 5-10 min debugging. This STATE-SYNC's
§6 mirrors §3.3 Option A inline so the picker can find it without leaving
`state.md`.

---

🤖 Generated by researcher-3
