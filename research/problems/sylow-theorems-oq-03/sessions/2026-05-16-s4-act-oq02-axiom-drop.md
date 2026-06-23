# 2026-05-16 — S4 ACT: Realize deferred OQ-02 axiom drop (5 → 4)

**Author:** researcher-3
**Phase:** S4 ACT (Lean-modifying; bundles gallery-meta sync + research state-sync)
**Iteration:** 13 (12 prior + this S4 ACT)
**Trigger:** S3 STATE-SYNC (PR #19347, merged 2026-05-16T01:08:37Z) named §5a
"Realize the deferred OQ-02 axiom drop (5 → 4)" as the top-priority next action,
characterizing it as a mechanic-grade ~5-LOC follow-on with negligible risk and
1 Docker iteration. The pre-S4 state.md plus this slug's JSON
`currentState.nextAction` both flagged it. No open PRs for this slug at S4 open
(verified 2026-05-16T02:22Z via `gh pr list --search "sylow-theorems-oq-03
in:title" --state open --repo rjwalters/lean-genius --limit 50` returning `[]`).

**Strict conflict-free:** 1 Lean file (OQ-02 axiom block + #check removal), 1
Lean file (OQ-03 docstring §"Effect on SylowTheoremOQ02.lean" correction), 1
gallery meta.json (OQ-02 axiomCount 5→4 + lineCount + assumption text + section
metadata refresh), 3 research files (state.md header + JSON `currentState` +
this NEW session note). Strictly orthogonal to all other open work; the deleted
axiom has **0 callers** in `proofs/Proofs/` beyond OQ-02's own `#check` line
(verified by exhaustive `grep` — see § 2 below).

---

## § 1 — What this PR changes

### Lean edits

**`proofs/Proofs/SylowTheoremOQ02.lean`** (−10 LOC, 384 → 374):

1. Delete lines 132–140 (axiom block):
   ```lean
   /-- The image of a Sylow pro-p subgroup under a continuous surjective
       homomorphism to a finite group is a p-group. -/
   axiom sylowProP_projects_pgroup
       (hpf : IsProfiniteGroup G) (p : ℕ) (hp : Fact p.Prime)
       (P : SylowProP G p)
       (H : Type*) [Group H] [Fintype H]
       (φ : G →* H) (hφ_surj : Function.Surjective φ) :
       IsPGroup p (P.toSubgroup.map φ)
   ```
   plus the trailing blank line. The block was at line 132–140 (9 lines for the
   axiom + 1 trailing blank); the deletion preserves the blank line *before*
   the docstring of the next axiom (`sylowProP_inter_trivial`).

2. Delete the `#check @sylowProP_projects_pgroup` line from the trailing
   `#check` block.

**`proofs/Proofs/SylowTheoremOQ03.lean`** (docstring correction only, 0 Lean
delta):

The §"Effect on `SylowTheoremOQ02.lean`" subsection of the file's leading
docstring used to read:

> This file does not edit `SylowTheoremOQ02.lean`. The original axiom
> `sylowProP_projects_pgroup` remains in OQ-02 as a thin wrapper for
> backward compatibility (axiom count of OQ-02 unchanged: 5). A future
> iteration may delete the axiom […]

After S4 ACT this prose is stale (the axiom *is* deleted). The corrected
subsection reads:

> In S4 ACT (this file's companion edit), the original axiom
> `sylowProP_projects_pgroup` was deleted from `SylowTheoremOQ02.lean`
> along with its `#check` line in the sanity-check block. Net OQ-02
> axiom count: 5 → 4. No callers anywhere in `proofs/Proofs/` referenced
> the axiom by name beyond the `#check`, so removal is purely additive
> to the gallery's axiom-integrity ledger; the continuity-enhanced
> theorem `ProfiniteSylow.sylowProP_projects_pgroup_continuous` below
> is the new bearer of the projection result.

This is documentation-only — no code changes in OQ-03.

### Gallery meta.json edits (`src/data/proofs/sylow-theorems-oq-02/meta.json`)

| Field | Pre-S4 | Post-S4 |
|-------|--------|---------|
| `description` | "…5 axioms, 0 sorries, 10 proved theorems." | "…4 axioms, 0 sorries, 10 proved theorems." |
| `meta.axiomCount` | 5 | 4 |
| `meta.lineCount` | 393 | 374 |
| `meta.assumptions` | "5 axioms encoding…(4) projection…(5) trivial intersection…" | "4 axioms encoding…(4) trivial intersection… The original 5th axiom — projection of Sylow pro-p subgroups to p-groups in finite quotients — was discharged in sylow-theorems-oq-03 as the continuity-enhanced theorem ProfiniteSylow.sylowProP_projects_pgroup_continuous, with no surviving callers of the deleted axiom in proofs/Proofs/." |
| `sections[axioms]` startLine/endLine | 89 / 148 | 98 / 139 |
| `sections[axioms]` summary | "Five axioms encode…(4) projection…(5) trivial intersection" | "Four axioms encode…(4) trivial intersection. The original 5th axiom (…) was discharged in sylow-theorems-oq-03 (S2 ACT PR #19260 plus this S4 ACT axiom-drop) and removed from this file; the continuity-enhanced theorem ProfiniteSylow.sylowProP_projects_pgroup_continuous in SylowTheoremOQ03.lean is the new bearer of the projection result." |
| `sections[axioms]` mathContext | "These five results…" | "These four results…" |
| `sections[summary-and-checks]` summary | "5 axioms, 7 proved theorems…1 sorry, 7 proved theorems" | "4 axioms, 10 proved theorems…0 sorries, 10 proved theorems" |
| `sections[counting-and-summary]` summary / mathContext | "5 axioms and 10 proved theorems" / "Score: 5 axioms, 10 proved theorems, 0 sorries" | "4 axioms and 10 proved theorems" / "Score: 4 axioms, 10 proved theorems, 0 sorries" |
| `conclusion.summary` | "298-line formalization … 7 proved theorems, 5 axioms, 4 definitions, and 1 sorry" | "374-line formalization … 10 proved theorems, 4 axioms, 5 definitions, and 0 sorries" |
| `leanFile.axiomCount` | 5 | 4 |
| `leanFile.lineCount` | 393 | 374 |

The remaining sections (other section line ranges, prerequisites, references,
crossReferences) are preserved verbatim — those drifts predate S4 ACT and are
out of scope for this PR.

### Research state edits

- `research/problems/sylow-theorems-oq-03/state.md` — phase
  `ACT-MERGED` → `ACT-REALIZED` (5 → 4 axiom drop now reflected on disk);
  iteration 12 → 13; lastUpdate refresh; the S3 §5a deferred follow-on is
  marked **realized**, the prior `## S3 STATE-SYNC` body preserved verbatim,
  a new `## S4 ACT` subsection appended.
- `src/data/research/problems/sylow-theorems-oq-03.json` —
  `currentState.{phase, iteration, focus, nextAction, lastUpdate,
  attemptCounts.total/currentApproach}` refreshed,
  `knowledge.{builtItems, nextSteps}` updated (S3 §5a moved from nextSteps to
  builtItems; the OQ-02 axiom drop now appears in builtItems with the merged
  ACT PR number).
- `research/problems/sylow-theorems-oq-03/sessions/2026-05-16-s4-act-oq02-axiom-drop.md`
  — this file.

## § 2 — Why deletion is safe: caller audit

Pre-S4, the OQ-02 axiom name `sylowProP_projects_pgroup` appeared in
`proofs/Proofs/` at exactly these locations (verified at the worktree's
working state, `grep -n "sylowProP_projects_pgroup" proofs/Proofs/**/*.lean`):

| File | Line | Kind | Action in S4 |
|------|------|------|--------------|
| `SylowTheoremOQ02.lean` | 134 | `axiom` declaration | **deleted** |
| `SylowTheoremOQ02.lean` | 380 | `#check @sylowProP_projects_pgroup` | **deleted** |
| `SylowTheoremOQ03.lean` | 13 | docstring section header | unchanged |
| `SylowTheoremOQ03.lean` | 17 | docstring prose | unchanged |
| `SylowTheoremOQ03.lean` | 58 | docstring prose ("remains in OQ-02 as a thin wrapper") | **rewritten** (see §1) |
| `SylowTheoremOQ03.lean` | 62 | docstring prose | unchanged |
| `SylowTheoremOQ03.lean` | 123 | docstring prose | unchanged |
| `SylowTheoremOQ03.lean` | 135 | `theorem sylowProP_projects_pgroup_continuous` | unchanged — distinct name |
| `SylowTheoremOQ03.lean` | 162 | `#check @ProfiniteSylow.sylowProP_projects_pgroup_continuous` | unchanged — distinct name |

**No theorem, definition, or tactic anywhere in `proofs/Proofs/`** referenced
the deleted axiom (the `#check` is a sanity-checker, not a usage). The
`AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean` file imports
`Proofs.SylowTheoremOQ02` but only uses its concrete definitions
(`IsProfiniteGroup`, etc.), not this axiom (verified by `grep` on the axiom
name returning no hits in that file).

Therefore deletion is purely additive to the axiom-integrity ledger: 5 → 4
axioms, no broken proofs.

## § 3 — Mathlib pin recheck

`proofs/lake-manifest.json` mathlib `rev`:

```
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67   (inputRev: v4.26.0)
```

Identical SHA to S3 STATE-SYNC + PREP-7 + S2 ACT. No drift.

The 8 Mathlib bearers used by OQ-03's S2 ACT (`SylowTheoremOQ03.lean`) — the
file that holds the continuity-enhanced replacement theorem — were
pin-verified at this SHA by PR #19297 (PREP-7) and reconfirmed by S3
STATE-SYNC's §3 table. They remain authoritative; this S4 ACT does not touch
`SylowTheoremOQ03.lean`'s theorem body, so the bearer set is unchanged.

## § 4 — Axiom Integrity recheck (per CLAUDE.md policy)

```text
$ grep -cE "^axiom " proofs/Proofs/SylowTheoremOQ02.lean
4
$ grep -nE "^axiom " proofs/Proofs/SylowTheoremOQ02.lean
108:axiom sylowProP_existence
119:axiom sylowProP_conjugacy
126:axiom frattini_profinite
133:axiom sylowProP_inter_trivial
$ grep -cE "^axiom " proofs/Proofs/SylowTheoremOQ03.lean
0
$ grep -E "^structure |^class " proofs/Proofs/SylowTheoremOQ02.lean
class IsProP (G : Type*) [Group G] [TopologicalSpace G] (p : ℕ) extends …
structure SylowProP (G : Type*) [Group G] [TopologicalSpace G] (p : ℕ) extends …
```

`class IsProP` and `structure SylowProP` are *definitional* (no assumption
fields — `IsProP` extends `Subgroup.IsClosed` plus a `Prop`-valued
`p_power_index` field that is a *statement*, not an assumption; `SylowProP`
bundles a subgroup with `IsProPSubgroup` + maximality proofs, both
statements). Neither encodes an axiomatic assumption.

**Net OQ-02 contribution to gallery axiom budget:** 4 axioms / 0
structure-encoded hypotheses / 0 sorries.

**Net OQ-03 contribution:** 0 axioms / 0 structure-encoded hypotheses / 0
sorries (unchanged from S2 ACT).

## § 5 — Build verification

Docker build target `Proofs.SylowTheoremOQ03` (which transitively pulls
`Proofs.SylowTheoremOQ02` via the `import` statement at line 10 of OQ-03 and
which is the test-bed for any breakage in OQ-02). Mathlib cache hit at
v4.26.0; ~7727 files unpacked successfully on the first iteration. Build
result reported in the body of the PR (this session note is committed
post-build); the build log is preserved at
`.loom/logs/researcher-3-sylow-s4-build.log`.

## § 6 — Next-action decision tree (post-S4 ACT)

The S3 STATE-SYNC §5 decision tree had four branches: §5a (this PR), §5b
(Candidate B ACT), §5c (Mathlib upstream), §5d (frattini restatement).
Post-S4:

### 6a. Candidate B ACT — `sylowProP_inter_trivial` (now the new "TOP")

Discharge `axiom sylowProP_inter_trivial` at L133 of `SylowTheoremOQ02.lean`
(post-S4 line; was L142 pre-S4) using PREP-2 / PREP-4 / PREP-5 findings:
- `nhds_basis_clopen` (replaces phantom `closedSubgroup_eq_sInf_open` per
  PREP-4 Finding I)
- `IsTopologicalGroup` typeclass bridge per PREP-5

**Scope.** New file `proofs/Proofs/SylowTheoremOQ03B.lean` (~25 LOC).
**Risk.** Medium per PREP-2 — primarily build-side, as the typeclass-instance
bridge from PREP-5 is recorded but not yet exercised at v4.26.0 in a Lean
file.
**Build budget.** 1–3 Docker iterations.
**Net effect.** OQ-02 axiom count 4 → 3.

### 6b. Mathlib upstream contribution

Same as S3 §5c — out-of-band, route as a `mathlib4` PR if pursued.

### 6c. `frattini_profinite` axiom restatement

Same as S3 §5d — curator/architect scope, no researcher action.

### 6d. Stop

OQ-03 was designed to surgically discharge surgical axioms adjacent to a
completed sibling. Two of the three S1-candidates are now complete (A as the
S2 ACT theorem, A-axiom-drop as this S4 ACT). The third (B,
`sylowProP_inter_trivial`) is the only remaining narrow target. Once B
lands or is declared out of researcher scope, OQ-03 reaches a natural
stopping point with OQ-02 axiom count 3, 0 sorries, and only the two deep
inverse-limit axioms (existence, conjugacy) + the derivable `frattini`
remaining. The completed sibling can be flagged for an axiom-budget review.

## § 7 — Conflict-free guarantees

Files touched by this PR:

1. `proofs/Proofs/SylowTheoremOQ02.lean` — −10 LOC (axiom block + #check)
2. `proofs/Proofs/SylowTheoremOQ03.lean` — docstring §"Effect…" rewritten
   (0 Lean delta, ~9 line prose swap)
3. `src/data/proofs/sylow-theorems-oq-02/meta.json` — axiom/line counts,
   assumption text, section metadata, summary text
4. `research/problems/sylow-theorems-oq-03/state.md` — header refresh +
   `## S4 ACT` subsection appended; prior STATE-SYNC content preserved
5. `src/data/research/problems/sylow-theorems-oq-03.json` —
   `currentState` + `knowledge.{builtItems, nextSteps}` refresh
6. `research/problems/sylow-theorems-oq-03/sessions/2026-05-16-s4-act-oq02-axiom-drop.md`
   — this file (NEW)

**Not touched:**

- Any other slug's data, including OQ-02's `state.md` / problem.md /
  knowledge.md (no `research/problems/sylow-theorems-oq-02/` directory — the
  sibling slug is gallery-only).
- The OQ-03 file's theorem body or imports (only the docstring prose §
  "Effect on `SylowTheoremOQ02.lean`" is rewritten).
- Any other Lean file in `proofs/Proofs/` (audit confirmed no callers
  beyond the deleted `#check`).
- The lake manifest.

**Race awareness.** At S4 open: `gh pr list --search "sylow-theorems-oq-03
in:title" --state open --repo rjwalters/lean-genius --limit 50` returned
`[]` — 0 open PRs for this slug. No concurrency risk on slug files.
Sibling slug `sylow-theorems-oq-02` is `completed` (not in-progress); its
gallery meta.json edits target only the axiomCount / lineCount / text fields
that this ACT directly motivates and that the audit tracker would otherwise
flag as drift on the next pass.

---

**Net of this PR.** 6 files touched (2 Lean — 1 deletion + 1 docstring
correction; 4 docs). −10 Lean LOC. Realizes the OQ-03 advertised "5 → 4"
axiom drop on `sylow-theorems-oq-02` (now an integrity-true claim). Strictly
orthogonal to all other open work in the repo (0 sibling open PRs for OQ-03;
OQ-02 is `completed` and the gallery-meta sync follows directly from the
Lean delta).
