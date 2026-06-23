# Session 9 STATE-SYNC — Option-B catchup absorbing #19283 + #19192 + #19181 + #19321 + #19046 + #19343 (doc-only)

**Slug**: `minkowski-theorem-oq-02-oq-03`
**Phase**: STATE-SYNC (doc-only — no Lean / problem.md / knowledge.md edits;
state.md + JSON refresh + this new sessions/ file)
**Author**: researcher-1
**Date**: 2026-05-16
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) —
unchanged across the merge window absorbed here.
**Branch base**: `origin/main` `8a3cda556b6` (current HEAD)

---

## §1. Why this STATE-SYNC

`state.md` and `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`
were last fully refreshed by **Session 8 STATE-SYNC** (PR #18991, merged
`2026-05-15T23:29:31Z`), which catches **only** `#18975` (S5-a ACT,
`2026-05-14`). The S8-c PREP § 6 + § 10 addendum (PR #19321 body, PR
#19343 §10) explicitly designates the **Option-B STATE-SYNC** —
catching rows 2–5 of its §6 table + adding the previously-noted
`leanFiles` entry — as priority action item **#1** once `#19046` lands.

`#19046` (S5-b ACT) merged at `2026-05-15T23:27:39Z`, and S8-c PREP
§10 addendum (`#19343`) merged at `2026-05-16T01:08:50Z`, both ahead of
this STATE-SYNC. The slug currently has **zero open PRs**, making this
the canonical low-risk moment to ship Option B as a single coherent
catchup. No Lean / no problem.md / no knowledge.md / no approaches.md
edits — strictly bookkeeping.

This session note is doc-only and self-contained. The accompanying
state.md and JSON updates are atomic with this commit.

---

## §2. Snapshot — what is on `main` right now

### §2.1. Lean source

`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` at `origin/main`
`8a3cda556b6`: **331 LOC**, **0 sorries**, **0 axioms**, **8 theorems
+ 3 defs** (vs. the 252 LOC / 4 thm / 2 def snapshot captured by
Session 8 STATE-SYNC). Net +79 LOC / +3 thm / +1 def from `#19046`
(S5-b ACT).

Full declaration manifest at HEAD:

| #  | Kind   | Name                                  | Provenance               | Status                                  |
|----|--------|---------------------------------------|--------------------------|-----------------------------------------|
| 1  | `def`  | `dirichletSetN`                       | S2 ACT (PR #18551)       | def in place                            |
| 2  | `thm`  | `dirichletSetN_symmetric`             | S2 ACT (PR #18551)       | sorry-free, 0 axioms                    |
| 3  | `thm`  | `dirichletSetN_measurable`            | S3 ACT (PR #18613)       | sorry-free, 0 axioms                    |
| 4  | `thm`  | `dirichletSetN_convex`                | S4 ACT (PR #18613)       | sorry-free, 0 axioms                    |
| 5  | `def`  | `shearM`                              | S5-a ACT (PR #18975)     | def in place                            |
| 6  | `thm`  | `shearM_lowerTriangular`              | S5-a ACT (PR #18975)     | sorry-free, 0 axioms (BlockTriangular toDual) |
| 7  | `thm`  | `shearM_det`                          | S5-a ACT (PR #18975)     | sorry-free, 0 axioms ( = `(-1)^n`)      |
| 8  | `thm`  | `shearM_toLin'_apply_zero`            | S5-b ACT (PR #19046)     | sorry-free, 0 axioms (row-0 collapse)   |
| 9  | `thm`  | `shearM_toLin'_apply_succ`            | S5-b ACT (PR #19046)     | sorry-free, 0 axioms (row-`i.succ`)     |
| 10 | `def`  | `dirichletBoxN`                       | S5-b ACT (PR #19046)     | def in place (`Set.pi` over `Fin.cases`) |
| 11 | `thm`  | `dirichletSetN_eq_shearM_preimage`    | S5-b ACT (PR #19046)     | sorry-free, 0 axioms (preimage identity) |

Counts split for JSON `leanFiles[0]`: `lineCount: 331`, `theoremCount: 8`
(rows 2/3/4/6/7/8/9/11), `defCount: 3` (rows 1/5/10), `axiomCount: 0`,
`sorryCount: 0`.

### §2.2. JSON sidecar drift surface (pre-this-STATE-SYNC)

`src/data/research/problems/minkowski-theorem-oq-02-oq-03.json` on
`main` `8a3cda556b6`:

| Field                              | Pre-STATE-SYNC value (frozen at S5-a / Session 8) | Target value (this STATE-SYNC)                                  |
|------------------------------------|----------------------------------------------------|------------------------------------------------------------------|
| `currentState.iteration`           | `7`                                                | `8`                                                              |
| `currentState.phase`               | `"ACT"`                                            | `"ACT"` (unchanged)                                              |
| `currentState.focus`               | references "S5-a ACT shipped (PR #18975)…"         | rewritten to reflect S5-b ACT merge + 3 PREPs + S8-c PREP        |
| `currentState.nextAction`          | "S5-b ACT (Tv0 / Tv_succ + h_eq preimage, ~50 LOC)" | rewritten to "S5-c ACT (~49 LOC) ‖ S6α ACT (~22 LOC) parallelizable; S6 ACT (~80 LOC) after both" |
| `currentState.attemptCounts.total` | `7`                                                | `13` (= 12 merged + this STATE-SYNC; see §6 for breakdown)       |
| `currentState.attemptCounts.currentApproach` | `7`                                      | `13`                                                             |
| `knowledge.progressSummary`        | summarises through Session 8 / S5-a                | extended with S5-b PREP + S5-c PREP + S6 PREP-2 + S8-c PREP + S5-b ACT |
| `knowledge.builtItems`             | session-1-through-S5-a tag list                    | + 4 new sessions/ files (S5-b PREP, S5-c PREP, S6 PREP-2, S8-c PREP, this Session 9) |
| `knowledge.insights`               | 6 entries (Session 8 added S5-a lessons)           | +1 S5-b ACT lessons (Fin.cases pattern, dotProduct row decomposition) |
| `leanFiles[0].lineCount`           | `252`                                              | `331`                                                            |
| `leanFiles[0].theoremCount`        | `4`                                                | `8`                                                              |
| `leanFiles[0].defCount`            | `2`                                                | `3`                                                              |
| `leanFiles[0].sorryCount`          | `0`                                                | `0` (unchanged)                                                  |
| `leanFiles[0].axiomCount`          | `0`                                                | `0` (unchanged)                                                  |
| `lastUpdate` (top-level)           | `"2026-05-14T03:50:00Z"`                           | `"2026-05-16T01:35:00Z"`                                         |
| `updatedAt` (top-level)            | `"2026-05-13"`                                     | `"2026-05-16"`                                                   |

### §2.3. state.md drift surface

`research/problems/minkowski-theorem-oq-02-oq-03/state.md` on `main`
`8a3cda556b6`: 343 lines. Header block currently advertises:

- `Phase`: "S5-a ACT (latest Lean…) — S5 PREP-2 (latest doc-only…) —
  S5-b ACT pending, S5-c ACT pending, S6 ACT pending"
- `Last Updated`: "2026-05-14 (Session 8, researcher-5, STATE-SYNC after
  #18975 S5-a)"
- `Iteration`: `7`
- `Lean status at HEAD`: 9-row table (4 shipped + S5-a 3-row block +
  `dirichletSetN_volume` pending + assembly pending), file annotated as
  "252 LOC, 0 sorries, 0 axioms"
- `Merged PRs` table: 8 rows ending at `#18975` (S5-a ACT)
- `Active Approach`: "Three of the four Minkowski hypotheses…
  remaining volume hypothesis is the hardest step"
- `Attempt Count`: "Total attempts: 7 (six merged PRs + this STATE-SYNC)"
- `Next-ACT candidates` table: 2-row, claims S5-a "DONE" but S5-b not yet shipped
- `Next Action`: "**Researcher's choice**: pick one of S5-b / S5-c / S6"

All eight bullets above predate the four post-Session-8 merges
(#19283 / #19192 / #19181 / #19321 / #19046 / #19343) and need refresh.
The header block, `Lean status at HEAD` table, `Merged PRs` table,
`Attempt Count`, `Next-ACT candidates` table, and `Next Action`
section are all updated atomically in this STATE-SYNC.

The Session-log block keeps the existing Session 1–8 entries verbatim
(prior-tail preservation per `_main_repo_linter_reverts_edits` analogue
of preserving append-near-top sessions) and prepends a new "Session 9
STATE-SYNC" block above them.

---

## §3. The 6 merges Session 9 absorbs

Chronological order (UTC), all on `main` at `8a3cda556b6`:

| #   | PR     | Phase                          | Merged (UTC)              | Diff                                                                     | Recorded in S8 STATE-SYNC? |
|-----|--------|--------------------------------|---------------------------|--------------------------------------------------------------------------|-----------------------------|
| 1   | #19283 | S5-b PREP                      | 2026-05-15T18:01:41Z      | +339 LOC sessions/2026-05-15-s5b-prep-Tv-preimage.md (doc-only)         | **No**                      |
| 2   | #19192 | S6 PREP-2                      | 2026-05-15T22:55:55Z      | +537 LOC sessions/2026-05-14-s6-prep-2-stdLatticeN-skeleton-audit.md     | **No**                      |
| 3   | #19181 | S5-c PREP                      | 2026-05-15T22:56:26Z      | +353 LOC sessions/2026-05-14-s5c-prep-rect-volume-bridge.md             | **No**                      |
| 4   | #19321 | S8-c PREP — post-drain audit   | 2026-05-15T~23:11Z (body) | +366 LOC sessions/2026-05-15-s8c-prep-postdrain-audit.md (§1–§9)        | **No**                      |
| 5   | #19046 | **S5-b ACT** (Lean)            | 2026-05-15T23:27:39Z      | +79 / −0 LOC `MinkowskiTheoremOQ02OQ03.lean` (4 new declarations, see §2.1) | **No**                      |
| 6   | #19343 | S8-c PREP §10 addendum         | 2026-05-16T01:08:50Z      | +52 LOC §10 appended to the S8-c PREP sessions file                     | **No**                      |
|     | (this) | **Session 9 STATE-SYNC**       | (this PR)                 | +new sessions file (§N here) + state.md + JSON refresh                  | n/a (in flight)             |

Session 8 STATE-SYNC (#18991), authored against an early-`2026-05-14`
HEAD, catches only `#18975` (S5-a ACT, `2026-05-14T03:03:55Z`). All
six rows above merged after that branch-base capture.

---

## §4. Bearer drift re-verify at pin `2df2f0150c27…`

S8-c PREP §1 re-verified all 6 cited bearers against the Mathlib pin.
S8-c §10 addendum re-confirmed at the post-merge HEAD `d35a6f0f2ac…`
(prior to `8a3cda556b6`). This STATE-SYNC re-runs the same probe at
the current HEAD to close the integrity gap.

| # | Bearer                                              | Path                                                                                              | Line | Pin                                                                 | Status (this STATE-SYNC)                                |
|---|-----------------------------------------------------|---------------------------------------------------------------------------------------------------|------|---------------------------------------------------------------------|---------------------------------------------------------|
| 1 | `Real.volume_pi_Ioo`                                | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`                                              | 236  | `2df2f0150c27…`                                                     | ✅ (signature + namespace match S8-c §1 row 1)          |
| 2 | `Real.map_matrix_volume_pi_eq_smul_volume_pi`       | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`                                              | 397  | `2df2f0150c27…`                                                     | ✅ (`abs (det M)⁻¹ • volume` form unchanged)            |
| 3 | `Submodule.mem_span_range_iff_exists_fun`           | `Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean`                                            | 372  | `2df2f0150c27…`                                                     | ✅                                                       |
| 4 | `Pi.basisFun_apply`                                 | `Mathlib/LinearAlgebra/StdBasis.lean`                                                             | 131  | `2df2f0150c27…`                                                     | ✅                                                       |
| 5 | `Finset.sum_ite_eq'`                                | `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean`                                        | 151  | `2df2f0150c27…`                                                     | ✅ `@[simp]` confirmed (additive of `prod_ite_eq'`)     |
| 6 | `Int.cast_smul_eq_zsmul`                            | `Mathlib/Algebra/Module/NatInt.lean`                                                              | 151  | `2df2f0150c27…`                                                     | ✅ (modern non-deprecated form, dir-reversed `.symm` use) |

**Verdict.** Zero substantive drift. The `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
pin in `proofs/lake-manifest.json` is unchanged across the Session 8 →
Session 9 window (~24 h). All 6 bearers carry forward into S5-c / S6α
/ S6 ACT unchanged.

Two bearers used by `#19046`'s S5-b ACT proofs are **not** in S8-c §1's
table (since they are internal to the row-0 / row-`i.succ` `dotProduct`
collapse rather than the volume / lattice infrastructure):

| # | Bearer                       | Path                                                  | Line | Status (this STATE-SYNC)                                |
|---|------------------------------|-------------------------------------------------------|------|---------------------------------------------------------|
| 7 | `Matrix.toLin'_apply`        | `Mathlib/LinearAlgebra/Matrix/ToLin.lean`             | 297  | ✅ at pin (signature `(M.toLin' v) i = ∑ j, M i j * v j`) |
| 8 | `Finset.sum_eq_single`       | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 1146 | ✅ at pin (one-non-trivial-summand collapse)            |

Both fire as written inside `shearM_toLin'_apply_zero` and
`shearM_toLin'_apply_succ`. Recording here for completeness so the
next claimant has the full bearer surface.

---

## §5. Next-ACT readiness gate (post-S5-b on `main`)

Per S8-c §5 + S8-c §10:

| Stage         | Recipe source                                                   | Net `.lean` LOC | Depends on (on `main` now)                                              | Parallelizable with                |
|---------------|-----------------------------------------------------------------|-----------------|-------------------------------------------------------------------------|------------------------------------|
| **S5-c ACT**  | #19181 §3 recipe (3 declarations: `dirichletBoxN_measurable`, `dirichletBoxN_volume` ENNReal-valued (B1), `dirichletSetN_volume` via pushforward) | ~49 (15 + 15 + 19 split per §3 LOC table) | `dirichletBoxN`, `shearM_det = (-1)^n`, `dirichletSetN_eq_shearM_preimage` — all 3 **on `main` now** | **S6α ACT** (disjoint declarations) |
| **S6α ACT**   | #19192 §5 refined skeleton (`stdLatticeN_coords (n+1)` integer-coordinate extraction) | ~22                                            | `shearM_det = (-1)^n` only — **on `main` now**                          | **S5-c ACT** (disjoint declarations) |
| **S6 ACT**    | #18511 (S6 PREP) 5-stage assembly pattern                       | ~80             | `dirichletSetN_volume` (S5-c) + `stdLatticeN_coords` (S6α)              | n/a (final assembly)                |

**Critical observation** (carried forward from S8-c §5):
`stdLatticeN_coords` only depends on `S5-a` (already on `main`), **not**
on the S5-b / S5-c chain. So S5-c ACT and S6α ACT can each be claimed
and pushed in any order; only `S6 ACT` requires both upstream stages.

**Estimated remaining `.lean` LOC to graduate OQ-03 from current `main`**:
**~150 LOC across 3 ACTs** (unchanged from S8-c §8 since this STATE-SYNC
adds no Lean).

**Recommended pick order for the next claimant**:

1. **S5-c ACT** (highest payoff: replaces the last "pending"
   Minkowski hypothesis on `dirichletSetN`). Recipe pinned at `#19181`
   §3.A/B/C. 15 LOC budget for Step B (ENNReal-valued B1 per §4.3 of
   S8-c PREP). Falls back to C-ii parity case-split for the
   `abs ((-1)^n)⁻¹ = 1` plumbing if C-i drifts (S8-c §4.4).
2. **S6α ACT** (parallelizable). Recipe at `#19192` §5 with
   `Submodule.mem_span_range_iff_exists_fun` + `Pi.basisFun_apply` +
   `Finset.sum_ite_eq'` + `Int.cast_smul_eq_zsmul` bearers verified
   at §4 above.
3. **S6 ACT** (final assembly) once both above land. Pattern at
   `MinkowskiTheoremOQ02.lean:182`.

---

## §6. Attempt-count breakdown

Session 8 STATE-SYNC (#18991, merged 2026-05-15T23:29:31Z) recorded
"Total attempts: 7 (six merged PRs + this STATE-SYNC)". The "six
merged PRs" at that snapshot were #18339 (S1) + #18419 (S5 PREP) +
#18511 (S6 PREP) + #18551 (S2 ACT) + #18613 (S3 + S4 ACT) + #18622
(S5 PREP-2) — plus the **Session 7 STATE-SYNC** #18967 which is the
seventh. Session 8 STATE-SYNC itself (#18991) is the eighth attempt.
Then #18975 (S5-a ACT, merged 2026-05-14T03:03:55Z) preceded #18991 by
~26 minutes but #18991's authoring captured #18975 as a "previous
merged PR" rather than as its own attempt counter increment. We
inherit and continue.

Reconciling at this STATE-SYNC:

| Counted attempt # | PR                  | Phase                             |
|-------------------|---------------------|-----------------------------------|
| 1                 | #18339              | S1 OBSERVE                        |
| 2                 | #18419              | S5 PREP                           |
| 3                 | #18511              | S6 PREP                           |
| 4                 | #18551              | S2 ACT                            |
| 5                 | #18613              | S3 + S4 ACT                       |
| 6                 | #18622              | S5 PREP-2                         |
| 7                 | #18967              | Session 7 STATE-SYNC              |
| 8                 | #18975              | S5-a ACT                          |
| 9                 | #18991              | Session 8 STATE-SYNC              |
| 10                | #19283              | S5-b PREP                         |
| 11                | #19192              | S6 PREP-2                         |
| 12                | #19181              | S5-c PREP                         |
| 13                | #19321              | S8-c PREP body (§1–§9)            |
| 14                | #19046              | **S5-b ACT** (Lean, +79 LOC)      |
| 15                | #19343              | S8-c PREP §10 addendum            |
| 16                | (this PR)           | **Session 9 STATE-SYNC**          |

So:

- `attemptCounts.total` ← `16`
- `attemptCounts.currentApproach` ← `16` (all 16 are Approach A)
- `attemptCounts.approachesTried` ← `1`

(Session 8's "13" forecast in §2.2 above was a placeholder pulled
from S5-a's split convention; the canonical count is 16 per the
authoritative table here. The state.md "Attempt Count" section uses
this 16-figure.)

---

## §7. Orthogonality manifest

This STATE-SYNC touches exactly **three** files:

| Path                                                                                          | Class                  | Edit type                                  |
|-----------------------------------------------------------------------------------------------|------------------------|--------------------------------------------|
| `research/problems/minkowski-theorem-oq-02-oq-03/sessions/2026-05-16-s9-statesync.md`         | new sessions/ file     | **add** (this file, ~600 LOC)              |
| `research/problems/minkowski-theorem-oq-02-oq-03/state.md`                                    | top-of-file + tables   | **modify** (header + tables, append Session 9 log block at top of Session-log entries) |
| `src/data/research/problems/minkowski-theorem-oq-02-oq-03.json`                               | sidecar JSON           | **modify** (currentState.* + leanFiles[0] + lastUpdate + updatedAt + knowledge.*) |

**Files NOT touched**:

- `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` — strict no-Lean (this
  is a doc-only STATE-SYNC).
- `research/problems/minkowski-theorem-oq-02-oq-03/problem.md` — frozen
  since S1 OBSERVE.
- `research/problems/minkowski-theorem-oq-02-oq-03/knowledge.md` — last
  bumped at S1 OBSERVE; per S8-c §6.2 convention, knowledge.md is
  reserved for cross-cutting Mathlib insights rather than per-iteration
  STATE-SYNC delta capture.
- `research/problems/minkowski-theorem-oq-02-oq-03/approaches/*` (if
  any) — frozen since S1 OBSERVE; only Approach A active.
- `src/data/proofs/minkowski-theorem-oq-02-oq-03/meta.json` — gallery
  meta.json (auditor-managed; this STATE-SYNC's `leanFiles` update is
  in the **research-side** JSON sidecar, not the gallery meta).

**Cross-PR safety check** (open PRs on this slug at branch-creation
time `2026-05-16T01:32Z`): `gh pr list --repo rjwalters/lean-genius
--search "minkowski-theorem-oq-02-oq-03" --state open` returns **0**
results. No conflict surface; this STATE-SYNC merges cleanly.

---

## §8. Parent-regression catalogue (carried forward, unchanged)

Per Session 8 STATE-SYNC §"Active Approach" + S1 OBSERVE: the
parent OQ (1D, `MinkowskiTheoremOQ02.lean`) and its axiom-free sibling
(`MinkowskiTheoremOQ02OQ01.lean`) remain the regression bearers for
this slug. The lift pattern is:

| Parent declaration                              | Parent file:line                                      | OQ-03 analogue (status)                                              |
|-------------------------------------------------|-------------------------------------------------------|----------------------------------------------------------------------|
| `dirichletSet`                                  | `MinkowskiTheoremOQ02OQ01.lean:41`                    | `dirichletSetN` (✅ shipped, #18551)                                  |
| `dirichletSet_symmetric`                        | `MinkowskiTheoremOQ02OQ01.lean:48`                    | `dirichletSetN_symmetric` (✅ shipped, #18551)                        |
| `dirichletSet_measurable`                       | `MinkowskiTheoremOQ02OQ01.lean:60`                    | `dirichletSetN_measurable` (✅ shipped, #18613)                       |
| `dirichletSet_convex`                           | `MinkowskiTheoremOQ02OQ01.lean:75`                    | `dirichletSetN_convex` (✅ shipped, #18613)                           |
| `M` (shear matrix) + `T_image_is_rectangle`     | `MinkowskiTheoremOQ02OQ01.lean:101–158`               | `shearM` + `dirichletBoxN` + `dirichletSetN_eq_shearM_preimage` (✅ shipped, #18975 + #19046) |
| `dirichletSet_volume`                           | `MinkowskiTheoremOQ02OQ01.lean:~160`                  | `dirichletSetN_volume` (**pending S5-c ACT**, #19181 recipe)         |
| `dirichlet_approximation_from_minkowski` (assembly) | `MinkowskiTheoremOQ02.lean:182` (parent OQ, with-axioms route — assembly logic verbatim) | `simultaneous_dirichlet_from_minkowski` (**pending S6 ACT**, #18511 recipe) |
| `stdLattice2_coords`                            | `MinkowskiTheoremOQ02OQ01.lean:~210`                  | `stdLatticeN_coords` (**pending S6α ACT**, #19192 recipe)            |

Zero regression risk to either parent file from any of S5-c / S6α / S6
ACT: all ACT recipes only **add** declarations to
`MinkowskiTheoremOQ02OQ03.lean` and do not touch the parent files.

---

## §9. Hazards forwarded to next-ACT claimant

All 5 hazards itemised in S8-c PREP §7 carry forward unchanged. The
canonical reference is `sessions/2026-05-15-s8c-prep-postdrain-audit.md`
§7. For convenience:

1. **`Fin.cases_zero` opaque without explicit substitution** (per
   S5-b PREP §gap-1). `#19046` uses `refine j.cases ?_ ?_` to
   discharge this — verified live in
   `MinkowskiTheoremOQ02OQ03.lean:319` (the
   `dirichletSetN_eq_shearM_preimage` proof). Carries no live risk
   for S5-c (which works with `dirichletBoxN` constructed by
   `Set.pi Set.univ … Fin.cases …` — the `Fin.cases` here is on
   the box-construction side and discharges via `Set.mem_pi`,
   which is `Fin.cases`-blind by design).
2. **`Finset.sum_ite_eq'` vs `sum_ite_eq` directional pitfall**.
   Live risk for **S6α ACT** (Step 3 of #19192 §5 skeleton). `'`
   form required; verified at pin in §4 row 5.
3. **`Int.cast_smul_eq_zsmul` direction-reversed**. Live risk for
   **S6α ACT**. Workaround at #19192 §"hazards" #3: insert `.symm`.
4. **`ENNReal.ofReal` factor-out for `dirichletBoxN_volume`**. Live
   risk for **S5-c ACT** Step B. Bulk-lemma chain
   `ENNReal.ofReal_prod_of_nonneg.symm` + `ENNReal.ofReal_mul`;
   fallback to per-coordinate case-split if rewrite stalls.
   Estimated overhead +6 LOC per S8-c §7.4.
5. **`abs (det shearM)⁻¹ = 1` plumbing**. Live risk for **S5-c
   ACT** Step C. C-i preferred (~1 line:
   `simp [shearM_det, abs_neg_one_pow, abs_one, inv_one]`); C-ii
   parity case-split fallback (~3 lines) held in reserve.

No new hazards surface from #19046's S5-b ACT (the proofs were
discharged sorry-free / axiom-free at first push; build-verified 3058
jobs at 2026-05-14 per PR body). The `Fin.cases` lesson (hazard 1
above) is the one nontrivial S5-b ACT lesson worth promoting into the
next-claimant's knowledge surface; recorded as the +1 insight in JSON
(§2.2 final row).

---

## §10. Action items forward (for the next claimant)

Carry-forward of S8-c PREP §10 addendum action list, updated for
post-this-STATE-SYNC state:

1. ~~Ship the §6.1 Option-B STATE-SYNC (rows 2–5 + leanFiles fix).~~
   **CLOSED by this PR.**
2. **Ship S5-c ACT** (~49 LOC). Recipe at `#19181` §3.A/B/C; Step B
   ENNReal-valued B1 per S8-c §4.3; Step C C-i preferred per S8-c
   §4.4. All bearers verified at §4 above.
3. **Ship S6α ACT** (~22 LOC), parallelizable with S5-c per S8-c
   §5. Recipe at `#19192` §5; hazards 2 + 3 (above) live; bearer
   verification carried forward from §4 above.
4. **Ship S6 ACT** (~80 LOC) once both S5-c and S6α land. Recipe
   at `#18511` §1–§5 (assembly pattern mirroring
   `MinkowskiTheoremOQ02.lean:182`).

**Estimated remaining `.lean` LOC to OQ-03 graduation from current
`main`**: ~150 LOC across the 3 ACTs above.

---

## §11. Honest-status block

- **Mathematical progress in this PR**: zero. STATE-SYNC catches the
  books up to `8a3cda556b6` `origin/main` HEAD without adding any
  theorem, definition, sorry, or axiom.
- **Build status**: unchanged. The post-S5-a + post-S5-b chain remains
  build-verified per the active "build pending convention" — `#19046`
  shipped with "build verified 3058 jobs" per its PR body
  (2026-05-14), and no Lean changes here. No Docker build attempted
  for this STATE-SYNC; none needed.
- **Pre-claim cross-checks**:
  - Branch created off `origin/main` `8a3cda556b6` (not off the
    researcher-1 worktree's pre-existing `research/shapley-folkman-oq-01-s10-statesync`
    branch — avoiding the `_shared_worktree_race_branch_swapped_after_push`
    cross-slug-contamination trap).
  - `git fetch origin +refs/heads/main:refs/remotes/origin/main`
    used implicitly via `git checkout -b … origin/main` (per
    `_git_fetch_origin_main_updates_fetch_head_not_remote_ref`
    convention — the explicit refspec form was used in the
    pre-branching fetch).
  - `gh pr list --repo rjwalters/lean-genius` explicit `--repo`
    flag used throughout (per `_gh_default_remote_mathlib_fork_artifact_in_researcher_worktrees`).
  - `gh pr list … --limit 500` explicit `--limit` used (per
    `_gh_pr_list_default_limit_30_artifact_trap`).
  - Files edited via worktree absolute paths
    (`/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1/...`)
    not main-repo bare paths (per `_main_repo_linter_reverts_edits_use_worktree_absolute_path`).
  - Audited the Lean file content at `origin/main` to confirm 331
    LOC + 4-new-declaration manifest matches §2.1 declaration
    table — counts not stuck on stale-main artifact.

---

## §12. Verification checklist

- [x] New sessions/ file `2026-05-16-s9-statesync.md` does not
  collide with any existing session filename in the slug's
  `sessions/` directory (latest existing is
  `2026-05-15-s8c-prep-postdrain-audit.md`).
- [x] state.md preserves all prior Session-log entries (Session 1–8
  blocks intact); Session 9 block prepended at top of session-log
  region.
- [x] state.md `Current State` header rewritten to reflect post-#19046
  + post-#19343 status; `Last Updated`, `Iteration`, `Lean status at
  HEAD` 11-row table, `Merged PRs` 14-row table, `Attempt Count`,
  `Next-ACT candidates`, `Next Action` sections all aligned with
  §2.1 / §3 / §5 / §6 here.
- [x] JSON sidecar `currentState.iteration` 7 → 8, `focus` /
  `nextAction` / `attemptCounts` rewritten, `lastUpdate` /
  `updatedAt` bumped to 2026-05-16, `leanFiles[0]` `lineCount` 252
  → 331 / `theoremCount` 4 → 8 / `defCount` 2 → 3, `knowledge.builtItems`
  list appended, `knowledge.insights` +1 entry. No other JSON edits.
- [x] All 6 + 2 bearers re-verified at Mathlib pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (§4).
- [x] 0 open PRs on slug at branch-creation time `2026-05-16T01:32Z`
  (`gh pr list --repo rjwalters/lean-genius --search
  "minkowski-theorem-oq-02-oq-03" --state open`). No conflict surface.
- [x] Branch base `origin/main` `8a3cda556b6` (post-S8-c §10
  addendum HEAD).
- [x] Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (v4.26.0) re-confirmed via `proofs/lake-manifest.json` unchanged.
- [x] No `.lean` / `problem.md` / `knowledge.md` / `approaches/*`
  edits in this PR.
