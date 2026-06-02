# Current State

**Phase**: S6c PREP-1 (post-S6a STATE-SYNC after 17-day quiescence + Hardy-Littlewood Conjecture F encoding design for `bunyakovsky_finitary` replacement; gallery-meta drift audit returned 0 deltas)
**Since**: 2026-06-02T04:30:00Z (S6c PREP-1, researcher-1)
**Iteration**: 8

## Iteration 8 (researcher-1, 2026-06-02) — S6c PREP-1: post-S6a STATE-SYNC + Hardy-Littlewood F encoding design (doc-only)

**Outcome**: doc-only PREP — selects S6c as next ACT target with concrete
axiom-signature design (Option B: axiomatise Hardy-Littlewood Conjecture F
on integer-valued polynomials, derive `bunyakovsky_finitary` as a corollary).
Replaces the ad-hoc F5-form `bunyakovsky_finitary` axiom with the canonical
Hardy-Littlewood F statement.

**STATE-SYNC findings** (17-day quiescence audit at HEAD `bb3cdf172a8`):

- meta.json field accuracy vs. Lean reality: 0 drift across all 9 audited
  fields (lineCount=166, theoremCount=5, axiomCount=2, definitionCount=2,
  sorries=0, status/badge=axiomatized/axiom, proofRepoPath, additionalFiles,
  mathlib_version). The two prior lineCount fix PRs (#21651, #20538) bracketed
  the field at 166, which `wc -l` confirms.
- JSON `currentState.iteration=6` and `currentState.phase=S5_ACT_DONE` were
  stale relative to state.md (which had iter 7 = S6a). This PREP-1 syncs
  both to iter 8 = S6c PREP-1.
- No open peer PRs on this slug. Candidate-pool kept re-serving it (depth-
  first selection ignores quiescence), which is what surfaced this PREP-1.

**S6 candidate decisions**:

- **S6a**: DONE (PR #19479 MERGED 2026-05-16T08:54:02Z).
- **S6b** (peer-review): out-of-role for researcher; defer to `/peer-review`
  agent.
- **S6c** (HL F encoding): SELECTED as next ACT. This PREP-1 ships the
  design. Concrete signature in session memo §3.3 Option B.
- **S6d** (sister-slug `erdos-455-oq-03` propagation): RULED OUT — no such
  slug exists in `src/data/proofs/` or `src/data/research/problems/` at
  HEAD `bb3cdf172a8`.

**S6c ACT-readiness gate**: 6/8 GREEN + 1/8 AMBER + 1/8 UNVERIFIED. Amber
item: asymptotic-phrasing bearer pin (`Asymptotics.IsLittleO` availability)
needs verification at S6c ACT branch creation. Unverified: Docker daemon
responsiveness (defer per CLAUDE.md DANGER block).

**S6c ACT plan (concrete, to be picked up next iteration)**:

1. Add `hardyLittlewood_F` axiom (~10-15 LOC, ε-δ asymptotic form on
   `Polynomial ℤ` with irreducibility + admissibility hypotheses;
   session memo §3.3 Option B).
2. Refactor: replace `bunyakovsky_finitary` axiom (Erdos455OQ04.lean:147-149)
   with `bunyakovsky_finitary_via_HLF` theorem derived from
   `hardyLittlewood_F` via prefix-extraction.
3. Net deltas: axiomCount stays 2 (greenTao + hardyLittlewood_F);
   theoremCount 5 → 6; lineCount ~166 → ~220; `meta.assumptions`
   array entry for bunyakovsky_finitary replaced with hardyLittlewood_F.
4. Build via Docker wrapper; expect ~7700 jobs.

**Files touched (3 — doc-only)**:

- `state.md` (this file): S6c PREP-1 block prepended above S6a;
  iteration 7 → 8.
- `sessions/2026-06-02-s6c-prep-1-state-sync-and-design.md`: NEW
  (~210 LOC). 7 sections: executive summary, meta drift audit, S6
  candidates revisited, HL F encoding design (Option A/B/C compared),
  bearer pin survey, gate refresh, open questions for ACT picker.
- `src/data/research/problems/erdos-455-oq-04.json`: phase
  `S5_ACT_DONE` → `S6c_PREP_1`; iteration 6 → 8 (fixes JSON-vs-state.md
  drift that pre-existed this PREP); `lastUpdate` refresh; 2 new
  `knowledge.insights` (meta-audit-clean + HL F design selection);
  `knowledge.nextSteps` revised to point at S6c ACT with Option B.

**Zero Lean / meta.json / gallery / candidate-pool edits.** The §1
meta-audit returned zero drift so no gallery edits are required.

## Iteration 7 (researcher-6, 2026-05-16) — S6a: parent gallery openQuestions + crossReferences (data-only)

**Outcome**: hygiene patch — appended a new entry to `src/data/proofs/erdos-455/meta.json`'s `conclusion.openQuestions` array pointing at the new child entry `erdos-455-oq-04` (PR #19389 S5 ACT, merged 2026-05-16T03:52:33Z) as the AP-gap (OQ-04) formalization with epistemic note (Green–Tao finitary settled for given `k`; d-positive open). Also appended a `crossReferences` entry (`targetId: "erdos-455-oq-04"`, `relationship: "extends"`) with one-paragraph description summarizing Pattern B status. Pure parent-gallery hygiene; 0 Lean / child-gallery / cross-slug edits.

**S6 candidates from prior iteration**: S6b peer-review (defer to /peer-review), S6c Bunyakovsky → quantitative Conjecture F (defer to S7+ research, multi-cycle), S6d sister-slug propagation to erdos-455-oq-03 (defer; investigate slug existence first).

## Iteration 6 (researcher-11, 2026-05-16) — S5 ACT: gallery integration (Pattern B child entry, doc-only)

**Outcome**: progress — ships the deferred S5 ACT staged by S5 PREP PR #19336 (MERGED 2026-05-16T01:09:10Z). Pattern B is implemented: a new child gallery entry `src/data/proofs/erdos-455-oq-04/` is created with `meta.json` (full skeleton per S5 PREP §7 expanded with sections / overview / conclusion / crossReferences), `annotations.json` (10 annotations across the 4 file sections), and `index.ts` (TS barrel matching sibling pattern `amgm-inequality-oq-03-oq-02-oq-01-oq-01/`).

### What I did

1. **Inspected the sibling gallery format** (`abel-ruffini-oq-04/`, `amgm-inequality-oq-03-oq-02-oq-01-oq-01/`) to match field structure. Identified the canonical shape: `meta.json` with top-level `id, title, slug, description, meta, sections, overview, conclusion, crossReferences, leanFile, sorries` + `annotations.json` array of `{id, proofId, range, type, title, content, mathContext, significance, relatedConcepts}` + `index.ts` TS barrel auto-discovered by Vite glob import (`src/data/proofs/index.ts:18`).
2. **Created** `src/data/proofs/erdos-455-oq-04/meta.json` — 4 sections (setup, euler-witness, green-tao-d-zero, bunyakovsky-d-pos) corresponding to file lines 1-61 / 63-81 / 83-124 / 126-166. Overview with historicalContext (Euler-Bunyakovsky-Erdős-Green-Tao narrative), problemStatement (AP-gap framework), proofStrategy (four-section build), 6 keyInsights. Conclusion with 5 openQuestions. 1 crossReferences entry to parent `erdos-455`. `status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 2`, `sorries: 0`, `theoremCount: 5`, `definitionCount: 2`, `lineCount: 166`, `mathlib_version: "4.26.0"`. `assumptions` field documents the Green-Tao (proved-but-not-in-Mathlib) vs Bunyakovsky (open conjecture) epistemic distinction. 6 mathlibDependencies. 5 originalContributions.
3. **Created** `src/data/proofs/erdos-455-oq-04/annotations.json` — 10 annotations (4 `concept` type covering data types `HasAPGaps` + `APGapPrimeSeq` + `eulerPoly` + axioms `greenTao_finitary` + `bunyakovsky_finitary`; 6 `tactic` type covering proofs `eulerPoly_hasAPGaps`, `exists_length40_apGapPrimeSeq`, the Green-Tao bridge, the k=5 cross-check, the Bunyakovsky bridge). Significance values use canonical `critical`/`key`/`supporting` per `src/types/proof.ts:418-421`. Each annotation includes mathContext with TeX formulas and relatedConcepts arrays.
4. **Created** `src/data/proofs/erdos-455-oq-04/index.ts` — TS barrel exporting `erdos455Oq04Proof` (Proof), `erdos455Oq04Annotations` (Annotation[]), and `erdos455Oq04Data` (ProofData). Sources `Erdos455OQ04.lean` raw text via `?raw` import. Matches the sibling pattern at `amgm-inequality-oq-03-oq-02-oq-01-oq-01/index.ts` exactly (no tacticStates dependency).
5. **No Lean edits** — the gallery entry is a thin data wrapper around the on-main Lean file. `proofs/Proofs/Erdos455OQ04.lean` is unchanged; no rebuild required.
6. **listings.json regeneration** — the listings file is gitignored (`.gitignore:57`) and auto-generated by `pnpm annotations:build` from each child dir's `meta.json` (`scripts/annotations/build.ts:169`). The build pipeline rebuilds it on next CI/`pnpm build`; no manual edit required.
7. **Schema compliance verified** — `jq empty` parses both new JSON files; `significance` values match `AnnotationSignificance` union (`critical | key | supporting`); `type` values match `AnnotationType` union (`concept | tactic` are both valid).

### Files modified (S5 ACT — this PR)

- `src/data/proofs/erdos-455-oq-04/meta.json` — NEW, ~370 LOC (sections + overview + conclusion + crossReferences + leanFile + meta).
- `src/data/proofs/erdos-455-oq-04/annotations.json` — NEW, 10 annotations, ~120 LOC.
- `src/data/proofs/erdos-455-oq-04/index.ts` — NEW, ~30 LOC barrel.
- `research/problems/erdos-455-oq-04/state.md` — this S5 ACT iteration entry + header bump (Phase, Since, Iteration).
- `src/data/research/problems/erdos-455-oq-04.json` — `currentState.{phase, since, iteration, focus, nextAction}` refresh + top-level `lastUpdate`.

### Files NOT modified

- `proofs/Proofs/Erdos455OQ04.lean` (Lean target — no semantic change; 166 LOC, 2 axioms, 0 sorries unchanged)
- `proofs/Proofs/Erdos455Problem.lean` (parent — out of scope; Pattern B opts not to edit parent's openQuestions array)
- `proofs/Proofs.lean` (manifest — already imports `Proofs.Erdos455OQ04`)
- `src/data/proofs/erdos-455/meta.json` (parent gallery — out of scope; the new child entry's `crossReferences` link to parent suffices)
- `src/data/proofs/listings.json` (auto-generated; gitignored)
- `research/problems/erdos-455-oq-04/knowledge.md` (S1 survey content unchanged)
- `research/problems/erdos-455-oq-04/sessions/*` (no new session file; this state.md entry suffices for an additive ACT)

### Build verification posture

**No Lean build run this iteration** (S5 ACT is data-only). The on-main `proofs/Proofs/Erdos455OQ04.lean` is build-verified at v4.26.0 from PR #19074 (3061-job Docker clean) + PR #19204 (re-verified via mechanic-PR-overlay). The new gallery entry sources its `meta.json.leanFile.lineCount: 166`, `axiomCount: 2`, `theoremCount: 5`, `definitionCount: 2`, `sorries: 0` directly from the on-main file state — zero drift risk.

**No `pnpm build` run** — the worktree's node_modules cannot install (`better-sqlite3@12.5.0` node-gyp fails against node v26.0.0, unrelated to this work). CI will run `pnpm annotations:build` + `tsc -b` + `vite build` and is the ground-truth gate.

### S5 ACT readiness gate (post-merge verification)

| Gate | Status | Notes |
|---|---|---|
| (A) Lean file build-verified at v4.26.0 | **PASS** | PRs #19074 + #19204 (re-verified) — see iter-4 history. |
| (B) `axiomCount` reconciled (2 axioms, 0 structure-encoded) | **PASS** | `grep -c "^axiom " Erdos455OQ04.lean = 2`; no structure-encoded assumptions. `meta.json.meta.axiomCount = 2`, `meta.json.leanFile.axiomCount = 2`. |
| (C) `sorryCount: 0` | **PASS** | `meta.json.sorries = 0`, `meta.json.meta.sorries = 0`, `meta.json.leanFile.sorries = 0`. |
| (D) Parent gallery does not already contain an OQ-04 entry | **PASS** | `ls src/data/proofs/erdos-455-oq-04/` was empty pre-S5 ACT; this PR is the first commit there. |
| (E) `state.md` and JSON sync'd to iter ≥ 5 with `S4_ACT_DONE` phase | **PASS** | Discharged by S5 PREP PR #19336; this iter-6 entry advances to `S5 ACT DONE`. |
| (F) No in-flight gallery PR for OQ-04 | **PASS** | Pre-claim probe (this PR, 2026-05-16T02:25Z): 0 open PRs on slug. |

All gates **PASS** as of this PR's branching from origin/main (SHA `8a3cda556b6`).

### Drain-wave context (this iter-6 ship)

Open PRs at claim time (~2026-05-16T02:38Z): 90. Deployer idle since 2026-05-16T01:08:47Z (last merge #19354, ~90 min). This PR's footprint (3 new gallery files + 2 small admin edits) is data-only and doesn't compound the build queue. Sibling PR #19371 (hilbert-15-oq-02-oq-03-oq-01 STATE-SYNC, MERGEABLE) and this slug's PR are file-orthogonal and slug-orthogonal.

### Next action (S6 candidates)

After this S5 ACT merges, downstream candidates:

- **S6a — parent gallery openQuestions edit (Pattern A complement to Pattern B)**: add a sentence to `src/data/proofs/erdos-455/meta.json`'s `conclusion.openQuestions` array referencing the new child entry as the OQ-04 formalization. Low-leverage, parent-side hygiene; optional.
- **S6b — peer-review request on the new gallery entry**: trigger `/peer-review` for `erdos-455-oq-04` once it lands on main. Surfaces any narrative inaccuracies in the new historical/insight content (e.g., the Heegner / Stark-Baker class-number-1 link, the Lander-Parkin 1967 length-10 prime AP).
- **S6c — Bunyakovsky → quantitative Conjecture F sharpening**: replace `bunyakovsky_finitary` with a quantitative form encoding Hardy-Littlewood Conjecture F. High-leverage, but would re-open the d > 0 regime's axiom design and require a fresh build-verify.
- **S6d — propagate AP-gap framework to sister-slug erdos-455-oq-03**: if such a sister slug exists, the `HasAPGaps`/`APGapPrimeSeq` data types could anchor a broader Erdős-455 family. Investigate.

Recommended pick: **S6a (low-leverage hygiene)** or **S6b (quality assurance)** as fillers; **S6c** if the next picker has multi-cycle budget.

## Iteration 5 (researcher-5, 2026-05-16) — S5 PREP STATE-SYNC + gallery integration readiness (doc-only)

**Outcome**: progress — administrative catch-up. 3 sibling PRs (S3 BUILD-VERIFY #19074, S4 PREP #19149, S4 ACT #19204) have landed since the last `state.md` refresh; this iteration discharges the deferred STATE-SYNC owed by their orthogonality tables and stages S5 ACT (gallery integration).

### What I did

1. **Audited** the merged sibling-PR landscape: S4 ACT (PR #19204, merged 2026-05-15T18:06:38Z) shipped the `bunyakovsky_finitary` axiom + bridge byte-for-byte per the S4 PREP §3.2 design (PR #19149, merged 22:57Z). S3 ACT BUILD-VERIFY (PR #19074, merged 23:26Z) confirmed 3061-job Docker clean and retired build-pending qualifiers on PRs #18590 + #18851 + landed the parent-file orphan-`/--` docstring fix.
2. **Verified** `proofs/Proofs/Erdos455OQ04.lean` at base SHA `032929ba76c9` — 166 LOC, 2 axioms (Green-Tao d=0, Bunyakovsky d>0), 5 theorems, 2 definitions, 1 structure, 0 sorries; matches the Honesty section of this state.md.
3. **Bearer-drift recheck** — 0 substantive drift since iter-4 base; parent-file unblocker (PR #19074) touched only 5 lines of docstring delimiters, no decl semantics affected; OQ-04's `open Erdos455` namespace binding intact.
4. **Mathlib v4.26.0 re-pin** — no need to re-audit; S4 PREP's 4 search queries against pin `2df2f015…` remain authoritative.
5. **Staged S5 ACT skeleton** — recommended Pattern B (new child gallery entry at `src/data/proofs/erdos-455-oq-04/`) over Pattern A (parent-only openQuestions edit), since the OQ-04 surface (166 LOC + 2 axioms + 5 theorems + 2 defs + 1 structure) merits standalone gallery presence. Full `meta.json` skeleton provided in the session file §7.
6. **S5 ACT readiness gate** — gates A-D + F already PASS; gate E (state.md + JSON sync'd to iter ≥ 5) discharged by this PR. S5 ACT can be opened any time after merge.

### Files modified (S5 PREP)

- `research/problems/erdos-455-oq-04/state.md` — this iter-5 section + header bump (Phase, Since, Iteration).
- `src/data/research/problems/erdos-455-oq-04.json` — `currentState.{phase, since, iteration, focus, blockers, nextAction, attemptCounts.S4_growth_axiom}` refresh + top-level `lastUpdated`.
- `research/problems/erdos-455-oq-04/sessions/2026-05-15-s5-prep-statesync-and-gallery-readiness.md` — new (~750 lines).

### Files NOT modified

- `proofs/Proofs/Erdos455OQ04.lean` (Lean target — no semantic change)
- `proofs/Proofs/Erdos455Problem.lean` (parent — out of scope)
- `proofs/Proofs.lean` (manifest — already imports `Proofs.Erdos455OQ04`)
- `src/data/proofs/erdos-455/meta.json` (parent gallery — S6 territory if at all)
- `research/problems/erdos-455-oq-04/knowledge.md` (S1 survey — S1 cubic-growth retraction already in this state.md §Honesty correction)

### Drain-wave context (post-claim)

Open PRs at claim time (2026-05-16T00:12Z): **83** (down from ~270 at 22:55Z; 187-PR drop over ~77min via 3 distinct 5-7-PR drain-wave clusters at 22:55Z, 23:26Z, and 00:08Z). Deployer healthy. Last merge #19327 ~4min before claim. This PR's footprint (1 new doc + 2 small admin edits) does not compound the drain.

### Build-verification posture

**No build run this iteration** (doc-only S5 PREP). Last build-verified at iter-4 base via PR #19074 (3061-job Docker clean at v4.26.0). PR #19204 re-verified via mechanic-PR-overlay (apply parent fix → build → revert) — re-confirms 3061-job clean post-S4 ACT.

### Open-PR pre-claim probe

`gh pr list --repo rjwalters/lean-genius --search "erdos-455-oq-04 in:title" --state open` returned **0** open PRs (race-safe). 0 active claims on the slug from other researchers per `claim-problem.sh status`.

### Next action (S5 ACT — gallery integration, recommended Pattern B)

Create child gallery entry at `src/data/proofs/erdos-455-oq-04/`:

1. `meta.json` — see session file §7 for full skeleton.
2. `annotations.json` — line-level Lean annotations for the 8 declarations (~50 LOC).
3. `index.ts` — TS barrel (~5 LOC).

Expected delta: 3 new files, 0 Lean edits, 0 build (or 1 `pnpm build` for gallery validation). `status: "axiomatized"`, `axiomCount: 2`, `badge: "axiom"`, `assumptions: ["Green-Tao 2008 (d=0)", "Bunyakovsky 1857 (d>0)"]`.

## Iteration 4 (researcher-9, 2026-05-14) — S3 ACT BUILD-VERIFY + parent `Erdos455Problem.lean` 3-docstring unblocker

**Outcome**: progress — `Proofs.Erdos455OQ04` is **build-verified at
Mathlib v4.26.0** (3061 jobs clean from worktree CWD). The S3 ACT
build-pending qualifier (PRs #18851, #18590) is retired. Surfaced and
fixed three pre-existing **orphan-`/--` docstring** parser regressions
in the parent file `proofs/Proofs/Erdos455Problem.lean` (lines 54-67,
68-76→79-82, 89-94) per the v4.26.0 strict-parser trap
(`feedback_researcher_mathlib_v426_standalone_docstring_parser_strict.md`).

### What I did

1. **Pre-claim Docker baseline** (worktree CWD per
   `feedback_researcher_docker_build_cwd_must_be_worktree.md`):
   `./proofs/scripts/docker-build.sh Proofs.Erdos455OQ04` →
   `error: Proofs/Erdos455Problem.lean:67:2: unexpected token '/--'; expected 'lemma'`
   plus two more at 82:2 and 94:2. The blocker was the **parent** file,
   not the OQ-04 target.

2. **Diagnosis**. The parent had three orphan `/--` docstring blocks
   that no longer attach to a following declaration:
   - Lines 54-67: docstring describing "Richter's Lower Bound (1976)"
     — the Richter axiom this docstring described was removed in a
     prior commit, leaving the docstring orphan. Now followed by
     another `/--` (which attaches to the `axiom erdos_455_conjecture`
     at line 77).
   - Lines 79-82: docstring "The conjecture is equivalent to..." now
     followed by a non-docstring `/-` comment (line 83), so orphan.
   - Lines 89-94: docstring "**Consequence**: The sequence q_n grows..."
     similarly orphan (next is `/-` at line 95).

3. **Fix**. Three minimal 2-char edits: `/--` → `/-!` on the orphan
   docstrings (the `/-!` form is a parser-recognized "section comment"
   that does NOT need to attach to a declaration). Also amended the
   Richter docstring text to clarify the axiom was removed.

4. **Post-fix Docker rebuild** (worktree CWD, build iter 2):
   `✔ [3061/3061] Built Proofs.Erdos455OQ04 (4.1s)`. Both parent and
   target build clean.

5. **Pre-existing residue**. The parent has one unused-variable linter
   warning at line 129:36 (`unused variable hq`). This pre-dates my
   changes; not my repair scope. Mechanic/doctor sweep territory.

### What this retires

| PR     | Iter    | Layer                                  | Before        | After          |
|--------|---------|----------------------------------------|---------------|----------------|
| #18590 | S2 ACT  | eulerPoly + AP-gap scaffold            | build pending | build verified |
| #18851 | S3 ACT  | `greenTao_finitary` + bridge + k=5     | build pending | build verified |

OQ-04 target: **126 LOC / 0 sorries / 1 axiom (greenTao_finitary) /
3061-job Docker build clean at v4.26.0**.

### Files modified (S3 BUILD-VERIFY + parent unblocker)

- `proofs/Proofs/Erdos455Problem.lean` — 3× 2-char `/--` → `/-!` swap
  at lines 54, 79, 89; +2-LOC clarification on the orphan Richter
  docstring noting the axiom was removed. **Parent file — bundled as
  in-PR build unblocker** per `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md`.
  No declaration-level changes; no semantic shifts.
- `research/problems/erdos-455-oq-04/state.md` — this iteration 4
  section. Header advanced ACT → ACT BUILD-VERIFY / iteration 3 → 4.
- `src/data/research/problems/erdos-455-oq-04.json` — top-level +
  `currentState.phase` synced to `ACT_BUILD_VERIFY` per
  `feedback_researcher_state_sync_misses_top_level_phase.md`; iter 3 → 4,
  `lastUpdated`, focus, blockers, nextAction, builtItems, insights.

### Build-verification posture

Docker build run from worktree CWD per
`feedback_researcher_docker_build_cwd_must_be_worktree.md`:
2 iterations (initial diagnosis surfacing the parent-file blocker,
final fix). Final: `Build completed successfully (3061 jobs).`

### Open-PR pre-claim probe

`gh pr list --search "erdos-455-oq-04 in:title" --state open` returns
**0 open PRs** at claim time (race-safe).

### Next action (S4 PREP — Bunyakovsky-style axiom for d > 0)

Per the prior S3 ACT JSON `nextAction` (preserved):

* State a Bunyakovsky-style axiom — for any irreducible integer
  polynomial `f(n)` of degree ≥ 1 with positive leading coefficient
  and gcd-of-values = 1, infinitely many `n` give prime `f(n)`.
* Specialize to the AP-gap quadratic `q_n = q_0 + n g_0 + binom(n,2) d`
  to derive an `APGapPrimeSeq d` existence statement for arbitrary
  length, conditional on the irreducibility + gcd conditions.
* Bridge theorem analogous to `exists_apGap_zero_of_length`.

Expected ~30-50 Lean lines, 1 new axiom (`bunyakovsky_finitary`),
0 new sorries.

## S3 ACT (researcher-3, 2026-05-13) — Green-Tao axiomatization for `d = 0`

**Outcome**: progress — extended `proofs/Proofs/Erdos455OQ04.lean`
from 84 → 126 LOC (+42 net). Added:
* `axiom greenTao_finitary` — finitary Green-Tao 2008 statement
  (form F1 per S3b PREP §3.1; raw AP triple `∃ a g, 0 < g ∧ ∀ n < k, prime (a + n g)`).
* `theorem exists_apGap_zero_of_length` — bridge from `greenTao_finitary`
  to the slug's `HasAPGaps q 0` predicate (~8 LOC, sorry-free).
* `theorem exists_apGap_zero_length_5_witness` — concrete `(a, g) = (5, 6)`
  certifying the `k = 5` instance `5, 11, 17, 23, 29` without invoking
  the axiom (~6 LOC, sorry-free **and** axiom-free, via `decide`).

Implements the S3b PREP §3.2 axiom signature + bridge verbatim (PR #18736)
plus the §4 optional concrete `k = 5` witness. No edits to the parent's
`exists_length40_apGapPrimeSeq` (S2 ACT) or to `HasAPGaps` / `APGapPrimeSeq`
declarations.

**Counts (post-S3 ACT)**:
* `lineCount`: 84 → 126 (per worktree `wc -l`)
* `theoremCount`: 2 → 4 (added `exists_apGap_zero_of_length`,
  `exists_apGap_zero_length_5_witness`)
* `defCount`: 2 (unchanged — `HasAPGaps`, `eulerPoly`) + 1 structure (`APGapPrimeSeq`)
* `sorryCount`: 0 (unchanged)
* `axiomCount`: 0 → 1 (`greenTao_finitary`; no structure-encoded axioms;
  per §3.1 design, F1 form so no nested-structure axioms)

**Build status**: pending — local Docker build blocked by `.lake` symlink
trap (memory `[.lake symlink loop + mid-build worktree wipe]`). Doctor/
Mechanic verifies on a fresh container.

**Tactics used** (all Mathlib-stable):
* `obtain` for axiom destructuring.
* `push_cast; ring` for `HasAPGaps q 0` discharge (matches
  `eulerPoly_hasAPGaps` from S2 ACT).
* `decide` / `interval_cases` for the `k = 5` concrete witness
  (`5, 11, 17, 23, 29` primality follows from kernel reduction).

**Next**: S4 PREP — Bunyakovsky-style axiom for `d > 0`. The S3b PREP §6.1
recommendation is to **drop the cubic-growth claim** (heuristically false:
prime density for irreducible quadratic `f(n)` is ~`1/log n`, giving
logarithmic-not-cubic growth) and replace with a Bunyakovsky-conjectural
unbounded-length axiom. Out of scope for S3 ACT.

## (Historic) S2 ACT (researcher-5, 2026-05-13) — Euler-polynomial witness scaffold

**Outcome**: progress — new file `proofs/Proofs/Erdos455OQ04.lean`
(~80 LOC, 2 defs + 1 structure + 2 theorems, **0 sorries, 0 axioms**)
landed as the verbatim transfer of S2 PREP §1 (PR #18540) minus the
deferred `apGap_odd_length_le_three` parity-bound. Concretely closes
the parent's `openQuestions[3]` at length 40 via Euler's
`n² + n + 41` polynomial, which has constant second-difference `d = 2`
and is prime for all `n < 40`.

Insertion in `proofs/Proofs.lean`: one new `import Proofs.Erdos455OQ04`
line, alphabetic between `Erdos454ProblemAristotle` and
`Erdos455Problem`.

**Counts**:
* `lineCount`: 0 → ~80
* `theoremCount`: 0 → 2
* `defCount`: 0 → 2 (HasAPGaps, eulerPoly) + 1 structure (APGapPrimeSeq)
* `sorryCount`: 0
* `axiomCount`: 0 (zero `axiom` declarations, zero structure-encoded axioms)

**Build status**: pending — worktree `.lake` symlink trap precludes
local Docker build. Doctor/Mechanic verifies on a fresh container.

**Next**: S2b ACT — `apGap_zero_iff_prime_AP` (~10 LOC) +
`apGap_subsumes_monotone` (~15 LOC) + `apGap_odd_length_le_three`
(~30 LOC, requires `Int.even_sub`). All three sorry-free per
state.md's pre-existing analysis.

## (Historic) Iteration 1 (researcher-10, 2026-05-12) — S1 OBSERVE

**Outcome**: pure survey, no Lean changes. Produced `problem.md`
(~3.0K words, S2–S7 decomposition + Mathlib gap analysis),
`knowledge.md` (~2.5K words, gap-condition hierarchy + manual
length-4+ enumeration), and the initial gallery JSON. Phase NEW →
OBSERVE.

The S1 generalization split:

1. **Constant-gap ($d = 0$)**: primes in arithmetic progression =
   **Green–Tao theorem**. Mathlib lacks Green–Tao; must axiomatise.
2. **AP-gap ($d > 0$)**: a *new* question. S1 conjectured cubic growth
   bound $\Omega(n^3)$. **This claim was retracted in S3b PREP §6.1**
   — see "Honesty correction" below.

S1 technical setup (still valid):
- $g_n = g_0 + n \cdot d$ — linear gap growth.
- $q_n = q_0 + n g_0 + \binom{n}{2} d$ — quadratic in $n$.

## Honesty correction (S3b PREP §6.1, 2026-05-13)

The S1 "cubic growth $\Omega(n^3)$" claim for $d > 0$ is **heuristically
false**. For an irreducible quadratic $f(n) = q_0 + n g_0 + \binom{n}{2} d$
the prime density is conjecturally $\sim 1/\log n$ (Bunyakovsky), giving
logarithmic-not-cubic growth in the number of prime values up to $N$.
The S1 sketch confused growth of the *value sequence* $q_n$ (genuinely
quadratic in $n$) with growth of the *count of primes* below $N$ in
that sequence (logarithmic). S4 drops the cubic axiom and replaces it
with a Bunyakovsky-style unbounded-length axiom.

## Active Approach (S3+)

Two-axiom architecture matching the two subcases:

1. **`greenTao_finitary`** (S3 ACT, landed) — finitary form F1:
   ```
   axiom greenTao_finitary :
     ∀ k, ∃ a g, 0 < g ∧ ∀ n < k, (a + n * g).Prime
   ```
   Bridge: `exists_apGap_zero_of_length : ∀ k, ∃ q, StrictMono q ∧
   (∀ n < k, (q n).Prime) ∧ HasAPGaps q 0` — discharged via `obtain`
   + `push_cast; ring`.
2. **`bunyakovsky_finitary`** (S4 PREP/ACT, planned) — finitary form
   for the AP-gap quadratic specialization:
   ```
   axiom bunyakovsky_finitary :
     ∀ k d, 0 < d →
       ∃ a g, ∀ n < k, (a + n * g + (n * (n - 1) / 2) * d).Prime
   ```
   (sketch — exact signature pending S4 PREP). Bridge: analogous to
   `exists_apGap_zero_of_length`.

Concrete small-length witnesses are axiom-free via `decide`/`native_decide`
(see `exists_apGap_zero_length_5_witness` for the S3 ACT example with
`(a, g) = (5, 6)` certifying `5, 11, 17, 23, 29`).

## Blockers

None mathematical. Practical:

- **Green–Tao 2008 absent from Mathlib**: axiomatised in S3 ACT
  (`greenTao_finitary`). The 30+-page proof is not Mathlib-reachable
  in any single iteration.
- **Bunyakovsky absent from Mathlib**: will be axiomatised in S4.
  Conjectural; no proof exists in any system.
- **Worktree `proofs/.lake` symlink-loop trap**: precludes local
  Docker build. Doctor/Mechanic verifies on a fresh container.
- **`status: "axiomatized"` is mandatory** — both Green-Tao and
  Bunyakovsky are unproved conjectures (Green-Tao d=0 case is the
  ONLY case with an actual proof — but the proof is far beyond
  Mathlib).

## Next Action

**S5 ACT (any researcher, doc-only — Pattern B child gallery entry)**:
S4 PREP (PR #19149) **MERGED** 2026-05-15T22:57:22Z. S4 ACT (PR #19204)
**MERGED** 2026-05-15T18:06:38Z. Both axioms (`greenTao_finitary` for
d=0 and `bunyakovsky_finitary` for d>0) plus bridges are live in
`proofs/Proofs/Erdos455OQ04.lean` at 166 LOC, build-verified via
PR #19074 (3061-job Docker clean at v4.26.0).

S5 ACT scope (Pattern B — new child gallery entry):

1. Create `src/data/proofs/erdos-455-oq-04/meta.json` per the S5 PREP
   skeleton (session file §7).
2. Create `src/data/proofs/erdos-455-oq-04/annotations.json` with
   line-level Lean annotations.
3. Create `src/data/proofs/erdos-455-oq-04/index.ts` (TS barrel).

`status: "axiomatized"`, `axiomCount: 2`, `badge: "axiom"`,
`assumptions: ["Green-Tao 2008 (d=0)", "Bunyakovsky 1857 (d>0)"]`.

Expected delta: 3 new files, 0 Lean edits, 0 build (or 1 `pnpm build`).

**S6 (optional)**: ship the parent `src/data/proofs/erdos-455/meta.json`
`openQuestions[3]` entry update to point at the new OQ-04 child entry.
Strictly orthogonal to S5 ACT — can ship same PR or follow-up.

**S7 (optional)**: extend `exists_length40_apGapPrimeSeq` with parallel
witnesses for other-d records (e.g. Lukasiewicz d=4 length 27). Lean
only; out of scope here.

## Honesty

S3 ACT delivers:
- 0 new sorries; 1 new axiom (`greenTao_finitary`); 2 new theorems.
- Lean file Erdos455OQ04.lean: 84 → 126 LOC.
- Build pending (worktree `.lake` symlink-loop trap).

The S1 cubic-growth claim is retracted (see "Honesty correction"
above). The post-S3 architecture is honest: two axiomatized cases
(Green-Tao d=0, Bunyakovsky d≥1 — the latter pending S4) plus
axiom-free decidable certifications for small concrete witnesses.

The final Lean entry will be `status: "axiomatized"` because BOTH
Green-Tao and Bunyakovsky are unprovable in any Mathlib-bounded
formalization. Concrete small-length results (the `k=5` witness) are
genuinely verified (no axiom dependency).
