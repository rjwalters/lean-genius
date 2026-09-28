---
name: project-migrate
description: Migrate existing studio projects to the post-#295 / post-#296 project-org model (BRIEF.md absorbs all config; `<project>/<slug>/<slug>.<N>/` shape; body filename echoes slug).
domain: anvil
type: skill
user-invocable: true
---

# anvil:project-migrate — Bridge existing projects to the new model

The `project-migrate` skill is a one-shot bridge tool: given a path to a studio
project that pre-dates the issue #295 / #296 contract, it migrates the project
in place to the canonical post-#295 / post-#296 shape:

```
<project>/
  BRIEF.md                  # ONE project brief absorbing all anvil config
  <slug>/
    <slug>.1/
      <slug>.md             # body filename echoes the slug
      _progress.json
      ...
    <slug>.2/
      <slug>.md
      ...
    <slug>.N/
  research/                 # shared evidence pool (untouched)
  refs/                     # shared per-project references (optional, untouched)
```

The migration tool exists because issues #295 and #296 changed the contract that
every existing studio project depended on. Without a bridge, every existing
project becomes silently broken at the first revise after the contract change.

## What this skill does

`project-migrate` is **opinionated, idempotent, and dry-run first**. It:

- **Detects** the current on-disk shape by walking the project tree.
- **Plans** the per-document migration steps (rename + content rewrite).
- **Applies** the plan atomically per document — a failure in doc B does not
  half-migrate doc A.
- **Verifies** by re-running `discover_thread_root` + `load_project_brief` on
  the result.

There are **no back-compat flags**. The skill exists to converge existing
projects onto one shape; it does not preserve the legacy shape under any
option. If a consumer needs to keep the legacy layout, they should not run the
migration.

## Recognized current shapes

The detector recognizes three pre-migration shapes. **Deck, slides, and
proposal threads are in scope** alongside memo (issue #382 — the parallel
rollout of the #295/#296 model to the other rich-command-set skills):

1. **Pre-#283 classic** — `memo.N/` siblings of the portfolio dir, optional
   per-thread `BRIEF.md`, skill-fixed `memo.md` body. No project-level
   `BRIEF.md`. This shape ALSO covers the **nested-but-flat**
   deck/slides/proposal variant (the studio canary's `series-a-deck`
   shape): a thread-root directory (`<slug>/` carrying the thread-level
   BRIEF + refs + assets and optionally a per-thread `.anvil.json`)
   sitting as a SIBLING of flat `<slug>.N/` version dirs at the project
   root. The migration moves the version dirs (and critic siblings) IN
   under the thread root; the thread-root contents stay where they are
   (the studio hand-fix `2cf3f37` is the reference shape).

   **Bare sub-state (issue #408).** A pre-#283 classic project with NO
   anvil config anywhere — no project BRIEF, no `.anvil.json`, no
   skill-fixed or retained body filenames — is the **bare** shape: a
   hand-rolled workflow that independently converged on the
   `{thread}.{N}/` + `.review`/`.audit` grammar (e.g. `<slug>.N/`
   dirs carrying `paper.tex` bodies, version gaps tolerated). Bare
   projects classify and migrate as PRE_283_CLASSIC, but the project
   BRIEF is **synthesized** from observed state (there is nothing to
   merge from): every inferred or defaulted frontmatter value carries
   a `# TODO(operator)` YAML comment, the BRIEF body carries a
   mirrored operator-confirmation checklist (body prose survives
   future BRIEF rewrites verbatim; YAML comments survive the no-op
   idempotent path), and the dry-run report prints the full proposed
   BRIEF text through the same `render_project_brief` code path the
   apply step writes. Synthesis is automatic when the bare sub-state
   is detected — dry-run-by-default is the safety surface; no extra
   flag.
2. **Post-#283 with `.anvil.json`** — project root with `BRIEF.md` listing
   `documents:`, per-thread directories under
   `<project>/<slug>/<slug>.N/memo.md`, separate per-thread `.anvil.json`
   files carrying `target_length` / `target_length_overrides` /
   `rubric_overrides` (or, on deck threads, the paired `max_iterations` +
   `iteration_cap_rationale` override). Mixed-grammar projects — a
   BRIEF-bearing project where some threads are nested and others still
   sit flat — dispatch per thread: flat threads get the nesting move,
   nested threads get the in-place cleanup.
3. **Fully-migrated** — project root, `BRIEF.md` absorbs all per-doc config,
   no skill-fixed body filename remains. This is the target shape; the
   migration is a no-op on this input (idempotence contract).

**Body filenames per skill.** Memo bodies are renamed to the slug-echo
shape (`memo.md` → `<slug>.md`). Deck/slides (`deck.md`) and proposal
(`proposal.tex`) **retain their skill-fixed body filenames** — the
slug-echo rename is scoped out for those skills because the filenames
are consumed by external tooling (marp CLI, xelatex,
`anvil-proposal.cls`); see the per-skill SKILL.md body-filename notes
(issue #382). The migration for those skills is directory nesting plus
`.anvil.json` → BRIEF merge only.

**Artifact types.** The registered artifact-type enum
(`anvil/lib/project_brief.py::ArtifactType`) carries skill-identity
values `deck`, `slides`, `proposal` (issue #386), and `paper` (registered as `pub`, issue
#408) alongside the memo subtypes. The migration infers the type from
the retained body filename and writes it into the BRIEF `documents:`
entry: `deck.md` → `deck`, `proposal.tex` → `proposal`. Threads with
no retained body (memo-shaped `.md` bodies) default to
`artifact_type: investment-memo`.
The plan surfaces an inference note on every retained-body thread —
including `.tex`-bodied proposal threads — and the deck note flags the
deck-vs-slides ambiguity: `anvil:slides` threads also use `deck.md`, so
body shape alone cannot distinguish them; edit the BRIEF entry to
`slides` for a talk deck.

On **bare** threads (issue #408) the inference extends to observed
non-`.md` bodies (`*.tex`): a body with
`\documentclass{anvil-proposal}` infers `proposal`; any other
`\documentclass` infers `paper`; markdown-bodied bare threads keep the
`investment-memo` default. Every bare inference — including the
default — is paired with a `# TODO(operator)` confirmation marker;
nothing is guessed silently. Observed body filenames (e.g.
`paper.tex`) are **recorded but never renamed** — the #382 slug-echo
carve-out applies because root-level build artifacts
(`paper.tex`/`paper.pdf`) are direct evidence that external tooling
consumes the fixed name; the plan emits a deferral note instead.
Existing `.review`/`.audit` sidecars rename cleanly with the thread;
hand-rolled unstamped review content stays invisible-but-intact to
`discover_critics` per the #346 additive contract (rebackportable via
`anvil:rubric-rebackport`).

**Foreign `.md` body filenames + `--artifact-type` (issue #878).** A
bare thread's `.md` body may carry a name fixed by a FOREIGN pipeline
(e.g. a hand-rolled blog tool's `post.md` — the shape `anvil:essay`
documents as its migration path) rather than any anvil skill's *own*
historical fixed name. Two independent gaps this closes:

1. **Circular declaration.** The bare-synthesis default is always
   `artifact_type: investment-memo` (TODO-marked), because the correct
   declaration (e.g. `artifact_type: essay`) can only come from the very
   BRIEF the run is synthesizing. `--artifact-type <type>` (validated
   against the same two-tier `#394` registry `--enroll`/`--adopt-vn`
   use) breaks the circularity: given on the main mode, it is applied
   directly to every synthesized `documents:` entry with **no** TODO
   marker — the operator's explicit declaration, not a guess.
2. **Nothing to rename.** `_SKILL_FIXED_BODY_FILENAMES` only recognizes
   anvil's own prior fixed names (`memo.md`, `proposal.md`, ...) — a
   foreign name like `post.md` matches none of them, so the historical
   rename loop has nothing to match. The planner separately detects a
   **single consistent** non-canonical `.md` filename across a bare
   thread's version dirs and plans its rename to `<slug>.md`,
   independent of whether `--artifact-type` is given — reviewable in the
   dry-run plan, paired with a `# TODO(operator)` confirmation note.
   Multiple distinct foreign names across the thread's version dirs are
   ambiguous: no rename is planned, and the plan notes it instead of
   guessing.

The bare-shape definitional edge case this resolves (curator note): a
project with no anvil config anywhere but a foreign pipeline's fixed
body name still classifies BARE (`ProjectInventory.is_bare` is
unaffected — a foreign name is not one of anvil's own skill-fixed or
retained names), and the rename mechanism now recognizes that same
foreign name as the thread's sole body candidate rather than having
nothing to match.

## Commands

| Command                                     | What it does                                                                                  |
|---------------------------------------------|-----------------------------------------------------------------------------------------------|
| `/anvil:project-migrate <project-dir>`      | **Dry-run.** Detect current shape, emit a per-doc migration plan. **No mutations** to disk.   |
| `/anvil:project-migrate <project-dir> --apply` | Execute the plan atomically per doc. Use `git mv` when the project is under git.           |
| `/anvil:project-migrate <project-dir> --report` | Emit a markdown report only (no plan, no mutations). Useful for portfolio surveys.        |
| `/anvil:project-migrate --enroll <file> [...]` | **Single-file enrollment** (issue #406): wrap loose `.md`/`.tex` files into project threads. Dry-run by default; `--apply` executes. Optional `--project <dir>`, `--slug <slug>`, `--artifact-type <type>`. |
| `/anvil:project-migrate --adopt-vn <dir>` | **vN report-dir adoption** (issue #432 Phase 1): adopt a foreign `v{N}/` family (+ `v{N}.review/` siblings) into `<project>/<slug>/<slug>.{N}/`. Dry-run by default; `--apply` executes. Optional `--slug <slug>`, `--artifact-type <type>`. |
| `/anvil:project-migrate --adopt-family <dir> --tag-map <file> --artifact-type <type>` | **Letter-family adoption** (issue #440 — Phase 2 of #432): adopt foreign `{Project}.{Letter}.{N}` families (+ foreign-tagged critic siblings, mapped declaratively) into `<dir>/<slug>/<slug>.{N}/`. Dry-run by default; `--apply` executes. Slugs are derived (no `--slug`); `--artifact-type` is REQUIRED. |
| `/anvil:project-migrate --adopt-review <dir>` | **Foreign `review.md` stub conversion** (issue #454 — Phase 3a of #432): on an already-adopted tree, convert each `<slug>.{N}.<tag>/` critic sibling holding only a single-file prose `review.md` into a recognizable-but-explicitly-**unscored** `_review.json` stub (+ `_meta.json` foreign-provenance marker), preserving `review.md` byte-identical. **NO LLM, NO synthesized scores.** Dry-run by default; `--apply` executes. |
| `/anvil:project-migrate --adopt-review <dir> --rescore` | **Operator-driven LLM rescore of stubs** (issue #507 — Phase 3b of #432): on a tree carrying Phase-3a stubs, resolve each stub's target anvil rubric and (with the operator/LLM step in the slash-command runtime supplying per-dimension scores) turn the unscored stub into a real scored `_review.json` (`unscored: false`), stamping `rubric_id` / `rubric_total` / `advance_threshold` + `rescored_from: foreign-adopted` lineage; `review.md` byte-identical. Unresolvable stubs are SKIPPED, never guessed. Dry-run by default; `--apply` (operator-gated) executes. |

All three main-mode forms in the table above (dry-run, `--apply`,
`--report`) accept an optional `--artifact-type <type>` (issue #878):
applied to every synthesized `documents:` entry on a BARE project
instead of the inferred/defaulted value — closing the circularity where
the correct declaration (e.g. `artifact_type: essay`) would otherwise
have to come from the very BRIEF the run is synthesizing. See "Bare
sub-state" below.

See `commands/project-migrate.md` for the operator-facing contract.

## Single-file enrollment (`--enroll`, issue #406)

Adoption-target monorepos hold hundreds of **loose single-file
documents** (flat `.md`/`.tex` files in topical directories, often
date-prefixed or date-suffixed). Enrollment is the path from a bare
file to a thread:

- The file moves to `<project>/<slug>/<slug>.1/<slug>.<ext>` (`git mv`
  in-repo so history follows). `.tex` bodies slug-echo too — new
  enrollments have no external-tooling carve-out; the enclosing move
  already breaks any path-based consumer, so a plan note records the
  rename instead.
- The slug derives from the filename (lowercased, hyphens, ISO date
  prefix/suffix stripped); the stripped date is preserved as a YAML
  comment on the BRIEF entry (`# enrolled-from: <file> (date: ...)`)
  and as a body `## Enrollment log` line (body prose survives future
  BRIEF rewrites; YAML comments do not). `--slug` must already be
  canonical — it is rejected, never silently re-sanitized.
- **Existing BRIEFs are extended by surgical textual append**, never
  re-rendered: the migrate-mode re-render path is lossy (it drops
  top-level `theme:`, per-doc `render_*` / `latex_header_includes`
  keys, every YAML comment, quoting style, and entry order), so the
  enroll path inserts the new entry lines at the end of the
  `documents:` block and leaves every other byte untouched. With no
  enclosing BRIEF, a minimal one is synthesized through the same
  `render_project_brief` path as bare-project migration (#408 TODO
  discipline). Both paths are strict-validated post-write and rolled
  back on failure.
- Artifact types come from `--artifact-type` (two-tier validation per
  #394) or are inferred with a `# TODO(operator)` marker (`.md` →
  `investment-memo`; `.tex` → `proposal`/`paper` from `\documentclass`).
- Batch form: N files enroll into ONE project as N independently
  planned documents. Plan-time errors (slug collisions, non-md/tex,
  already-enrolled inputs, malformed BRIEF) abort pre-mutation;
  apply-time failures isolate per doc with the BRIEF written for the
  succeeded subset. Re-enrolling an enrolled file is a refusal, not a
  duplicate.

## vN report-dir adoption (`--adopt-vn`, issue #432 Phase 1)

Adoption-target repos also hold **foreign vN report-dir families**
(`projects/<proj>/reports/v{N}/` + `v{N}.review/` siblings — ~213
entries across the sphere survey). `project-scout`'s foreign-grammar
guard correctly refuses to recommend a migrate on them; `--adopt-vn`
is the conversion path:

- One family per invocation: `v{N}/` → `<project>/<slug>/<slug>.{N}/`
  and `v{N}.<tag>/` → `<slug>.{N}.<tag>/` (`git mv` in-repo). The slug
  defaults to the sanitized enclosing-dir name (`reports`); `--slug`
  must already be canonical (rejected, never re-sanitized).
- Version gaps tolerated. Stray non-versioned dirs (and orphan
  sidecars) are left untouched and reported. Bodies inside version
  dirs are recorded but **never renamed** (the #408 carve-out).
- Minor-versioned oddballs (`v14.1`) are a plan-time, pre-mutation
  refusal naming each offending dir with a suggested manual target
  (the next free integer) — Phase 1 is strictly mechanical and
  operator-confirmable.
- BRIEF handling mirrors enrollment: surgical append into an existing
  project BRIEF (#406/#416), starter synthesis with `# TODO(operator)`
  markers otherwise (#408). Strict-validated post-write with rollback;
  the dry-run preview is byte-identical to the apply-time write.
- Artifact type: `--artifact-type` (two-tier #394 validation) or
  inferred `report` with a TODO marker (`report` is a registered
  skill-identity artifact type as of #432, the #408 `pub`/`paper` precedent).
- Post-adopt names pass project-scout's foreign-grammar guard clean;
  re-running on an adopted tree is a no-op.

## Letter-family adoption (`--adopt-family`, issue #440 — Phase 2 of #432)

Adoption-target repos also hold **foreign letter-family ip threads**
(`{Project}.{Letter}.{N}` — `Meridian.C.7/` +
`Meridian.C.7.enablement/` siblings, ~163 version dirs across the
sphere survey). `--adopt-family` is their conversion path:

- One invocation = one directory = N letter families (batch): each
  `{Project}.{Letter}` stem becomes one document —
  `{stem}.{N}/` → `<dir>/<slug>/<slug>.{N}/` with the slug **derived**
  from the stem (`Meridian.C` → `meridian-c`; deliberately no `--slug`
  in this mode). Plan-time errors abort the whole batch pre-mutation;
  apply-time failures isolate per family with the BRIEF written for
  the succeeded subset.
- **Declarative sidecar tag mapping (`--tag-map <file>`)** — the
  binding spec is the issue #432 curation comment: JSON
  `{"tag_map": {"<foreign>": "<canonical>", ...}}`, REQUIRED whenever
  any renameable critic sidecar is observed; every observed tag MUST
  have an entry (unmapped tag = refusal LISTING the tags; identity
  mappings expected — `"s101": "s101"`); values must be a single
  dot-free word with no `-vN` suffix; two foreign tags → one canonical
  tag on the SAME version dir is a refusal (the same pair on different
  dirs is legal); the dry-run report prints the full per-directory
  resolution. NO heuristics, ever. The versioned tags `--adopt-vn`
  refuses (`review-v2`) become mappable here.
- **`--artifact-type` is REQUIRED, invocation-wide**: there is no safe
  inference between `ip-uspto` and `ip-uspto-provisional` (both
  registered skill-identity artifact types as of #440). Every BRIEF
  entry carries a `# TODO(operator): confirm — applied
  invocation-wide by --adopt-family` marker; per-family divergence is
  a cheap post-adopt BRIEF edit.
- BRIEF handling, strays/orphans reporting, the never-rename-bodies
  carve-out, `git mv`, strict post-write validation with rollback, the
  byte-identical dry-run BRIEF preview, idempotent re-runs, and the
  clean post-adopt foreign-guard pass all mirror `--adopt-vn` above.
- Renamed sidecars holding only a single-file `review.md` payload stay
  **invisible-but-intact** to `discover_critics` (the #346 additive
  contract); content conversion to a recognizable review payload is
  **Phase 3a** (`--adopt-review`, issue #454 — see next section;
  `anvil:rubric-rebackport` does not apply: it targets anvil-shaped
  legacy reviews only).

## Foreign `review.md` stub conversion (`--adopt-review`, issue #454 — Phase 3a of #432)

Phases 1–2 make foreign version-dir and critic-sibling **names**
canonical. `--adopt-review` is the deferred **content** step: it converts
a foreign critic sibling's single-file prose `review.md` into a payload
`anvil/lib/critics.py::discover_critics` recognizes — so the review
history becomes visible to the reviser. It runs **standalone on an
already-adopted tree** (single responsibility; compose with
`--adopt-family` via two operator runs), touches **no `BRIEF.md`**, and is
**dry-run by default**.

**Honest scope: STUB conversion, NOT prose→score extraction.** Foreign
`review.md` payloads (sphere `.enablement` / `.s101` / `.fto` / `.critic`
/ `.audit2` / `.pre_flight` siblings) were **never scored on any anvil
rubric** — there is no per-dimension table, no `Total: X/Y`, no
`advance: true|false` to parse. Synthesizing /44 scores from foreign prose
would be **fabrication**, and a deterministic pass cannot do it honestly.
So this mode does the minimal honest thing per sidecar:

- Write a canonical `_review.json` that is **recognizable-but-explicitly-
  unscored**: empty `scores` / `findings` / `critical_flags`; null
  `total` / `threshold` / `verdict`; `unscored: true` (the one schema flag
  that lets `scores` be empty — issue #454 added it to `review_schema.py`,
  additive, absent = byte-identical).
- Write a sibling `_meta.json` foreign-provenance marker
  (`{"source": "foreign-adopted", "unscored": true, "origin_filename":
  "review.md", "adopted_by": "anvil:project-migrate#454"}`) so a reader
  distinguishes an unscored-foreign stub from a real review.
- Preserve the original `review.md` **byte-identical** — the stub is
  purely additive. All writes go through
  `anvil/lib/sidecar.py::staged_sidecar` (per-sidecar atomic, crash-safe;
  the live dir is moved aside and restored untouched on any mid-write
  failure).

**NO LLM call. NO score synthesis.** Idempotent: a sidecar that already
carries `_review.json` is skipped (re-run = empty plan). An empty-scores
stub passes `_has_recognizable_review` and feeds `aggregate`, contributing
**zero dimensions** — it never corrupts a real co-sibling's total or flips
its verdict (regression-locked in the discovery test).

## Phase 3b: operator-driven LLM rescore (`--adopt-review --rescore`, issue #507)

Phase 3b turns a Phase-3a **unscored stub** into a **real scored review**.
It is an opt-in `--rescore` modifier on `--adopt-review`, **NOT** a
`rubric-rebackport` extension — three code-grounded reasons (issue #507
curation): (1) rubric-rebackport's detector only matches `.review`
siblings, not the `.enablement` / `.s101` / `.fto` critic tags foreign
stubs live on; (2) its `--rescore` requires a prior anvil score (to record
a prior→new delta) a never-scored stub lacks; (3) the stub already carries
its own `source: foreign-adopted` input marker at the project-migrate seam
that wrote it.

The scoring itself is an **operator-driven LLM step that stays in the
slash-command runtime** (the exact precedent in
`anvil/skills/rubric-rebackport/lib/rescore.py`: "the actual LLM call
belongs in the consumer's slash-command runtime, not in this Python
library"). The Python here is a thin **planner + marker-flip +
atomic-write** harness:

- **Plan** (`build_rescore_plan`): scan for sidecars carrying a Phase-3a
  stub (`_review.json` `unscored: true` + `_meta.json`
  `source: foreign-adopted`); resolve each stub's target anvil rubric
  (BRIEF `documents:` block → body-filename fallback). A stub whose rubric
  cannot be resolved is **SKIPPED with an operator-visible note — never
  guessed** (the honesty guard).
- **Operator/LLM hand-off**: the runtime reads the verbatim `review.md` +
  resolved rubric and produces per-dimension scores (an
  `adopt_review.ScoredReviewInput`).
- **Write back** (`apply_rescore_plan`, `--apply` only): per-sidecar
  atomic via `staged_sidecar` (reusing Phase 3a's staged/backup/swap so
  `review.md` stays byte-identical). Replaces `_review.json` with a scored
  `Review` (`unscored: false`; `total` / `threshold` / `verdict` derived
  from the supplied scores), and updates `_meta.json` to flip
  `unscored: false`, add `rescored_from: foreign-adopted` (retaining
  `origin_filename`), and stamp the v0.4.0 per-review rubric fields
  `rubric_id` / `rubric_total` / `advance_threshold`. A target with no
  supplied score is left as an honest stub — the harness NEVER fabricates
  scores. The `--apply` operator gate is binding: `--rescore` never runs
  silently as part of `--adopt-review` / `--adopt-family`.

## Atomicity & rollback

The skill applies its plan one document at a time. Within a single doc, the
sequence is:

1. Compute the new layout (target paths for every file the doc owns).
2. Perform the renames + content rewrites.
3. If any step fails, roll back the doc's changes from a per-doc snapshot
   taken before the apply began (the snapshot lives at `.anvil-migrate-rollback/<slug>/`
   under the project root and is removed on successful apply).

Failures in doc B do not affect already-migrated docs A. A partial apply on
doc B is rolled back before the skill moves on (or surfaces the error and
stops, depending on the failure mode).

## Idempotence

Re-running `--apply` on a project that has already been migrated is **zero
diff**: the detector reports the project as fully-migrated and the planner
emits an empty plan. The verify step then succeeds without writing.

This is the **canonical safety net** for operators who lose track of which
projects they've already migrated.

## Cross-thread reference rewriting

The plan walks every `<slug>.md` body for cross-thread references using the
old `memo.N` shape (e.g., "see `memo.7` §3"). When found, the planner emits a
content-rewrite step that updates the reference to the new `<slug>.N` shape.
This handles the canary case where multiple `memo.N` versions of a single
thread inadvertently cite one another.

## Relationship to `anvil/skills/memo/lib/migrate.py`

The memo-side LaTeX bootstrap helper (`migrate.py`) currently writes a legacy
`.anvil.json` file when ingesting a LaTeX memo source. Per the carve-out from
issue #296's judge review, this skill **runs as a post-step** to that helper:
an operator who runs `memo-migrate` to ingest a LaTeX source produces a
`.anvil.json`-shaped thread; running `project-migrate --apply` on the
resulting portfolio merges the `.anvil.json` into the project `BRIEF.md`.

A future refactor may retarget `memo-migrate` to write `BRIEF.md` directly;
for now the two skills compose cleanly under the post-step model, and
`project-migrate`'s idempotence means re-running it is safe.

## State machine

The skill does not produce a versioned artifact. It runs to completion as a
one-shot. The on-disk evidence is the rewritten project tree itself.

## Tests

Fixtures are programmatic builders in `tests/_fixtures.py` (trees are
constructed in tmp dirs rather than baked on disk):

- `build_pre_283_classic` — pre-#283 layout (memo.N siblings, no project
  BRIEF, `memo.md` bodies).
- `build_post_283_anvil_json` — post-#283 with `.anvil.json` (project BRIEF +
  per-thread `.anvil.json`).
- `build_fully_migrated` — target shape (no-op test).
- `build_foundry_shaped` — sanitized multi-thread snapshot exercising the
  canary case (multiple `memo.N` versions, critic siblings).
- `build_beacon_shaped_deck` — sanitized snapshot of the studio's
  pre-`2cf3f37` deck thread (thread root with BRIEF + refs + assets +
  `.anvil.json` as a sibling of flat version dirs; issue #382).
- `build_mixed_memo_deck_proposal` — the mixed-skill canary case: one
  project root with flat memo + deck + proposal threads (issue #382).
- `build_bare_version_dir_threads` — the bare adoption-target shape
  (issue #408): `.tex` bodies, version gaps {1,3,4,5,6,7}, mixed
  hand-rolled `.review`/`.audit` sidecars, root-level
  `paper.tex`/`paper.pdf` build artifacts, `figures/`.
- `build_bare_foreign_md_body_threads` — the `anvil:essay`
  adoption-target shape (issue #878): a bare thread whose `.md` body is
  a foreign pipeline's fixed name (`post.md`), not any anvil skill's
  own historical fixed name.
- `build_bare_ambiguous_md_body_threads` — a bare thread whose version
  dirs disagree on the foreign body filename (`post.md` vs `draft.md`)
  — the ambiguous case the single-candidate constraint refuses to guess
  at (issue #878).
- `build_loose_file_in_existing_project` — migrated project with a
  tripwire-laden operator BRIEF (`theme:`, `render_*` keys, YAML
  comments, quoting, non-alpha entry order) + a dated loose file
  (issue #406).
- `build_loose_file_no_project` — bare topical dir with date-prefixed
  and date-suffixed loose files (issue #406).
- `build_loose_file_batch` — batch of loose files incl. a `.tex` with
  `\documentclass`, an intra-batch slug-collision pair, and a
  non-md/tex refusal target (issue #406).
- `build_vn_report_dirs` — the foreign vN report-dir family (issue
  #432): `v{N}/report.md` dirs with a gap, `v{N}.review/` siblings, a
  stray non-versioned dir, optional `v14.1` minor oddball and optional
  enclosing operator BRIEF.

Test files:

- `test_project_migrate_detect.py` — shape detection across all fixtures.
- `test_project_migrate_plan.py` — per-shape plan generation.
- `test_project_migrate_apply.py` — apply correctness, atomicity, rollback.
- `test_project_migrate_dry_run.py` — snapshot-and-diff: dry-run
  leaves the input byte-identical.
- `test_project_migrate_idempotent.py` — apply on fully-migrated input is a
  no-op (zero diff).
- `test_project_migrate_verify.py` — post-apply the project rounds-trips
  through `discover_thread_root` + `load_project_brief` (incl. the mixed
  fixture through the promoted `anvil.lib` primitives).
- `test_project_migrate_detect_mixed.py` — nested-but-flat + mixed-skill
  classification and inventory (issue #382).
- `test_project_migrate_plan_mixed.py` — nesting renames, critic-sibling
  moves, retained-body no-rename, iteration-cap pair extraction.
- `test_project_migrate_apply_mixed.py` — nested tree correctness +
  cross-skill discovery smoke through `anvil.lib.project_discovery`.
- `test_project_migrate_idempotent_mixed.py` — re-apply on a migrated
  mixed project is zero diff.
- `test_project_migrate_bare.py` — bare sub-state (issue #408):
  characterization lock (PRE_283_CLASSIC), artifact-type inference +
  TODO markers, dry-run BRIEF preview, apply + post-apply contracts
  (`discover_thread_root`, strict load, verify, `discover_critics`
  excludes unstamped sidecars), byte-identical idempotence.
- `test_project_migrate_foreign_body.py` — foreign `.md` body rename +
  `--artifact-type` on the bare main mode (issue #878): single- vs
  multi-candidate detection, dry-run rename plan (post-move path
  correctness), `--artifact-type` closing the circularity with no TODO
  marker, `PlanError` on an unregistered value pre-mutation, end-to-end
  apply + `discover_thread_root`/`verify_migration`, idempotence.
- `test_project_migrate_enroll_slug.py` — slug derivation + canonical
  `--slug` validation (issue #406).
- `test_project_migrate_enroll_append.py` — surgical-append byte
  preservation against the tripwire BRIEF + strict re-parse + append
  refusal cases (issue #406).
- `test_project_migrate_enroll_apply.py` — enroll end-to-end: existing
  project, no-project synthesis, batch, `.tex` inference, git-mv
  history follow, per-doc failure isolation with succeeded-subset
  BRIEF write (issue #406).
- `test_project_migrate_enroll_errors.py` — plan-time hard errors
  (collisions, refusals, idempotency-as-refusal, malformed BRIEFs,
  flag validation) all pre-mutation (issue #406).
- `test_project_migrate_enroll_dry_run.py` — dry-run default leaves
  the tree digest unchanged; the previewed BRIEF is byte-identical to
  the apply-time write (issue #406).
- `test_project_migrate_adopt_vn_detect.py` — vN family grouping (gap
  tolerated), minor-oddball + versioned-tag refusals, stray/orphan
  reporting, `Shape.ADOPT_VN` plan-mode-only regression (issue #432).
- `test_project_migrate_adopt_vn_plan.py` — renames incl. sidecars,
  slug default/override/refusal, artifact-type inference + two-tier
  validation, collision refusals, BRIEF preview (issue #432).
- `test_project_migrate_adopt_vn_apply.py` — end-to-end synth + append
  paths, strict round-trip + `discover_thread_root`, git-mv history,
  injected-failure rollback (issue #432).
- `test_project_migrate_adopt_vn_dry_run.py` — dry-run default leaves
  the tree digest unchanged; preview == apply-time BRIEF write (issue
  #432).
- `test_project_migrate_adopt_vn_idempotent.py` — re-run after adopt
  is a no-op; post-adopt names pass project-scout's
  `find_foreign_families` clean (issue #432).
- `test_project_migrate_adopt_family_detect.py` — letter-family
  grouping by `{Project}.{Letter}` stem (gap tolerated), strays /
  orphan sidecars / numeric-tag oddballs reported-untouched,
  `Shape.ADOPT_FAMILY` plan-mode-only regression (issue #440).
- `test_project_migrate_adopt_family_tag_map.py` — the declarative
  tag-map contract: all four refusal classes (missing map, unmapped
  tags listed, non-canonical values, same-dir collision), cross-dir
  acceptance, identity + `review-v2` remaps, file-shape refusals
  (issue #440).
- `test_project_migrate_adopt_family_plan.py` — multi-family
  DocumentPlans with derived slugs (no `--slug`), REQUIRED
  invocation-wide `--artifact-type` (refusal names the ip
  candidates; both ip types registered), collision refusals, BRIEF
  preview + resolution table in the report (issue #440).
- `test_project_migrate_adopt_family_apply.py` — end-to-end synth +
  append paths incl. sidecar renames per the map, strict round-trip +
  `discover_thread_root`, git-mv history, per-family
  injected-failure rollback with succeeded-subset BRIEF write
  (issue #440).
- `test_project_migrate_adopt_family_dry_run.py` — dry-run default
  leaves the tree digest unchanged; full tag resolution printed;
  preview == apply-time BRIEF write (issue #440).
- `test_project_migrate_adopt_family_idempotent.py` — re-run after
  adopt is a no-op; post-adopt names pass `find_foreign_families`
  clean on all three predicates; `review.md`-only sidecars stay
  undiscovered by `discover_critics` (#346 regression) (issue #440).
- `test_project_migrate_adopt_review_detect.py` — finds `review.md`-only
  sidecars under an adopted tree; ignores already-converted
  (`_review.json`-present) and real scored siblings; never treats version
  dirs / bodies as sidecars (issue #454).
- `test_project_migrate_adopt_review_plan.py` — stub paths planned;
  `review.md` recorded as PRESERVED (never a rename source); the stub
  `Review` is unscored/empty and validates against `review_schema`; the
  provenance marker shape is pinned (issue #454).
- `test_project_migrate_adopt_review_apply.py` — `_review.json` +
  `_meta.json` written via `staged_sidecar`; `review.md` byte-identical
  pre/post (hash compare); injected mid-write failure restores the dir
  untouched; whole-batch failure leaves the tree byte-identical
  (issue #454).
- `test_project_migrate_adopt_review_dry_run.py` — dry-run default leaves
  the input tree byte-identical (snapshot-and-diff); the report names the
  conversions and the "no LLM / no synthesized scores" contract
  (issue #454).
- `test_project_migrate_adopt_review_idempotent.py` — second `--apply`
  yields an empty plan, zero diff (issue #454).
- `test_project_migrate_adopt_review_discovery.py` — post-apply
  `discover_critics` finds the converted sidecar, `load_review` parses the
  stub, and `aggregate([stub, real_sibling])` does NOT corrupt the real
  sibling's total or flip its verdict (the zero-dimension-tolerance check
  — the load-bearing risk) (issue #454).
- `test_project_migrate_adopt_review_doc.py` — pins the `--adopt-review`
  flag, the "no LLM / no synthesized scores" contract, the stub field
  set, and the Phase 3a/3b split (issue #454).

## Git sync hook (opt-in, off by default)

Consumers running anvil under an external orchestrator (a sphere channel-agent, a Loom-style daemon) can opt in to a per-phase git commit hook so every write-bearing run leaves the working tree clean: a repo-level `.anvil/config.json` with `git.commit_per_phase: true` (and optionally `git.push: true`) has the `project-migrate` command end its run by staging only the paths it wrote and committing as `anvil(project-migrate/apply): <project> [MIGRATED]`. The full contract — knob shape, defaults-off rule, commit-message format, staging scope, and warn-and-continue failure semantics — lives in `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md` in an installed consumer repo). The apply-mode run adopts it (the non-thread commit shape per `git_sync.md` §Commit-message shape → "Non-thread commit shapes"); dry-run and `--report` modes write nothing and are unaffected. When `.anvil/config.json` is absent or the knob is false, behavior is byte-identical to a pre-#426 install — the hook is **default off**.
