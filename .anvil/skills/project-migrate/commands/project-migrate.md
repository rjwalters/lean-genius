---
name: project-migrate
description: Migrate an existing studio project to the post-#295 / post-#296 canonical model (BRIEF.md absorbs all config, `<slug>.md` body filename, `<project>/<slug>/<slug>.<N>/` shape).
---

# `/anvil:project-migrate`

Bridge tool. Migrates an existing studio project in place to the canonical
post-#295 / post-#296 model.

## Usage

```
/anvil:project-migrate <project-dir>             # dry-run (no mutations)
/anvil:project-migrate <project-dir> --apply     # execute the plan
/anvil:project-migrate <project-dir> --report    # markdown report only
    [--artifact-type <type>]                     # optional on all three above (issue #878)

/anvil:project-migrate --enroll <file> [<file> ...]    # dry-run enrollment
    [--project <dir>] [--slug <slug>] [--artifact-type <type>] [--apply]

/anvil:project-migrate --adopt-vn <dir>                # dry-run vN adoption
    [--slug <slug>] [--artifact-type <type>] [--apply]

/anvil:project-migrate --adopt-family <dir>            # dry-run letter-family adoption
    --tag-map <file> --artifact-type <type> [--apply]

/anvil:project-migrate --adopt-review <dir>           # dry-run review.md stub conversion
    [--apply]
/anvil:project-migrate --adopt-review <dir> --rescore # dry-run operator-LLM rescore of stubs
    [--apply]
```

`<project-dir>` is the project root: the directory that holds (or will hold)
the project-level `BRIEF.md` and the per-thread `<slug>/` directories.

## Procedure

### 0. Mode dispatch

If neither `--apply` nor `--report` is passed, the command runs in **dry-run
mode**: it detects, plans, and prints, but writes nothing to disk.

`--apply` and `--report` are mutually exclusive. Passing both is rejected.

`--artifact-type <type>` is an OPTIONAL modifier on the main mode
(dry-run / `--apply` / `--report` alike, issue #878) — see §2 below for
the full contract. It does not change mode dispatch.

`--enroll <file> [...]` selects **single-file enrollment mode** (issue
#406): instead of migrating a whole project, it wraps one or more loose
`.md` / `.tex` files into project threads. Enrollment runs through
`orchestrate.run_enroll(...)` (dry-run by default, like every mode in
this skill) — see §6 below.

`--adopt-vn <dir>` selects **vN report-dir adoption mode** (issue #432
Phase 1): it adopts a foreign `v{N}/` version-dir family (with
`v{N}.review/`-style critic siblings) into the canonical
`<project>/<slug>/<slug>.{N}/` shape. Adoption runs through
`orchestrate.run_adopt_vn(...)` (dry-run by default) — see §7 below.

`--adopt-family <dir>` selects **letter-family adoption mode** (issue
#440 — Phase 2 of #432): it adopts foreign `{Project}.{Letter}.{N}`
version-dir families (with foreign-tagged critic siblings mapped
through a declarative `--tag-map`) into the canonical
`<dir>/<slug>/<slug>.{N}/` shape. Adoption runs through
`orchestrate.run_adopt_family(...)` (dry-run by default) — see §8
below.

`--adopt-review <dir>` selects **foreign `review.md` stub-conversion
mode** (issue #454 — Phase 3a of #432): on an ALREADY-ADOPTED tree, it
converts each `<slug>.{N}.<tag>/` critic sibling holding only a
single-file prose `review.md` into a recognizable-but-explicitly-
**unscored** `_review.json` stub (+ a `_meta.json` foreign-provenance
marker), preserving `review.md` byte-identical. **NO LLM call, NO
synthesized scores.** Conversion runs through
`orchestrate.run_adopt_review(...)` (dry-run by default) — see §9
below.

`--adopt-review <dir> --rescore` selects **operator-driven LLM rescore
mode** (issue #507 — Phase 3b of #432): on a tree carrying Phase-3a
stubs, it resolves each stub's target anvil rubric and (with the
operator/LLM step supplying per-dimension scores in the slash-command
runtime) turns the unscored stub into a real scored `_review.json`,
flipping `unscored` to `false` and stamping `rubric_id` / `rubric_total`
/ `advance_threshold`. Runs through `orchestrate.run_adopt_review(...,
rescore=True)` (dry-run by default; `--apply` required to mutate) — see
§9b below.

### 1. Detect current shape

Call `detect.detect_shape(project_dir)`. This returns a `Shape` enum:

- `Shape.FULLY_MIGRATED` — project root with `BRIEF.md` absorbing all config,
  `<slug>/<slug>.N/<slug>.md`.
- `Shape.POST_283_ANVIL_JSON` — project root with `BRIEF.md` listing
  `documents:`, per-thread directories under `<project>/<slug>/`, but with
  separate `.anvil.json` files and possibly `memo.md` bodies.
- `Shape.PRE_283_CLASSIC` — no project-level `BRIEF.md`; `memo.N/` siblings
  directly under the project root; skill-fixed `memo.md` bodies. The
  **bare sub-state** (issue #408 — version-dir families with no anvil
  config anywhere, e.g. `paper.tex` bodies; `ProjectInventory.is_bare`)
  also classifies here: the BRIEF is then SYNTHESIZED from observed
  state with `# TODO(operator)` confirmation markers on every inferred
  value, and the report header reads
  `pre_283_classic (bare — BRIEF will be synthesized)`.
- `Shape.UNKNOWN` — not recognizable; emit a diagnostic and exit non-zero.

### 2. Plan

Call `plan.build_plan(project_dir, shape, artifact_type=...)`. Returns a
`Plan` object listing per-document `DocumentPlan` entries. Each entry
carries:

- `slug` — final slug name.
- `source_dir` — current on-disk directory (may equal target).
- `target_dir` — where the doc should live post-migration
  (`<project>/<slug>/`).
- `renames` — list of `(source_path, target_path)` pairs for filesystem moves.
- `content_rewrites` — list of `(file_path, old_string, new_string)` tuples
  for in-file content edits (cross-thread refs, body filename refs).
- `brief_merge` — optional `BriefMergeOp` recording the `documents:` entry
  to add/update in the project-level `BRIEF.md`.
- `anvil_json_source` — optional path to a `.anvil.json` that will be merged
  into the BRIEF entry.
- `notes` — operator-facing notes (e.g., "cross-thread references rewritten:
  3 occurrences").

**`--artifact-type <type>` on the main mode (issue #878).** A bare project
(no anvil config anywhere — `ProjectInventory.is_bare`) with a plain `.md`
body used to be stuck: the BRIEF this run synthesizes always defaulted
every thread to `artifact_type: investment-memo`, but the *correct*
declaration (e.g. `artifact_type: essay`) can only come from that same
synthesized BRIEF — circular, so a consumer whose body filename doesn't
match anvil's own historical fixed names (e.g. a foreign blog pipeline's
`post.md`) got neither the right type nor a body rename. `--artifact-type`
resolves the circularity directly:

- Validated against the same two-tier registry `--enroll` /
  `--adopt-vn` use (`REGISTERED_ARTIFACT_TYPES` + consumer-declared types
  via `discover_consumer_artifact_types`); an unregistered value is a
  plan-time refusal (`plan.PlanError`) raised BEFORE any mutation.
- Applied to every synthesized `documents:` entry on a BARE thread —
  `artifact_type` is set directly with **no** `# TODO(operator)` marker
  (the operator declared it explicitly; nothing was guessed). Non-bare
  threads (already carrying a declared or legacy type) are unaffected.
- **Independent of the body-filename rename below** — the flag only
  affects the BRIEF's `artifact_type:` value.

**Foreign body-filename detection (issue #878, independent of the flag
above).** A bare thread's `.md` body filename may be fixed by a FOREIGN
pipeline (e.g. `post.md`) rather than any anvil skill's *own* historical
fixed name (`memo.md`, `proposal.md`, `report.md`, `installation.md`,
`pub.md`) — the historical skill-fixed rename loop only recognizes
anvil's own names, so it has nothing to match. The planner separately
scans each bare thread for a **single consistent** non-canonical `.md`
filename across its version dirs and, when exactly one is found, plans
its rename to `<slug>.md` — reviewable in the dry-run plan before
`--apply`, and paired with a `# TODO(operator)` confirmation note (never
silent). This fires whether or not `--artifact-type` is given. When
**multiple distinct** foreign names are observed across the thread's
version dirs, the choice is ambiguous: no rename is planned, and the plan
surfaces an operator-facing note instead of guessing.

### 3. Report (dry-run / `--report`)

Print the plan as a markdown report:

- Header naming the project, detected shape, and plan summary.
- One section per document with its planned renames, content rewrites, and
  BRIEF merge.
- The **full proposed `BRIEF.md` text** (issue #408) whenever the plan
  carries BRIEF merges — rendered through the same
  `apply.render_project_brief` code path the apply step writes, so the
  preview is byte-identical to the eventual write.
- Footer with the verify-step preview ("after apply, the project would
  round-trip through `discover_thread_root` + `load_project_brief`").

In dry-run mode, the command exits 0 after printing. In `--report` mode it
also exits 0.

In `--apply` mode, the report is printed first (so the operator can see what
is about to happen), then the apply step runs.

### 4. Apply (`--apply` only)

For each `DocumentPlan` in the plan:

1. Take a per-doc snapshot at
   `<project>/.anvil-migrate-rollback/<slug>/` (copy the source dir).
2. Run the renames + content rewrites.
3. If the project is under git (`.git/` exists at or above `project_dir`),
   prefer `git mv` over plain `shutil.move`. Plain renames still work
   correctly; `git mv` is preferred so history follows.
4. If any step in the doc fails, roll back this doc only:
   restore from the snapshot and surface the error. Already-migrated docs are
   not affected.
5. On success, remove the per-doc snapshot.

After all per-doc applies, write the project-level `BRIEF.md` with the merged
`documents:` list. (BRIEF write is the LAST step — until it succeeds, the
existing `BRIEF.md`, if any, is unchanged on disk.) Use a temp-file + rename
to make the BRIEF write atomic.

### 5. Verify (`--apply` only)

Call `verify.verify_migration(project_dir)`:

1. `discover_thread_root(<project>/<slug>/<slug>.N/<slug>.md)` returns a
   `DiscoveryResult` for every slug.
2. `load_project_brief(project_dir)` parses cleanly and lists every slug.
3. No `.anvil.json` files remain anywhere under `project_dir`.
4. No `memo.md` files remain (they should all be `<slug>.md`).
5. No `memo.N/` directories remain at the project root (they should all be
   `<slug>.N/` under their `<slug>/` parent).

Report each verify result. If any fail, exit non-zero with the failures.

### 6. Enrollment mode (`--enroll`, issue #406)

Wraps loose single-file documents (flat `.md` / `.tex` files in topical
directories) into project threads:

```
/anvil:project-migrate --enroll corporate/memos/2026-05-19-board-update.md
/anvil:project-migrate --enroll ip/*.md --project ip --apply
```

Call `orchestrate.run_enroll(files, project=..., slug=...,
artifact_type=..., apply=...)`. The flow:

1. **Project resolution**: `--project` if given (must exist; BRIEF
   optional — created if absent); else walk up from the file looking
   for an existing project BRIEF (bounded by the git repo root); else
   propose the file's parent as a new project root.
2. **Slug derivation**: from `--slug` (must already be canonical —
   `^[a-z0-9][a-z0-9-]*$`; rejected, never re-sanitized), else from the
   filename: leading/trailing ISO date token stripped (and preserved as
   a YAML comment on the BRIEF entry plus a body enrollment-log line),
   lowercased, non-alphanumeric runs collapsed to `-`.
3. **Mechanics**: move the file to `<project>/<slug>/<slug>.1/<slug>.<ext>`
   (`git mv` in-repo so history follows; plain move otherwise). `.tex`
   bodies slug-echo too — new enrollments have no external-tooling
   carve-out (the enclosing move already breaks any path-based
   consumer); a plan note records the rename and that references to the
   old path are NOT rewritten.
4. **BRIEF write**: with an existing BRIEF, the new `documents:`
   entries are added by **surgical textual append** at the end of the
   `documents:` block — every pre-existing byte (YAML comments, top-level
   `theme:`, per-doc `render_*` keys, quoting, entry order) is preserved
   byte-identically, and the body gains an `## Enrollment log` line.
   With no BRIEF, a minimal one is synthesized via
   `render_project_brief` with the #408 TODO-marker discipline. The
   write is strict-validated (`load_project_brief_strict`,
   `validate_dirs=True`) and rolled back on any parse failure.
5. **Artifact type**: `--artifact-type` validated against the two-tier
   registry (#394: registered + consumer-declared); else inferred WITH a
   `# TODO(operator)` marker (`.md` → `investment-memo`;
   `.tex` with `\documentclass{anvil-proposal}` → `proposal`; other
   `\documentclass` → `paper`).
6. **Batch semantics**: N files → N independently-planned
   `DocumentPlan`s in ONE project. Plan-time errors (slug collisions —
   existing or intra-batch, non-md/tex inputs, already-enrolled inputs,
   malformed BRIEF) abort the whole batch BEFORE any mutation.
   Apply-time failures isolate per document (snapshot rollback); the
   BRIEF is written for the **succeeded subset**.

Hard errors (plan-time, pre-mutation):

- Slug collision with a BRIEF entry, an on-disk path, or another batch
  member — the error names the conflict; suggest `--slug`.
- Non-`.md`/`.tex` input; `BRIEF.md` / `README.md` inputs.
- Already-enrolled input (inside a version dir, or
  `discover_thread_root` resolves it) — re-enrolling is a refusal, not
  a duplicate (idempotency).
- Existing BRIEF that fails strict parsing — never modify a BRIEF we
  can't parse.
- A BRIEF-less project root containing other thread-shaped dirs — run
  plain `project-migrate` on it first.
- Empty derived slug (date-only or symbol-only stems) — pass `--slug`.

### 7. vN report-dir adoption mode (`--adopt-vn`, issue #432 Phase 1)

Adopts a foreign `v{N}` version-dir family — the sphere-survey report
grammar (`projects/<proj>/reports/v3/` + `v3.review/` siblings) — into
the canonical anvil shape:

```
/anvil:project-migrate --adopt-vn projects/acme/reports
/anvil:project-migrate --adopt-vn projects/acme/reports --slug quarterly --apply
```

Call `orchestrate.run_adopt_vn(directory, slug=..., artifact_type=...,
apply=...)`. The flow (one family per invocation):

1. **Family scan**: `^v(\d+)$` dirs under `<dir>` are the family;
   `v{N}.<tag>` sibling dirs (observed: `v{N}.review/`) rename
   alongside their version dir. Version gaps are tolerated (per #408).
   Stray non-versioned dirs — and orphan `v{N}.<tag>` sidecars whose
   `v{N}` is absent — are left untouched and reported.
2. **Project resolution**: walk up from `<dir>`'s parent looking for an
   enclosing project BRIEF (bounded by the git repo root); else propose
   `<dir>`'s parent as a new project root (starter BRIEF synthesized).
3. **Slug**: `--slug` (must already be canonical — rejected, never
   re-sanitized; #406 precedent) or the sanitized enclosing-dir name
   (`reports` is grammar-valid as-is).
4. **Renames**: `v{N}/` → `<project>/<slug>/<slug>.{N}/` and
   `v{N}.<tag>/` → `<slug>.{N}.<tag>/` (`git mv` in-repo so history
   follows). When `<slug>` equals the family dir's name (the default),
   the renames are in-place. Bodies inside the version dirs are
   recorded but **never renamed** (the #408 carve-out).
5. **BRIEF write**: surgical textual append when an enclosing project
   BRIEF exists (#406/#416 — never re-render an operator BRIEF);
   starter synthesis with `# TODO(operator)` markers otherwise (#408).
   Strict-validated post-write; rolled back on any parse failure. The
   dry-run report previews the full proposed BRIEF through the same
   render path as apply (byte-identical).
6. **Artifact type**: `--artifact-type` validated against the two-tier
   #394 registry; else inferred `report` WITH a `# TODO(operator)`
   marker (the mode targets report dirs; nothing is guessed silently).
7. **Idempotence**: re-running on an adopted tree finds no `v{N}`
   family and is a successful no-op (even under `--apply`).

Hard errors (plan-time, pre-mutation — the whole family aborts):

- Minor-versioned oddballs (`v14.1`): refusal naming each offending dir
  with a suggested manual target (the next free integer). A
  `--renumber` escape hatch is deferred until canary friction demands
  it.
- Versioned critic-sidecar tags (`v3.review-v2`): refusal — renaming
  would re-create a foreign name; tag vocabulary mapping is
  `--adopt-family`'s `--tag-map` (a versioned tag becomes mappable
  there, e.g. `"review-v2": "review"`).
- Slug collision with a BRIEF entry or an on-disk path; target
  `<slug>.{N}` already exists — suggest `--slug`.
- Existing BRIEF that fails strict parsing — never modify a BRIEF we
  can't parse.
- A BRIEF-less project root containing other thread-shaped dirs — run
  plain `project-migrate` on it first.

### 8. Letter-family adoption mode (`--adopt-family`, issue #440 — Phase 2 of #432)

Adopts foreign `{Project}.{Letter}.{N}` version-dir families — the
sphere-survey ip-thread grammar (`Meridian.C.7/` +
`Meridian.C.7.enablement/` siblings, flat under one directory) — into
the canonical anvil shape:

```
/anvil:project-migrate --adopt-family agents/Meridian \
    --tag-map tag-map.json --artifact-type ip-uspto-provisional
/anvil:project-migrate --adopt-family agents/Meridian \
    --tag-map tag-map.json --artifact-type ip-uspto-provisional --apply
```

Call `orchestrate.run_adopt_family(directory, tag_map=...,
artifact_type=..., apply=...)`. The flow (one invocation = one
directory = N letter families, batch):

1. **Family scan**: `{Project}.{Letter}.{N}` dirs group by their
   `{Project}.{Letter}` stem (the letter is the single-letter final
   dot-segment); `{stem}.{N}.<tag>` sibling dirs rename alongside
   their version dir. Version gaps tolerated (per #408). Strays
   (non-matching dirs, numeric-tag oddballs like `Meridian.C.7.1`) and
   orphan sidecars (version dir absent) are left untouched and
   reported.
2. **Project root**: `<dir>` itself — the families sit flat under it
   and the adopted threads land at `<dir>/<slug>/<slug>.{N}` with the
   BRIEF at `<dir>/BRIEF.md`.
3. **Slugs are derived, not flagged**: the `{Project}.{Letter}` stem
   folds via the standard sanitization (`Meridian.C` → `meridian-c`).
   There is NO `--slug` in this mode (multi-family invocations make a
   single override meaningless; derived slugs are deterministic).
4. **Declarative tag mapping (`--tag-map <file>`)** — the binding spec
   is the issue #432 curation comment ("Declarative tag-mapping
   contract"). JSON, stdlib-only:
   `{"tag_map": {"<foreign>": "<canonical>", ...}}`. REQUIRED whenever
   any renameable critic sidecar is observed; every observed foreign
   tag MUST have an entry (identity mappings allowed and expected —
   `"s101": "s101"`). NO heuristics, ever. Values must be a single
   dot-free word with no `-vN` suffix. The dry-run report prints the
   full per-directory resolution (every sidecar's old name → new
   name) for operator confirmation. Versioned tags refused by
   `--adopt-vn` become mappable here (`"review-v2": "review"`).
5. **Renames**: `{stem}.{N}/` → `<dir>/<slug>/<slug>.{N}/` and
   `{stem}.{N}.<foreign>/` → `<slug>.{N}.<canonical>/` per the tag map
   (`git mv` in-repo so history follows). Bodies inside the version
   dirs are recorded but **never renamed** (the #408 carve-out).
   Sidecars holding only a single-file `review.md` payload stay
   invisible-but-intact to `discover_critics` after the rename (the
   #346 additive contract) — content conversion is Phase 3 (issue
   #454; `anvil:rubric-rebackport` targets anvil-shaped legacy
   reviews only and does not apply).
6. **Artifact type**: `--artifact-type` is REQUIRED — there is no safe
   inference between `ip-uspto` and `ip-uspto-provisional` (both
   registered skill-identity values as of #440), and nothing is
   guessed silently with legal-artifact stakes. The value applies
   invocation-wide; every BRIEF entry carries a
   `# TODO(operator): confirm — applied invocation-wide by
   --adopt-family` marker, and per-family divergence is a cheap
   post-adopt BRIEF edit (artifact_type is per-slug).
7. **BRIEF write**: surgical textual append when `<dir>/BRIEF.md`
   exists (#406/#416); starter synthesis with `# TODO(operator)`
   markers otherwise (#408). Strict-validated post-write; rolled back
   on any parse failure. The dry-run report previews the full
   proposed BRIEF through the same render path as apply
   (byte-identical).
8. **Batch semantics**: N families → N independently-applied
   `DocumentPlan`s. Plan-time errors abort the WHOLE batch
   pre-mutation; apply-time failures isolate per family (snapshot
   rollback) with the BRIEF written for the **succeeded subset** (the
   enroll contract, routed through `Shape.ADOPT_FAMILY`).
9. **Idempotence**: re-running on an adopted tree finds no letter
   family and is a successful no-op (even under `--apply`); post-adopt
   names pass project-scout's `find_foreign_families` clean on all
   three predicates.

Hard errors (plan-time, pre-mutation — the whole batch aborts):

- Critic sidecars observed but no `--tag-map` passed — refusal listing
  the observed foreign tags.
- Unmapped observed tag — refusal listing the missing tags (the
  operator's next edit is mechanical).
- Tag-map value violating the canonical tag grammar (dotted word,
  `-vN` suffix, non-word characters).
- Two foreign tags resolving to one canonical tag on the SAME version
  dir (e.g. `.audit` + `.audit2` → `audit` on `Meridian.C.7`); the
  same pair on different version dirs is legal.
- Missing `--artifact-type` — refusal naming the two likely ip
  candidates.
- Slug collision with a BRIEF entry or an on-disk path; cross-family
  collision after sanitization (`Meridian.C` vs `meridian.c`).
- Existing BRIEF that fails strict parsing — never modify a BRIEF we
  can't parse.
- A BRIEF-less project root containing other thread-shaped dirs — run
  plain `project-migrate` on it first.

Single-file `review.md` → recognizable-review-payload conversion is
**Phase 3a** (`--adopt-review`, issue #454 — see §9). The optional
operator-driven LLM rescore (turning a stub into a real scored review)
is **Phase 3b** (`--adopt-review --rescore`, issue #507 — see §9b).

### 9. Foreign `review.md` stub-conversion mode (`--adopt-review`, issue #454 — Phase 3a of #432)

```
/anvil:project-migrate --adopt-review agents/agent-workspace
/anvil:project-migrate --adopt-review agents/agent-workspace --apply
```

Call `orchestrate.run_adopt_review(directory, apply=...)`. The flow runs
**standalone on an already-adopted tree** (canonical
`<slug>/<slug>.{N}/` version dirs with `<slug>.{N}.<tag>` siblings); it
touches **no `BRIEF.md`** and is **dry-run by default** like every mode
in this skill. Steps:

1. **Scan** the adopted tree for `<slug>.{N}.<tag>/` critic siblings
   that hold only a single-file prose `review.md` — those that FAIL
   `critics._has_recognizable_review` and so stay invisible to
   `discover_critics` (the #346 additive contract). A sidecar that
   already carries `_review.json` (a prior conversion, or a real review)
   is skipped.

2. **Plan** one stub conversion per such sidecar. The original
   `review.md` is recorded as PRESERVED, never as a rename source.

3. **Honest STUB conversion — NO LLM, NO synthesized scores.** Foreign
   `review.md` payloads were never scored on any anvil rubric (no
   per-dimension table, no `Total: X/Y`, no `advance: true|false`), so
   extracting scores would be **fabrication**. Each conversion writes:
   - a canonical `_review.json` with empty `scores` / `findings` /
     `critical_flags`, null `total` / `threshold` / `verdict`, and
     `unscored: true` (the schema flag — issue #454, additive — that
     lets `scores` be empty for an honest unscored-foreign stub);
   - a sibling `_meta.json` foreign-provenance marker
     `{"source": "foreign-adopted", "unscored": true, "origin_filename":
     "review.md", "adopted_by": "anvil:project-migrate#454"}`;
   - and preserves `review.md` **byte-identical** (the stub is purely
     additive).

4. **Apply** (`--apply` only): per-sidecar atomic + crash-safe via
   `anvil/lib/sidecar.py::staged_sidecar`. The live dir is moved aside,
   the full replacement (verbatim `review.md` + the two new files) is
   staged and atomically renamed in, and the moved-aside original is
   removed. On any mid-write failure the original dir is restored
   untouched and the conversion is recorded as failed (failures isolate
   per sidecar).

   **Non-Python-driver ordering (fail-open, manual fallback)** — issue
   #645: this whole `--apply` conversion runs **inside**
   `orchestrate.run_adopt_review(...)`, a Python driver that holds the
   `staged_sidecar` context manager open across the moved-aside → stage →
   swap sequence, so the code path is code-enforced by default. The clause
   below is the fallback for a **driver-less agent session** that reproduces
   this conversion by hand (no orchestrating Python process to hold the
   `with` block open across its own editing-tool writes). It applies to
   **both** apply sites in this skill: this Phase 3a stub conversion and the
   Phase 3b scored-rescore write in §9b step 3 (both reuse the same
   staged/backup/swap pattern). Two tiers, in preference order:

   1. **Primary — `python -m anvil.lib.sidecar` CLI shim** (the common
      case; wraps the *exact same* `staged_sidecar` code, so the
      manifest check + single atomic `Path.rename` are code-enforced, not
      agent discipline). In an installed consumer repo (anvil vendored
      under `.anvil/`, not on `sys.path`), prefix every invocation below
      with `uv run --project .anvil` (the `.anvil/pyproject.toml` +
      `uv sync --project .anvil` shipped by the installer since #230 make
      the module resolvable from the consumer root); in the anvil source
      repo the bare `python -m anvil.lib.sidecar` form works as-is. For the
      sidecar dir `<slug>.{N}.<tag>/` being converted:
      - `uv run --project .anvil python -m anvil.lib.sidecar stage <slug>.{N}.<tag>` — but note this
        primitive **refuses to overwrite an existing final dir**
        (`FileExistsError`), whereas this conversion **replaces a live dir
        in place**. So the moved-aside contract is preserved by hand first:
        `mv <slug>.{N}.<tag> <slug>.{N}.<tag>.bak` (the "moved aside"
        original), THEN `stage <slug>.{N}.<tag>` to open a fresh staging
        path, write the full replacement (verbatim `review.md` copied back
        from the `.bak` + the new `_review.json` + `_meta.json`) into it.
      - `uv run --project .anvil python -m anvil.lib.sidecar commit <slug>.{N}.<tag> --required review.md,_review.json,_meta.json`
        → verifies the manifest, then atomically renames staging → final.
        **Nonzero exit (1) leaves the staging dir in place with no partial
        final dir** if any required file is missing; on success remove the
        `<slug>.{N}.<tag>.bak` moved-aside original. On any failure, restore
        it (`mv <slug>.{N}.<tag>.bak <slug>.{N}.<tag>`) so the sidecar is
        left **byte-identical** — matching the "original dir is restored
        untouched" isolation guarantee above.
      - Stale-staging sweep analog: `uv run --project .anvil python -m anvil.lib.sidecar cleanup <slug>.{N}.<tag>`.
   2. **Last resort — manual `mv`-based staging** when even `python`/`uv`
      is unavailable. Reproduce the contract by hand: (a) `mv
      <slug>.{N}.<tag> <slug>.{N}.<tag>.bak` to move the live original
      aside; (b) `mkdir <slug>.{N}.<tag>.staging` and write **every**
      replacement file into it (`review.md` copied byte-identical from the
      `.bak`, then the new `_review.json`, then `_meta.json` **last**);
      (c) confirm all three files are present, **then** `mv
      <slug>.{N}.<tag>.staging <slug>.{N}.<tag>` as the **last** step (a
      same-filesystem dir rename is atomic, matching `Path.rename`), and
      remove the `.bak`. On any mid-write failure, `rm -rf` the staging dir
      and `mv <slug>.{N}.<tag>.bak <slug>.{N}.<tag>` to restore the original
      untouched. **Record the fallback durably** so a reader can tell
      atomicity was reproduced by hand rather than tool-verified: stamp the
      converted `_meta.json` with `"atomicity_fallback": "manual-mv"`
      alongside its `source: foreign-adopted` marker. Absent this note the
      manual swap is indistinguishable from an unsafe direct write.

   Both tiers land a byte-identical on-disk result to the driver-held
   `staged_sidecar` path (verbatim `review.md`, additive new files, original
   restored on any failure); they exist only to give a Python-less session a
   code-enforced (tier 1) or contract-faithful (tier 2) route to the same
   atomicity guarantee. When `run_adopt_review` runs under a Python driver
   (the default), it uses `staged_sidecar` directly and the CLI shim is not
   needed.

5. **Idempotence**: re-running finds no `review.md`-only sidecar and is
   a successful no-op (even under `--apply`). An empty-`scores` stub
   passes `_has_recognizable_review` and feeds `aggregate`, contributing
   **zero dimensions** — it never corrupts a real co-sibling's total or
   flips its verdict.

### 9b. Operator-driven LLM rescore of stubs (`--adopt-review --rescore`, issue #507 — Phase 3b of #432)

```
/anvil:project-migrate --adopt-review agents/agent-workspace --rescore
/anvil:project-migrate --adopt-review agents/agent-workspace --rescore --apply
```

Phase 3b turns a Phase-3a **unscored stub** into a **real scored review**.
It is an opt-in `--rescore` modifier on `--adopt-review` — **NOT** a
`rubric-rebackport` extension (rubric-rebackport's detector only matches
`.review` siblings, not the `.enablement` / `.s101` / `.fto` critic tags
foreign stubs live on, and its `--rescore` requires a prior anvil score a
stub never had). Call `orchestrate.run_adopt_review(directory,
rescore=True, apply=..., scored_reviews=...)`. **Dry-run by default**; the
operator gate is binding — a rescore NEVER runs silently. Steps:

1. **Plan** (`run_adopt_review(directory, rescore=True)`): scan the
   adopted tree for sidecars carrying a Phase-3a stub — `_review.json`
   with `unscored: true` AND `_meta.json` `source: foreign-adopted` (the
   dual marker Phase 3a stamped at the project-migrate seam). For each
   stub, **resolve the target anvil rubric**: BRIEF `documents:` block
   (`artifact_type` → skill) first, sibling version-dir body filename
   (`memo.md`, `ip-uspto.md`, …) as fallback. A stub whose rubric cannot
   be resolved is **SKIPPED with an operator-visible note — never
   guessed** (the honesty guard, mirroring `rubric-rebackport`'s
   `inferred_skill is None` → skip discipline).

2. **Operator/LLM hand-off (in the slash-command runtime, NOT Python).**
   For each planned target, read the verbatim `review.md` prose + the
   resolved rubric (`rubric_id`, the per-dimension dimensions and weights
   from the skill's `rubric.md`) and produce per-dimension scores,
   optional findings, and optional critical flags. This is the
   judgment-laden step; it stays in the consumer's runtime — the exact
   precedent in `anvil/skills/rubric-rebackport/lib/rescore.py` ("the
   actual LLM call belongs in the consumer's slash-command runtime, not
   in this Python library"). Package each result as an
   `adopt_review.ScoredReviewInput(sidecar_name, scores, findings,
   critical_flags)` and assemble a `{sidecar_name: ScoredReviewInput}`
   map.

3. **Apply** (`--rescore --apply` only): call
   `run_adopt_review(directory, rescore=True, apply=True,
   scored_reviews=<map>)`. For each target with a supplied score, the
   harness writes the scored review **per-sidecar atomically** via
   `anvil/lib/sidecar.py::staged_sidecar` (reusing Phase 3a's
   staged/backup/swap pattern), so `review.md` stays **byte-identical**.
   **Non-Python-driver ordering (fail-open, manual fallback)** — issue
   #645: because this reuses Phase 3a's staged/backup/swap pattern, the
   two-tier CLI-shim / manual-`mv` fallback documented at §9 step 4 (the
   `uv run --project .anvil python -m anvil.lib.sidecar stage/commit/cleanup` shim, then the manual
   moved-aside `mv` last resort with a durable `atomicity_fallback:
   manual-mv` stamp) applies verbatim to this scored-rescore write for a
   driver-less agent session; the only difference is the replacement
   `_review.json` is the **scored** review (below) rather than the unscored
   stub. When `run_adopt_review` runs under a Python driver (the default),
   it holds `staged_sidecar` open directly and the shim is not needed.
   Each write:
   - replaces `_review.json` with a **scored** `Review`: populated
     `scores` / `findings` / `critical_flags`, `total` = sum of non-null
     scores, `threshold` = the rubric's `advance_threshold`, `verdict`
     derived (`BLOCK` if any critical flag; else `ADVANCE` if `total >=
     threshold`; else `REVISE`), `rubric` = the resolved `rubric_id`, and
     **`unscored: false`** (the #454 schema contract REQUIRES non-empty
     `scores` before this flag flips — the harness refuses an empty
     scorecard);
   - updates `_meta.json` to record lineage: flips `unscored: false`, adds
     `rescored_from: foreign-adopted` (retaining `source: foreign-adopted`
     + `origin_filename`), and stamps the v0.4.0 per-review rubric fields
     `rubric_id` / `rubric_total` / `advance_threshold`.
   A target with **no** supplied score is left as an honest stub
   (recorded in the report) — the harness NEVER fabricates scores.

4. **Atomicity + idempotence**: on any mid-write failure the original stub
   is restored byte-identical (still `unscored: true`). Re-running
   `--rescore` on a fully-rescored tree finds no `unscored: true` stub and
   is a successful no-op. Running on a tree with no Phase-3a stub yields
   an empty plan, not an error.

The operator gate is binding: `--rescore` is NEVER auto-run as part of
`--adopt-review` / `--adopt-family`; it requires the explicit `--rescore`
flag (and `--apply` to mutate).

## Output

In all modes, the command prints a markdown report to stdout. In `--apply`
mode it also writes filesystem changes.

The report follows this shape:

```markdown
# Project migration: <project-name>

**Project root**: <abs path>
**Detected shape**: <Shape>
**Documents**: <N>

## Plan

### <slug-1>
- Rename: `<source>/memo.3/` → `<slug-1>/<slug-1>.3/`
- Rename: `<slug-1>.3/memo.md` → `<slug-1>.3/<slug-1>.md`
- Content rewrite: `<slug-1>.3/<slug-1>.md`:
  - `memo.2` → `<slug-1>.2` (1 occurrence)
- BRIEF merge: add `<slug-1>` to `documents:` with target_length, rubric_overrides
  from `.anvil.json`.

### <slug-2>
- ...

## Verification preview

After apply, the project would round-trip through `discover_thread_root` +
`load_project_brief` cleanly.
```

## Errors

- Source directory does not exist or is not a directory: hard-fail.
- `--apply` and `--report` both passed: hard-fail.
- Detection returns `Shape.UNKNOWN`: hard-fail with a diagnostic.
- `--artifact-type` given but not a registered or consumer-declared
  artifact type (issue #878): `plan.PlanError`, raised BEFORE any
  mutation — the message lists both the registered and consumer-declared
  sets.
- Apply step fails for a doc: per-doc rollback, then report the failure and
  exit non-zero. Already-migrated docs are not rolled back.
- Verify fails after apply: report the failures and exit non-zero. The
  filesystem state is left in place (the operator needs to inspect).

## Idempotence

Re-running `--apply` on a fully-migrated project produces a `Shape.FULLY_MIGRATED`
detection, an empty plan, and a clean verify. Zero diff on disk.

## Relationship to `anvil:memo-migrate`

The memo-side LaTeX bootstrap (`anvil:memo-migrate`) produces a thread in the
post-#283 with `.anvil.json` shape. Running `/anvil:project-migrate <project>
--apply` on the resulting portfolio is the documented post-step that
consolidates the `.anvil.json` into the project `BRIEF.md`. The composition
works without flags or special-casing — `project-migrate` recognizes the
post-#283 shape and migrates it the same way it would migrate any other
post-#283 project.

## Git sync (opt-in, off by default)

Per `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md` in an installed consumer repo): if `.anvil/config.json` exists and `git.commit_per_phase` is `true`, end this phase: stage only the dirs this phase wrote, commit as `anvil(<skill>/<phase>): <thread>.{N} [<state>]`, push if `git.push` is `true`. Git failures warn and continue — never fail the phase. When the config or knob is absent, skip this step entirely (default off).

This phase's specifics (a project-scoped tool, not a `<thread>.{N}` phase — non-thread commit shape per `git_sync.md` §Commit-message shape → "Non-thread commit shapes"):

- **Ordering**: on the `--apply` path only, after the apply + verify steps complete. Dry-run and `--report` modes write nothing, so the hook has nothing to commit and is a silent no-op; an idempotent re-run of `--apply` on a fully-migrated project likewise produces zero diff and silently skips the commit.
- **Staging target**: ONLY the paths the migration plan touched — the renamed version dirs and body files, the rewritten file contents, and the created-or-merged project `BRIEF.md` — each staged explicitly by path (never `git add -A`).
- **Commit**: `anvil(project-migrate/apply): <project> [MIGRATED]` — the version token is the project slug.
