---
name: paper-revise
description: Reviser command for the paper skill. Reads the latest version + all critic siblings (review, audit, litsearch) and produces the next version with a changelog mapping critic notes to changes.
---

# paper-revise — Reviser

**Role**: reviser.
**Reads**: latest `<thread>.{N}/` (+ `provenance.md` when the corpus tier is active — issue #612) and ALL `<thread>.{N}.*/` critic siblings (`.review/`, `.audit/`, `.corpus-audit/`, `.litsearch/`, `.critic/`, ...).
**Writes**: `<thread>.{N+1}/` containing the revised paper, `figures/`, `_progress.json` (+ a refreshed `provenance.md` when the corpus tier is active), and a `changelog.md` mapping critic notes to the changes made.

This command is the canonical "N parallel critics, one reviser" pattern from anvil's design principles. It consumes any number of critic siblings at the current version and produces a single revised version that addresses them.

## Inputs

- **Thread slug** (positional argument).
- **Latest version**: highest `N` with `<thread>.{N}/main.tex`.
- **Critic siblings**: ALL `<thread>.{N}.<critic>/` directories at that `N`. At minimum the `.review/` sibling is required (the reviewer's verdict drives the dimension-by-dimension revision plan). Optional siblings (`.audit/`, `.litsearch/`, `.critic/`, etc.) contribute additional findings.

## Outputs

```
<thread>.{N+1}/
  main.tex             Revised paper body
  refs.bib             Revised bibliography (entries added/removed as the revision requires)
  figures/             Carried over and/or updated figures (with figures/src/ scripts preserved)
  changelog.md         Maps each critic note (by sibling + section) to the change made in this revision
  _progress.json       Phase state with revise: done
```

## Procedure

1. **Discover state**: find the highest `N` with `<thread>.{N}/main.tex` AND at least `<thread>.{N}.review/verdict.md`. If no review exists, exit with an error ("no review to revise against; run `paper-review` first").
2. **Resume check**: if `<thread>.{N+1}/_progress.json.revise.state == done` and `main.tex` + `changelog.md` exist, the revision is complete — exit early with a notice.
3. **Iteration cap check**: read `metadata.max_iterations` from `<thread>.{N}/_progress.json` (or `<thread>/.anvil.json` override; default 4). If `N + 1 > max_iterations`, exit with a `BLOCKED` notice — human review required.
4. **Verdict pre-check**: parse `<thread>.{N}.review/verdict.md`. If `advance == true` AND there are no critical flags in `.review/` AND there are no critical flags in `.audit/` (if `.audit/` exists), exit with a notice: the thread is `READY` (or `AUDITED`), no revision needed. **Exception**: if `.audit/` exists at this `N` with critical flags, revision IS required even when the reviewer marked advance — audit findings drive a new revision.
5. **Initialize `_progress.json`**: write `phases.revise.state = in_progress`, `phases.revise.started = <ISO>`, `metadata.iteration = N+1`, `metadata.max_iterations`, `metadata.revised_from = N`.
6. **Read inputs**:
   - Prior version's `main.tex`, `refs.bib`, `figures/`.
   - `<thread>.{N}.review/verdict.md` + `scoring.md` + `comments.md`.
   - `<thread>.{N}.review/_review.json` (canonical generic /44 scorecard) via `anvil.lib.critics.load_review`.
   - `<thread>.{N}.review/_review.venue.json` IF present — the venue advisory overlay scorecard. Load via the same `load_review` (both files use the existing `Review` schema in `anvil/lib/review_schema.py`; no new shape). The venue file's findings and critical_flags ARE actionable for the reviser, but a venue critical flag does NOT independently force another revise iteration (the convergence gate is computed from the generic file's verdict only).
   - `<thread>.{N}.audit/` if present: `citation-audit.md`, `numerical-audit.md`, `flags.md`.
   - `<thread>.{N}.corpus-audit/` if present (corpus tier active — issue #612): `_review.json` (`kind: tool_evidence`) via `anvil.lib.critics.load_review` + `corpus-audit.md`. Its five-way classification findings and fabrication-class `critical_flags` drive `provenance.md` copy-forward corrections in step 8b (a `FABRICATED` row means cut or re-ground the claim, never invent a citation).
   - `<thread>.{N}.vision/` if present: `_review.json` (`kind=vision`) via `anvil.lib.critics.load_review`. Vision findings target rendered-only figure/table/equation defects and are resolved at the figure source or LaTeX structure, not the prose (see the D6 note under "Notes for the reviser agent").
   - `<thread>.{N}.litsearch/` if present: `notes.md` + `candidates.bib` (the reviser may merge new entries into the revised `refs.bib`).
   - `<thread>.{N}.pending/` if present (pending-marker gate — issue #842): `_review.json` (`kind: tool_evidence`) via `anvil.lib.critics.load_review`. Its `pending_dependency`-typed `critical_flags` and `nit` findings mark honestly-declared `[PENDING <source>]` values that are still outstanding. **These are the ONE flag class the reviser must NOT "resolve" by editing prose** — see the pending-marker carve-out under "Notes for the reviser agent" below.
   - Every other `<thread>.{N}.<critic>/` sibling discovered on disk.
7. **Build a revision plan**:
   - For each rubric dimension that scored below threshold (or had a critical flag), enumerate the specific changes required to lift the score.
   - For each `comments.md` entry tagged `blocker` or `major`, plan a concrete change.
   - For each critical flag in `.audit/flags.md` (unsupported citation, numerical inconsistency, missing experiment, build failure), plan a specific fix.
   - For litsearch-driven additions, identify which related-work section paragraphs need new citations and which `candidates.bib` entries to merge into `refs.bib`.
   - Resolve conflicting feedback between critic siblings explicitly (e.g., reviewer says "expand related work," auditor says "drop the unsupported Smith 2024 cite" — pick a synthesis: expand related work using audit-verified citations from litsearch, drop Smith 2024).
8. **Produce `main.tex`** at `<thread>.{N+1}/main.tex`:
   - Address each planned change.
   - Preserve sections that scored well — do not regress on dimensions that already met the standard. (Reviser anti-pattern: rewriting an 6/6 Method section to "improve flow" and accidentally introducing ambiguity.)
   - Carry over `figures/` from the prior version; update or add figures as the revision plan requires. **Preserve `figures/src/` scripts** so the figurer can re-render in place.

     **Non-Python-driver ordering (binary/bulk-asset channel, issue #1017)**: a `figures/*.pdf` (or a rendered PNG) is binary — an agent's editing tool is text-only and cannot hold its bytes, and a consumer hook may separately block the Bash channel entirely (redirection, `tee`, `cp`, `mv`, `sed -i` — a worktree-isolation guard). Both gaps close the same way `commands/paper-audit.md` step 3 closes the text-sidecar gap: shell out to the sanctioned code-enforced copy primitive rather than reaching for an ad hoc escape hatch (a `shutil.copyfile` one-off, or hand-typing binary content):

     - **Unchanged figure, byte-identical carry-forward**: `uv run --project .anvil python -m anvil.lib.sidecar copy <thread>.{N}/figures/<name>.pdf <thread>.{N+1}/figures/<name>.pdf` (bare `python -m anvil.lib.sidecar copy ...` in the anvil source repo). This copies the whole `figures/` tree in one call when nothing under it changed: `... copy <thread>.{N}/figures <thread>.{N+1}/figures`. Stages into a same-parent leading-dot sibling and lands with a single atomic rename (same shape `staged_sidecar` uses), with post-copy `(size, sha256)` byte-identity verification by default — refuses (nonzero exit) rather than landing an unverified copy. Refuses if the destination already exists; that should never happen for a fresh `<thread>.{N+1}/` version dir.
     - **Updated/new figure**: rendered by `paper-figures` in the normal flow (unaffected by this primitive — it is for moving existing bytes, not generating new ones).
     - The two tiers land a byte-identical on-disk result whether invoked via this CLI shim or an orchestrating Python driver calling `anvil.lib.sidecar.copy_bytes()` directly; use `copy_bytes()` directly when a Python driver is present.
8b. **Copy `provenance.md` forward (conditional — issue #612)**: when the project BRIEF declares a top-level `corpus:` (i.e., `anvil/lib/project_brief.py::resolve_corpus_dirs(<project_dir>)` returns ≥1 dir), read the `<thread>.{N}/provenance.md` claim→source map alongside the critic feedback and **copy it forward** — write a refreshed `<thread>.{N+1}/provenance.md` per `anvil/lib/snippets/provenance.md` §Section 2, applying the same updates as the prose revision: new claims added in the revision get new rows (each with an `Anchor`, issue #868); claims removed drop their rows; changed claims have their `Source file` / `Line range` / `Anchor` updated to match the revised `main.tex`. Any fabrication-class critical flag from `paper-review` step 6 or the `<thread>.{N}.corpus-audit/` sidecar MUST be addressed — cut the fabricated claim or re-ground it in a real corpus passage, never invent a citation. Without this copy-forward, a draft → review → revise → re-audit thread would have no map in version N+1 for `paper-audit` step 5b's second pass to verify. **Mechanically repoint drifted anchors (§Section 4b, #868)**: after copying the map forward, run `python -m anvil.lib.provenance_anchor repoint <thread>.{N+1}/provenance.md <corpus_root> [...]` — it rewrites only the `Line range` cell of rows `paper-audit` step 5b flagged `DRIFTED`, leaving `Claim`/`Source file`/`Anchor`/`Notes` and every non-drifted row untouched; mechanical, never the fabrication case above. **Carry forward `metadata.corpus_dirs_resolved`** in the new `_progress.json`. When the tier is inactive (no `corpus:` key), skip this step entirely — no `provenance.md` copy-forward, **byte-identical to pre-#612** behavior.
9. **Produce `refs.bib`** at `<thread>.{N+1}/refs.bib`:
   - Start from prior version's `refs.bib`.
   - Remove entries that were cited only in passages now deleted.
   - Add entries from `<thread>.{N}.litsearch/candidates.bib` for the new citations.
   - Fix bibliography hygiene issues flagged in the review (missing fields, inconsistent formatting).
   - Verify every `\cite{key}` in the new `main.tex` resolves before marking the phase done.
   - **When a revision adds or rewrites cited prose, pick the cite *command* per the "Citation-command choice under natbib author-year" rule below** — do not reintroduce `Name~\cite{key}` author-name doubling even if the original draft got it right. A revise pass that renames an author in prose or moves a citation across the parenthetical/textual boundary must re-choose between `\citet` / `\citeyearpar` / `\citep`.
10. **Write `changelog.md`**: a markdown table mapping each critic note to the change made.

    Label each entry's `Source` column with both the sibling dir and the **source rubric**: `generic` for entries originating in the generic /44 `_review.json`, `venue:<slug>` for entries from `_review.venue.json`, and `audit` / `litsearch` for the corresponding sibling dirs. This lets a reader see at a glance which rubric flagged which issue — important because the venue overlay is advisory only and a reader may wish to weight venue-origin entries differently.

    ```
    | Source                                       | Note                                    | Resolution                                  |
    |----------------------------------------------|-----------------------------------------|---------------------------------------------|
    | q3-method.1.review (generic, blocker)        | TAM figure unsourced in Sec. 4          | Cited Acme2025 (added to refs.bib)          |
    | q3-method.1.review (generic, major)          | Related Work omits Smith2024            | Added paragraph + citation from litsearch   |
    | q3-method.1.review (venue:neurips, major)    | Missing baseline vs. Chen2024 in Tab. 1 | Added baseline column with rerun results    |
    | q3-method.1.review (venue:neurips, minor)    | Reproducibility checklist gap: seeds    | Added seed table to appendix                |
    | q3-method.1.audit (critical-flag)            | Cite{jones2023} resolves to wrong paper | Removed jones2023 cite; replaced with jones2024 (verified)  |
    | q3-method.1.audit                            | Table 2 accuracy 87.3 ≠ text 87.1       | Recomputed; both now 87.3                   |
    ```

    For deliberate non-resolutions (e.g., critic suggested a change the reviser disagrees with), include them with `Resolution: declined — <one-line reason>`. The next reviewer pass can override or accept the reviser's judgment. Declining a `venue:<slug>` entry is reasonable when the venue advice conflicts with the generic-rubric guidance — note the trade-off in the resolution column.
11. **Update `_progress.json`**: `phases.revise.state = done`, `phases.revise.completed = <ISO>`.
11b. **Record the evidence-drift baseline (issue #857)**: invoke `uv run --project .anvil python -m anvil.lib.evidence_drift record <thread>/ <thread>.{N+1}/` — the same call `paper-draft` step 9b makes, re-baselined against the new version dir. Every revision re-records the current BRIEF/refs mtimes so `paper-review` always compares against the freshest version's baseline, not a stale one from N versions ago. Purely additive; never fails the revise. **Tooling-unavailable fallback**: when `uv` is not on `PATH`, **or this step's write is blocked** (e.g. a consumer-repo hook that blocks Bash-channel writes — issue #1018), skip this step with a one-line notice. Do **not** hand-type a snapshot into `_progress.json` as a substitute — a hand-transcribed mtime float loses precision and can produce a false-positive drift report later. The next successful draft/revise pass records the baseline instead (bootstrap-safety: a missing snapshot reports as clean, never a false positive).
12. **Report**: print the path to the new version dir and a one-line status (e.g., `Revised q3-method.1 → q3-method.2/ (addressed 9 notes including 2 critical-flags, declined 1)`).

## Citation-command choice under natbib author-year

The default `anvil-paper` class loads natbib in **author-year / round** mode (`templates/anvil-paper.cls:56` — `\RequirePackage[round,sort&compress,authoryear]{natbib}`). In this mode **bare `\cite{key}` is aliased to `\citet{key}`** and prints "Author (Year)" — NOT the parenthetical "(Author, Year)". So writing `Name~\cite{key}` **doubles the author name** in the rendered PDF (e.g. `Chung and Miller~\cite{chung2020}` renders as "Chung and Miller Chung and Miller (2020)"). The `.tex` source reads idiomatically, so this defect is invisible in every text-only review/audit pass and surfaces only in the rendered PDF — a revise pass that adds or rewrites cited prose must choose the cite command from whether the author is already named in the surrounding prose:

| Author named in prose? | Use | Renders as |
|---|---|---|
| Yes | `\citeyearpar{key}` | "Chung and Miller (2020)" |
| No | `\citet{key}` | "Chung and Miller (2020) show..." |
| N/A (fully parenthetical) | `\citep{key}` | "...prior work (Chung and Miller, 2020)" |
| — | ~~bare `\cite{key}`~~ | **avoid** — aliases to `\citet{}` under author-year mode; doubles the name when the author is already named in prose |

The **`numeric` documentclass option** (`\documentclass[numeric]{anvil-paper}`) is **unaffected**: there bare `\cite{key}` renders `[N]` and there is no doubling risk, so this rule is scoped to the default (author-year) path only.

## Idempotence and resumability

- A completed revision (`revise.state == done` AND `main.tex` + `refs.bib` + `changelog.md` exist) is never re-run.
- A crashed revision is re-runnable after deleting partial output.

## Convergence

After this command produces `<thread>.{N+1}/`, the orchestrator should:
1. Run `paper-figures <thread>` if any figures changed or were added.
2. Run `paper-review <thread>` on the new version.
3. If reviewer marks `advance: true`, run `paper-audit <thread>`.
4. If audit raises critical flags, loop back to `paper-revise <thread>`.

The cycle continues until:
- Audit reports no unresolved critical flags AND review marks `advance: true` (thread reaches `AUDITED`), OR
- `N+1 > max_iterations` (thread is `BLOCKED` for human review).

## Notes for the reviser agent

- **Do not regress.** If a section scored 5/6 in the prior review, the next version should keep it at ≥5/6. The `changelog.md` is the audit trail proving you did not lose ground while addressing other dimensions.
- **Critical flags trump everything — with ONE explicit exception (issue #842).** Audit and review critical flags MUST be addressed. Failing to do so is a worse outcome than declining a stylistic suggestion. A revision that does not address a flagged citation error will be re-flagged and the iteration cap will burn through quickly. **The exception is the specially-resolved `pending_dependency` flag** (from the `<thread>.{N}.pending/` sibling — see the carve-out immediately below): it is NOT a defect to fix in prose.
- **NEVER fabricate a value to clear a `pending_dependency` flag (issue #842).** A `[PENDING <source>]` marker (surfaced by the `<thread>.{N}.pending/` sibling as a `pending_dependency`-typed `critical_flag` and `nit` findings, and as an "Outstanding dependencies" note in `verdict.md`) is an **honest disclosure that a load-bearing number does not exist yet** — a training run still finishing, a benchmark queued, a vendor quote not returned. It carries its own priority tier precisely so it does NOT force `Verdict.BLOCK` the way an ordinary critical flag does — do **not** treat it as a "critical flag that must be addressed" per the bullet above. The ONLY correct resolution is to replace the marker with the **real value once it genuinely exists**; until then, **leave the marker in place** (carry it forward verbatim into `<thread>.{N+1}/main.tex`) and note in `changelog.md` that the dependency is still outstanding (`Resolution: pending — <source> not yet resolved; marker carried forward`). **Inventing a plausible-looking number to make the marker "go away" is the single most severe error available in an outward-facing paper** — it is the exact fabrication failure this convention exists to prevent. The marker is not counted against any dimension score and does not block the revise loop; it only holds the READY/AUDITED terminal transition, which is correct — the paper genuinely is not done until the value lands.
- **Declined notes are a feature, not a bug.** Sometimes the reviewer is wrong. Document the disagreement in `changelog.md` so the next reviewer can re-evaluate with full context. Generic-rubric critical flags, however, are not appropriate to decline — challenge them in changelog if you must, but address them in the prose. (The `pending_dependency` flag is neither "declined" nor "addressed in prose" — it is carried forward until the value resolves, per the carve-out above.) **Venue critical flags** (from `_review.venue.json`) are advisory: addressing them is good practice for the target venue, but declining a venue critical flag is acceptable when the trade-off is justified (document the reasoning in the changelog).
- **Vision findings (D6) require edits to figure source or LaTeX structure, NOT the prose.** Findings from the `paper-vision` critic (per `commands/paper-vision.md`, sibling `<thread>.{N}.vision/_review.json` with `kind=vision`) flag rendered-only defects in the compiled PDF that no prose edit can fix:
  - **`palette_adherence` / `mathtext_artifacts` on a plot** → a matplotlib-script fix under `figures/src/*.py` (color cycle; escaping `$` or using `usetex`/raw strings on labels), then re-run `paper-figures`.
  - **`axis_legibility` / `label_cropping` on a figure** → a `figsize` / `fontsize` / DPI / `bbox_inches="tight"` change in the same `figures/src/*.py` script.
  - **Table overflow** (a wide `tabular`/`longtable` clipped at the right margin, surfaced under `label_cropping` and often paired with the `rendered_overflow_unrecoverable` flag) → a `tabular` column-spec / `\resizebox` / `\small` / `longtable` fix in `main.tex` — not a wording change.
  - **`mathtext_artifacts` on a display equation** (overflow past the right margin, broken span) → a line-break (`\\`, `align`, `split`) or macro fix in `main.tex`.

  The default assumption "the reviser edits the prose in `main.tex`" silently underserves vision findings — surface the figure-source path or the specific LaTeX structure (table/equation) explicitly in the `changelog.md` resolution column. The `mathtext_artifact_breaks_meaning` critical flag is the highest-stakes vision finding for a paper: because LaTeX is the source-of-truth, a rendered equation that diverges from intent is a correctness defect and MUST be resolved at the source.
- **Preserve `figures/src/`.** The figurer relies on source scripts for re-render. Carry them over verbatim unless the revision deletes the corresponding figure.

## Voice and style overrides

If `.anvil/skills/paper/voice.md` exists in the consumer repo, load it and apply its guidance while revising prose. The reviser rewrites prose across every version, so it MUST honor the same author/lab voice hook the drafter reads (`commands/paper-draft.md` § "Voice and style overrides") — otherwise a tell introduced or retained during a revise pass is never scrubbed, even when the consumer's `voice.md` names it. This is the ad hoc skill-local override (a static consumer file re-read fresh each command invocation, with no version-dir footprint to carry forward), distinct from the #613 **subject**-voice tier (third-party dialogue grounding), which this command deliberately does not participate in. This is the standard anvil override pattern — see `SKILL.md` "Defaults and overrides" and the consumer's `.anvil/skills/paper/` layout.

## `_progress.json` snippet (revised version dir)

This command writes the version-dir shape documented in `anvil/lib/snippets/progress.md`. The reviser adds a `metadata.revised_from` field naming the parent version:

```json
{
  "version": 1,
  "thread": "<slug>",
  "phases": {
    "revise": { "state": "done", "started": "<ISO>", "completed": "<ISO>" }
  },
  "metadata": {
    "iteration": <N+1>,
    "max_iterations": 4,
    "revised_from": <N>
  }
}
```

When the corpus tier is active (issue #612), the reviser also carries `metadata.corpus_dirs_resolved` forward into this new `_progress.json`; the field is omitted entirely when the tier is inactive (byte-identical to pre-#612). Step 11b (issue #857) additionally writes `metadata.evidence_snapshot: { "brief_mtime": <float|null>, "refs_mtime": <float|null> }` — re-baselined for the new version dir every revision.

`metadata.revised_from` helps the orchestrator's anomaly detection catch gaps in the version chain. Use ISO-8601 UTC timestamps per `anvil/lib/snippets/timestamp.md`.

## Git sync (opt-in, off by default)

Per `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md` in an installed consumer repo): if `.anvil/config.json` exists and `git.commit_per_phase` is `true`, end this phase: stage only the dirs this phase wrote, commit as `anvil(<skill>/<phase>): <thread>.{N} [<state>]`, push if `git.push` is `true`. Git failures warn and continue — never fail the phase. When the config or knob is absent, skip this step entirely (default off).

This phase's specifics:

- **Ordering**: after `_progress.json` records the revise phase `done` on the new version dir.
- **Staging target**: ONLY the new `<thread>.{N+1}/` version dir.
- **Commit**: `anvil(paper/revise): <thread>.{N+1} [REVISED]`.
