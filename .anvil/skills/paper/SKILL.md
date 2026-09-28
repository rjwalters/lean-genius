---
name: paper
description: Draft, review, revise, and audit research papers in LaTeX (compilable PDF) using the standard anvil lifecycle plus an optional read-only literature-search critic.
domain: paper
type: skill
user-invocable: false
---

# anvil:paper — Research papers (LaTeX)

The `paper` skill produces research papers as LaTeX sources that compile to a PDF at READY state. It follows the canonical anvil lifecycle — `draft → review → revise → audit → figures` — with one paper-specific addition: an optional pre-draft **literature-search** critic (`paper-litsearch`) that the drafter and the reviser can consume. Litsearch is a sibling critic, not a phase that gates the state machine.

Papers carry sharper expectations than memos around evidence and citation correctness, so the audit phase (`paper-audit`) is a first-class part of the lifecycle (not optional), and the rubric weights rigor / evidence / citation hygiene heavily.

## Artifact contract

A **paper thread** is a single research paper authored across one or more revisions, identified by a slug (e.g., `q3-method`, `acme-bench-2026`). Each thread occupies a portfolio directory:

```
<portfolio>/
  <thread>/                       Optional thread root with brief and reference material
    BRIEF.md                      Structured or freeform brief (frontmatter + prose); when absent,
                                  paper-draft bootstraps one via an interactive interview
                                  (non-interactive / --no-interview runs keep the fail-fast;
                                  see commands/paper-draft.md § BRIEF bootstrap interview)
    refs/                         Optional reference material (datasets, prior drafts, transcripts)
    refs.bib                      Optional starter bibliography supplied by the author
  <thread>.0.litsearch/           Optional pre-draft literature-search sibling (read-only)
    notes.md                      Annotated discussion of related work + positioning
    candidates.bib                Candidate BibTeX entries the drafter may merge into refs.bib
    _progress.json                Phase state (litsearch)
  <thread>.1/                     First drafted version (immutable once written)
    main.tex                      Paper body (LaTeX, uses anvil-paper.cls by default)
    refs.bib                      Bibliography (BibTeX)
    figures/                      Figure assets and source scripts
      src/                        Optional source scripts (e.g., Python plot scripts)
      *.pdf / *.png / *.svg / *.tex   Rendered figures (TikZ .tex or rasterized)
    _progress.json                Phase state for this version
    changelog.md                  (revisions only) Maps prior critic notes to changes
  <thread>.1.review/              Reviewer output for version 1 (read-only)
    verdict.md                    Top-level decision (advance / block) + total /44
    scoring.md                    Per-dimension scores against the paper rubric
    comments.md                   Line-level comments keyed to main.tex sections
  <thread>.1.audit/               Fact / citation auditor critic sibling (read-only)
    citation-audit.md             Per-\cite{} resolution + claim-support check
    numerical-audit.md            Numbers-in-text vs figures/tables consistency
    flags.md                      Critical flags (unsupported citations, numerical disagreement)
  <thread>.1.litsearch/           (optional) Re-run litsearch after reviewer flagged missing prior work
  <thread>.2/                     Revised version (after revise consumes v1 + all critic siblings)
  ...
  <thread>.{N}/                   Terminal version, marked READY in its _progress.json
```

Versioned dirs (`<thread>.{N}/`) and critic sibling dirs (`<thread>.{N}.<critic>/`) are **immutable once their `_progress.json` records the phase as `done`**. Revisions are produced as a new version dir, never by editing in place.

The litsearch sibling is intentionally allowed at `.0.litsearch/` (before any drafted version) AND at `.{N}.litsearch/` (after a reviewer points out missing prior work). Both follow the same "N parallel critics, one reviser" rule: when present at `<thread>.{N}.litsearch/`, the next `memo-revise`-equivalent pass (`paper-revise`) consumes it alongside `.review/` and `.audit/`.

## State machine

Per-thread state, derived from on-disk evidence (not flags):

```
EMPTY → DRAFTED → REVIEWED → REVISED → … → READY → AUDITED
        ↑
        (optional .0.litsearch/ may exist before DRAFTED; it does not gate the machine)
```

| State | Evidence |
|---|---|
| `EMPTY` | No `<thread>.{N}/` directories exist (a bare `<thread>.0.litsearch/` is still EMPTY for state purposes) |
| `DRAFTED` | Latest `<thread>.{N}/` exists with `main.tex` + `refs.bib` + `_progress.json.draft == done`; no sibling review at the same `N` |
| `REVIEWED` | `<thread>.{N}.review/verdict.md` exists for the latest `N` |
| `REVISED` | A `<thread>.{N+1}/` exists after a prior `<thread>.{N}.review/` |
| `READY` | Latest `<thread>.{N}.review/verdict.md` records `advance: true` AND no unresolved critical flag (in either `.review/` or `.audit/`) AND no unresolved `[PENDING <source>]` marker in the body (`paper-review` step 7's terminal gate) |
| `AUDITED` | `<thread>.{N}.audit/` exists alongside a `READY` version AND `audit/_progress.json.audit == done` AND `flags.md` records no unresolved critical flag AND no unresolved `[PENDING <source>]` marker in the body (`paper-audit` step 6b's terminal gate) |

> **Pending-marker gate is a separate terminal condition, not a critical flag (issue #842).** An unresolved `[PENDING <source>]` marker (an honest disclosure that a load-bearing value is not yet available — a training run still running, a benchmark queued, a vendor quote not returned) holds the READY and AUDITED transitions *independently of* the "no unresolved critical flag" clause above. It is deliberately **not** implied by that clause: the deterministic `pending_marker` gate (`anvil/lib/pending_marker.py`, wired at `paper-review` step 4g / step 7 and `paper-audit` step 6b) emits the specially-resolved `pending_dependency` flag type, which `convergence.blocking_critical_flags` filters *out* of the ordinary blocking-critical set — so it never forces `advance: false`, never lowers a dimension score (see `rubric.md`), and would be missed by a reader relying on the literal "no unresolved critical flag" wording. Resolving it means replacing the marker with the real value; **never fabricate a value to force the terminal transition.**

Thresholds: **≥35/44** advances. **<35/44** requires revision. Any critical flag (from `.review/` OR `.audit/`) short-circuits regardless of total — block until addressed.

Iteration cap: default `max_iterations: 4` (`<thread>.{max_iterations}/` — `<thread>.4/` at the default — is the worst-case terminal version dir; there is no `<thread>.5/` under a default cap). The cap is configurable per-thread by writing `{ "max_iterations": <N> }` to `<thread>/.anvil.json` in the thread root. Exceeding the cap marks the thread `BLOCKED` (in the portfolio orchestrator's report) and requires human review.

### `<thread>/.anvil.json` schema

The per-thread config supports the following optional fields:

```json
{
  "max_iterations": 4,
  "venue": "neurips",
  "artifact_verify": {
    "commands": ["lake build", "lake exe check_theorems"],
    "cwd": "proof/",
    "timeout_s": 300
  }
}
```

| Field | Type | Default | Effect |
|---|---|---|---|
| `max_iterations` | int | 4 | Iteration cap (see above). |
| `venue` | string | none | Target venue slug. When set, `paper-review` also scores the paper against the matching venue YAML and writes `_review.venue.json` alongside `_review.json`. Advisory only; does not change the /44 gate. See "Venue overlays" below. |
| `artifact_verify` | object | none | Optional external-artifact verification gate (issue #663). When declared, `paper-review` runs each command in `commands` (a list of command strings) in the resolved `cwd` (thread-relative or absolute; defaults to the thread root) under a per-command `timeout_s` budget (default 300s). A failed command (non-zero exit or timeout) emits an `artifact_verify_*` critical flag that blocks the review. When absent, behavior is byte-identical to today. See "External-artifact verification" below. |

### Venue overlays (advisory)

`anvil:paper` supports **venue-pinned advisory rubrics** in addition to the generic /44. When `<thread>/.anvil.json` declares a `venue`, the reviewer scores the paper against the matching venue YAML and writes the results as a second `_review.json`-shaped file (`_review.venue.json`) in the same `.review/` sibling dir. The venue overlay is **advisory only** — the generic /44 rubric remains the sole driver of the `advance` decision, preserving the framework-wide "the skill's generic rubric is the sole advance gate" invariant. See `rubric.md` for the convergence-gate semantics and `anvil/lib/snippets/rubric.md` for the framework-wide rule.

The Python-side schema and loader live in `anvil/lib/rubric.py` (`Rubric`, `load_rubric`, `discover_venue_rubric`).

#### Shipped venue YAMLs

| Venue | File | Total | Notes |
|---|---|---|---|
| `neurips` | `rubrics/neurips.yaml` | /16 | Soundness, presentation, contribution, novelty, reproducibility. |
| `nature` | `rubrics/nature.yaml` | /15 | Broad significance, accessibility, evidence strength, novelty. |
| `arxiv` | `rubrics/arxiv.yaml` | /10 | Citation completeness, reproducibility, clarity, scope/category. |

Each YAML cites its public source in a header comment so the overlay can be updated as venue guidelines change.

#### Venue discovery (three-tier search)

`discover_venue_rubric` (in `anvil/lib/rubric.py`) searches three tiers in order — first hit wins:

1. **Per-thread**: `<thread>/.anvil/rubrics/<venue>.yaml`. For a single thread that wants a non-shipped venue overlay without touching the consumer install.
2. **Consumer-installed**: `<consumer>/.anvil/skills/paper/rubrics/<venue>.yaml` (where `<consumer>` defaults to the portfolio directory, i.e., `<thread>.parent`). For consumer-wide custom venues.
3. **Skill-shipped**: `<skill_root>/rubrics/<venue>.yaml` — the framework defaults (`neurips`, `nature`, `arxiv`). In an installed consumer repo, this is `.anvil/skills/paper/rubrics/<venue>.yaml`.

Search precedence: per-thread > consumer-installed > skill-shipped. Both override tiers are consumer-controlled; the per-thread file is more specific and wins. Skill-shipped is the fallback.

When `venue` is set but no matching YAML is found in any tier, the reviewer emits a stdout warning and proceeds with the generic rubric only. The review is not blocked by the missing venue overlay — the generic /44 gate continues to apply unchanged.

#### Adding a consumer venue

A consumer who wants to ship a custom venue (e.g., ICLR) drops a `Rubric`-shaped YAML into one of the two override tiers above. The YAML must validate against the `Rubric` schema in `anvil/lib/rubric.py` with `advisory: true`. See the shipped `rubrics/neurips.yaml` as a worked example. Set `venue: <slug>` in `<thread>/.anvil.json` to activate.

### External-artifact verification (opt-in, fail-open) — issue #663

`anvil:paper`'s render gate + numeric-consistency checker verify the *paper* artifact; the reproducibility rubric dimension (dim 5) scores whether replication *info is present*. Neither runs the **external artifact** a paper's central claim rests on — a companion Lean 4 proof repository that must `lake build` clean, a benchmark harness that must reproduce a headline number, a dataset whose checksum must match. A review pass can score a paper highly and advance it to READY while the artifact backing its central claim is silently broken (the motivating canary incident: a paper ACCEPTed with a headline theorem that did not actually hold, caught only later by manually running `lake build`).

A consumer opts a thread in by declaring an `artifact_verify` block in `<thread>/.anvil.json` (schema table above). `paper-review` step 4f then runs each declared command as a deterministic pre-scoring gate — **run the artifact, not just the PDF**. This extends the *existing* "Build / compile failure" critical-flag class (`rubric.md`) to cover external companion artifacts; it is **not** a new rubric dimension and the rubric total stays /44.

The contract mirrors the venue-overlay discovery/fail-open shape exactly (fail-open when undeclared, one-line stdout warning when declared-but-unresolvable):

- **Absent** (the default for every existing thread): no subprocess call, no `_artifact_verify.json` file, no finding — behavior is **byte-identical** to a pre-#663 review. This is the load-bearing fail-open contract.
- **Declared and resolvable**: each command in `commands` runs via `subprocess.run` in the resolved `cwd` (thread-relative or absolute; defaults to the thread root) under `timeout_s` (default 300s), subprocess-only with no new Python dependency. ALL commands run — an earlier failure does not short-circuit the rest — so a reviewer sees every failing step in one pass. A failed command (non-zero exit OR timeout) emits a `CriticalFlag` with `type` prefix `artifact_verify_<n>` (`<n>` is the 0-based command index) that routes through the unchanged `anvil/lib/critics.py::compute_verdict` path and forces `Verdict.BLOCK` — no aggregator or schema change.
- **Declared but unresolvable** (missing / non-directory `cwd`, or a command whose executable is not launchable): the gate **fails open** — a one-line stdout warning + a `major` finding in `comments.md`, and the review proceeds. A broken declaration is a defect worth surfacing, but it must not be indistinguishable from "the reviewer never checked" — so it does NOT block and does NOT silently pass as "verified".

The gate's raw stdout/stderr capture is written to `<thread>.{N}.review/_artifact_verify.json` (mirroring the render gate's `_gate.json`) for CI/operator inspection — a conditional output, NOT in the review's required-files manifest. The skill-local implementation lives at `anvil/skills/paper/lib/artifact_verify.py` (`discover_artifact_verify`, `verify`, `ArtifactVerifyResult.to_review()`/`to_critical_flags()`), modeled on `anvil/lib/render_gate.py`'s `GateResult` shape but scoped to paper per the "wait for the second consumer before generalizing" rule.

### Area Chair pattern (AI-Scientist) maps to existing N-critics-one-reviser

The "Area Chair ensemble" pattern published in AI-Scientist (Sakana, 2024) — multiple reviewer agents whose outputs are merged into a single recommendation — maps directly onto the framework's existing **N parallel critics, one reviser** primitive in `anvil/lib/critics.py::aggregate`. No separate AC role is needed in this skill; the reviser pass IS the AC pass. The venue overlay above is a parallel design move: the reviser already aggregates across all `<thread>.{N}.<critic>/` siblings, so the venue scorecard at `_review.venue.json` is consumed in the same machinery as `.review/_review.json`, `.audit/_review.json`, etc.

**READY vs AUDITED distinction.** Unlike memo (where `AUDITED` is rarely reached), `paper-audit` is part of the normal lifecycle. A paper is **not done** until it reaches `AUDITED`: the auditor's job is to verify every `\cite{}` resolves and every cited claim is actually supported. The PDF compile check (see Acceptance criteria) lives in the auditor's responsibility because it requires the bibliography to be valid.

**`paper-vision` is recommended-but-optional.** Unlike `paper-audit` (mandatory-at-`READY`), `paper-vision` does **not** gate the state machine and will **not** run unless explicitly invoked — a thread with figures can reach terminal `AUDITED` without any visual review. To keep the rendered-artifact critic from being silently skipped, the portfolio orchestrator (`paper`) surfaces the recommendation: at `READY` with figures present but no `<thread>.{N}.vision/` sibling it recommends `paper-vision` (before `paper-audit`), and at `AUDITED` in the same condition it emits a non-blocking `NEVER-VISION-CHECKED` operator note. Threads with **no figures** are never prompted for vision. This is a recommendation only — it does not change the `AUDITED` state's on-disk evidence definition below, and the vision-owned dimensions remain an additive overlay outside the /44 gate (see `rubric.md`).

**`paper-review` surfaces `EVIDENCE-DRIFT` when thread-root evidence changed after the reviewed version was written (issue #857).** Version-dir immutability means `<thread>.{N}/` is frozen at draft/revise time, but `<thread>/BRIEF.md` and `<thread>/refs/**` are mutable thread-root siblings — a terminal `READY`/`AUDITED` thread whose BRIEF or refs changed since drafting looks identical on disk to one whose evidence is current. `paper-draft`/`paper-revise` record a BRIEF/refs mtime baseline into `<thread>.{N}/_progress.json.metadata.evidence_snapshot` (`anvil/lib/evidence_drift.py`) at completion; `paper-review` step 4h compares the CURRENT thread-root mtimes against that baseline and, on drift, adds a non-blocking "Evidence drift" note to `verdict.md` naming what changed. Like `NEVER-VISION-CHECKED`, this is **purely advisory** — it does NOT change `advance`, any dimension score, or the terminal-state gate, and it is never routed through the `CriticalFlag` machinery (contrast the pending-marker gate below, which IS wired through `CriticalFlag` because it has something to *resolve*; evidence drift has nothing to resolve, only something to re-weigh). A thread with no recorded baseline (pre-#857, or no draft/revise pass since adoption) reports clean, never a false positive.

## Command dispatch

| Command | Role | Reads | Writes |
|---|---|---|---|
| `paper` | portfolio orchestrator | all `<thread>.*` dirs under cwd | (none; reports state per thread + recommends next command) |
| `paper-litsearch <thread>` | literature-search critic | `<thread>/BRIEF.md` (+ `<thread>/refs/`); for re-run, the latest `<thread>.{N}/main.tex` and any `.review/` notes about missing prior work | `<thread>.0.litsearch/` (initial) or `<thread>.{N}.litsearch/` (re-run) |
| `paper-draft <thread>` | drafter | `<thread>/BRIEF.md` (bootstrapped via interview when absent + interactive; `--no-interview` keeps the fail-fast), `<thread>/refs.bib` (if present), `<thread>/refs/`, AND any `<thread>.0.litsearch/` sibling | `<thread>.1/` with `main.tex` + `refs.bib` + `figures/` (+ `<thread>/BRIEF.md` on the bootstrap path) |
| `paper-review <thread>` | reviewer | latest `<thread>.{N}/` | `<thread>.{N}.review/` |
| `paper-vision <thread>` | vision critic (rendered-artifact) | latest `<thread>.{N}/main.tex` rendered to `paper.pdf` + per-page PNGs | `<thread>.{N}.vision/` with `_review.json` (`kind=vision`) |
| `paper-revise <thread>` | reviser | latest `<thread>.{N}/` + all `<thread>.{N}.*/` critic siblings | `<thread>.{N+1}/` with `changelog.md` |
| `paper-audit <thread>` | fact / citation auditor | latest `<thread>.{N}/` (after reaching `READY`) | `<thread>.{N}.audit/` |
| `paper-figures <thread>` | figurer | latest `<thread>.{N}/main.tex` and `figures/src/` | figures into `<thread>.{N}/figures/` |

The portfolio orchestrator (`paper`) is the user-facing entry point for status; the lifecycle commands are dispatched from it (or invoked directly by the orchestrating agent). `paper-vision` is an optional rendered-artifact critic sibling (like `paper-review`/`paper-audit`): it scores figure/table/equation defects visible only in the compiled PDF and feeds the same `paper-revise` aggregation. It does not gate the state machine on its own. See `commands/paper-vision.md`.

## Progress tracking

Each version dir and critic sibling dir contains `_progress.json`. Schema (matches memo skill, with paper-relevant phases):

```json
{
  "version": 1,
  "thread": "<thread>",
  "phases": {
    "draft":   { "state": "done",        "started": "<ISO>", "completed": "<ISO>" },
    "figures": { "state": "in_progress", "started": "<ISO>" }
  },
  "metadata": {
    "iteration": 1,
    "max_iterations": 4
  }
}
```

Phase states: `pending`, `in_progress`, `done`, `failed`. Validation is **by file existence** (does `main.tex` exist? does each `\includegraphics{figures/fig-1.pdf}` resolve to a file?), not by flag — `_progress.json` is a resume hint, not a source of truth. A phase that crashed mid-write should be re-runnable from `pending` after deleting any partial output.

The canonical `_progress.json` schema, read-merge-write recipe, and crash recovery contract live in `anvil/lib/snippets/progress.md` (in an installed consumer repo: `.anvil/anvil/lib/snippets/progress.md`); every command in this skill follows that convention. The merge is shallow: a command updates one phase, preserves all others. Critic siblings (`<thread>.{N}.review/`, `<thread>.{N}.audit/`, `<thread>.{N}.litsearch/`) follow the `human-verdict` scorecard kind per `anvil/lib/snippets/scorecard_kind.md`.

## Rubric

See `rubric.md` for the 9-dimension /44 scoring schema (paper-tuned weights, rigor + evidence + citation hygiene = 17/44 ≈ 38.6%), the ≥35 advance threshold, and the critical-flag short-circuit policy. `rubric.md` also documents the **vision-owned dimensions** (`label_cropping`, `axis_legibility`, `palette_adherence`, `mathtext_artifacts`) scored by the optional `paper-vision` critic against the *rendered* PDF — these are an additive overlay (like the venue overlay), not part of the /44 gate.

## Skill-specific phases

**`paper-litsearch` (optional, read-only critic).** Pure-LLM literature search is prone to hallucinating citations. This role MUST refuse to invent BibTeX entries. Instead, it produces:
- `notes.md` — discussion of how the paper positions against the related work the author already supplied, plus a list of **gaps** (named missing topics or specific known papers the brief mentioned but did not supply BibTeX for).
- `candidates.bib` — entries that come from author-supplied refs (re-formatted for consistency) or that the role is **explicitly told** about in the brief. Entries from "I think there's a 2023 paper about X by someone named Smith" are forbidden — the role surfaces such gaps in `notes.md` for the author to fill manually (e.g., by pasting a Semantic Scholar export into `<thread>/refs/`). Before `litsearch.state` reaches `done`, `candidates.bib` must pass the deterministic structural gate at `anvil/skills/paper/lib/bib_lint.py::lint_bib_file` (issue #998) — catches a bare `@<word>` token left outside a real entry (e.g. inside a `%`-comment discussion — BibTeX has no comment syntax) and unbalanced entry braces, before either can propagate into a version's `refs.bib` via `paper-draft`/`paper-revise`'s merge.

### Opt-in web search (`web_search: true`) — issue #424

By default this skill runs **no autonomous web search** — the anti-hallucination posture above. A consumer can opt a thread in by setting `web_search: true` (a YAML boolean, default `false`) in the per-thread `<thread>/BRIEF.md` frontmatter; in a post-#295 project layout the equivalent carrier is the `web_search` key on the thread's `documents:` entry in the project `BRIEF.md` (schema-validated as a strict bool by `anvil/lib/project_brief.py`). When the knob is absent or `false`, `paper-litsearch` and `paper-review` are byte-identical to their default no-web behavior.

When enabled:

- **`paper-litsearch`** may run live academic web searches, under the **resolver-verified-or-dropped contract**: a web-discovered candidate enters `candidates.bib` ONLY after `anvil/lib/cite.py::resolve()` returns a `BibRecord` (Crossref for DOIs, arXiv API for arXiv IDs). No resolver hit, no BibTeX entry. Unresolvable hits (`pmid`/`url` identifier kinds — unsupported in v0, `CiteResolutionError` after retries, or no extractable identifier) become **leads** in the `## Web leads (unverified)` section of `notes.md` — never citations. Verified web discoveries get a provenance table row in `notes.md` (bib key → identifier → resolver) so author-supplied vs web-verified entries stay auditable. The drafter and reviser MUST NOT cite leads; the author promotes a lead by supplying a resolvable DOI / arXiv ID.
- **`paper-review`** may run 3–5 targeted searches while scoring D4 (related-work positioning). The reviewer stays read-only with respect to citations: discovered identifiers land in `comments.md` as `related-work`-tagged leads recommending a `paper-litsearch` re-run, which centralizes the resolver verification in one command.

See `commands/paper-litsearch.md` § "Opt-in web search" and `commands/paper-review.md` Inputs for the full contracts.

**`paper-audit` (mandatory at READY).** Sharper than the generic auditor:
1. Verify every `\cite{}` in `main.tex` resolves to a real entry in `refs.bib`.
2. Spot-check that cited papers actually support the surrounding claim (the auditor reads `<thread>/refs/` for any author-supplied source PDFs / notes; for citations whose source is not on disk, the auditor flags them as "claim-support unverified — source not on disk" rather than fabricating a verification).
3. Flag claims that should have a citation but do not.
4. Flag numerical values in the text (Tables, Sec. results) that disagree with figures/tables.
5. Verify the LaTeX compiles: run `pdflatex`/`bibtex`, then rerun `pdflatex` to the "Label(s) may have changed. Rerun" fixpoint, capped at 5 total `pdflatex` passes (latexmk-style convergence loop — see `commands/paper-audit.md` step 4; or equivalent) and capture the log. A non-zero exit, any unresolved `??` citation in the rendered PDF, OR non-convergence at the 5-pass cap is a critical flag.

**`paper-figures`.** Writes into the current `<thread>.{N}/figures/` directory (not a sibling — figures are part of the artifact). The figurer SHOULD NOT invent data. Source scripts go in `figures/src/`; rendered outputs go in `figures/`. Conventions:
- **TikZ / PGFPlots** (`.tex` files in `figures/`) — for diagrams and small plots; vector-native in the compiled PDF, included via `\input{figures/diagram-1.tex}`.
- **Matplotlib** (Python in `figures/src/*.py`) — for data plots from real datasets; saved as `.pdf`, included via `\includegraphics{figures/fig-1.pdf}`.
- **External assets** (`.png` / `.svg` dropped into `figures/`) — allowed; the figurer leaves them alone.

The auditor (`paper-audit`) may re-run scripts in `figures/src/` to verify rendered outputs are current; this verification policy is documented in `paper-audit.md`.

**`paper-review` render-gate hook (deterministic pre-flight).** `paper-review` runs a deterministic render-gate pre-flight via `anvil/lib/render_gate.py` (the LaTeX-skill analog of `marp_lint` for the deck/slides skills). The gate checks page count (`page_cap=None` — paper length is venue-dependent; consumers can override per-thread via `<thread>/.anvil.json: render_gate.page_cap`), overfull boxes (>5.0pt threshold), compile success, and source-side placeholders (`TODO` / `[TBD]` / `(figure)` / `.MISSING`). The gate runs after `paper-audit` has produced `main.pdf` + `compile-log.txt`; if invoked before audit, the gate fails open with a clear stdout message and the review proceeds without enforcement. On failure, the gate emits a typed `Review(kind=tool_evidence)` with one `CriticalFlag` per failed gate dimension, which the existing `anvil/lib/critics.py::compute_verdict` path treats as `BLOCK`. See `commands/paper-review.md` step 4b.

## Templates / assets

- **Default LaTeX class**: `templates/anvil-paper.cls` — minimal generic single-column class with `\title`, `\author`, `\abstract`, standard sectioning, and `\bibliographystyle{plainnat}` baked in. Compiles cleanly with `pdflatex` + `bibtex` from a fresh checkout, no venue-specific assumptions. Supports an `anonymous` option (`\documentclass[anonymous]{anvil-paper}`) that suppresses author/affiliation rendering for double-blind submission, and a `numeric` option (`\documentclass[numeric]{anvil-paper}`) that switches citations from the default author-year `(Author, Year)` style to numeric `[7]`-style — the two options compose (`\documentclass[numeric,anonymous]{anvil-paper}`).
- **Bibliography**: BibTeX (`.bib`) is the primary format, with `natbib` for citation commands (`\citep{}`, `\citet{}`). Most venues accept either BibTeX or biblatex; BibTeX has wider tooling compatibility.
- **Venue overrides**: NeurIPS, IEEE, ACM, arXiv, etc. are handled by the standard anvil override mechanism — the consumer drops `neurips_2024.sty` (or equivalent) into `.anvil/skills/paper/templates/` in their own repo and the brief instructs the drafter to switch the documentclass line (e.g., `\documentclass{neurips_2024}`). This skill ships **no venue style files** (licensing + staleness concerns).
- **Entry-point template**: `templates/main.tex.j2` — Jinja2-style placeholder document with frontmatter hooks (`{{title}}`, `{{author}}`, `{{abstract}}`) and section skeletons (`\section{Introduction}`, etc.). The drafter substitutes from the brief and elaborates.
- **Starter bibliography**: `templates/refs.bib.j2` — empty `.bib` with a comment header explaining that entries come from either author-supplied `<thread>/refs.bib` or the litsearch sibling's `candidates.bib`.
- **Smoke test brief**: `assets/example-brief.md` — a one-page paper brief the drafter can turn into a compilable 2–4 page paper with one figure and a handful of citations. Used by the acceptance test.
- **Worked fixtures**: `examples/` — two hand-authored projects (`underclaiming-buried-lede/`, `bold-synthesis-labeled/`) reporting the *same synthetic study with the same evidence and the same bibliography, framed two ways*, plus their recorded `paper-review` siblings (33/44 `advance: false` with a named `underclaiming_buried_lede` finding; 43/44 `advance: true` with no overclaiming deduction). They are the regression fixtures for the dim 3 / dim 9 symmetry in `rubric.md` (issue #1046/#1047/#1048) and double as a reviewer-calibration reference — read the two verdicts' cold-reader and ambition-versus-inflation tables side by side. Everything in them is synthetic; see `examples/README.md`.

## Project BRIEF artifact type

`paper` is registered as a **skill-identity** `artifact_type` value in the
shared project-BRIEF registry
(`anvil/lib/project_brief.py::REGISTERED_ARTIFACT_TYPES` /
`SKILL_IDENTITY_ARTIFACT_TYPES`; issue #408, following the #386
pattern for `deck`/`slides`/`proposal`). In a shared project BRIEF, a
`documents:` entry with `artifact_type: paper` declares that this skill
owns the thread. It is NOT a memo subtype: it selects no memo rubric
overlay, and memo commands fail loudly when pointed at a `paper`-declared
thread. `anvil:project-migrate` writes this value when its BRIEF
synthesis infers a paper-class thread from a `.tex` body with a
non-`anvil-proposal` `\documentclass`.

> **Legacy `pub` compatibility (issue #694):** this skill was renamed
> from `pub` to `paper`. The BRIEF parser accepts the legacy string
> `artifact_type: pub` as an **input alias** that normalizes to the
> canonical `paper` type, so existing consumer BRIEFs authored before
> the rename keep parsing. New BRIEFs SHOULD write `artifact_type:
> paper`. There is **no** skill-level forwarding alias — re-run
> `install-anvil.sh` with `--skills=paper` (not `--skills=pub`).

## Defaults and overrides

This skill ships opinionated defaults. Consumers are expected to override liberally via `.anvil/skills/paper/` in their own repo:

- `voice.md` (optional) — Author or lab voice/style guidance both the drafter (`commands/paper-draft.md`) and the reviser (`commands/paper-revise.md`) read in addition to their base prompts, so a voice tell is scrubbed on every prose-writing pass, not just the first draft (issue #732).
- `rubric.overrides.md` (optional) — Add domain-specific critical-flag examples or adjust the open-ended "any dealbreaker a sophisticated reader would catch" instruction.
- `templates/<venue>.cls` or `templates/<venue>.sty` — Venue-specific style files. The brief tells the drafter to use them.
- `BRIEF.md.example` — Reference brief shape; freeform prose with optional YAML frontmatter is accepted.

## Migrating an existing paper

Bringing a pre-existing, hand-authored LaTeX paper into the `paper` grammar is a **first-class, sanctioned workflow** — not a workaround. There are three supported class choices, all on equal footing; pick the cheapest one that preserves your paper's rendered output:

1. **`\documentclass{anvil-paper}` (default).** Use when the paper has no load-bearing preamble and its citations are author-year. You get margins, `microtype`, colored `hyperref`, and caption styling for free.
2. **`\documentclass[numeric]{anvil-paper}`.** Use when the *only* blocker is citation style — the paper renders numeric `[7]`-style citations. The `numeric` option swaps natbib into numeric mode (`\citep`/`\citet` unchanged) while keeping all of anvil-paper's other styling. This is strictly cheaper than a full keep-original-class migration, so prefer it when nothing but the citation style collides. Compose with `anonymous` if double-blind (`\documentclass[numeric,anonymous]{anvil-paper}`).
3. **Keep the paper's original `\documentclass` (e.g. `\documentclass{article}`) and its preamble verbatim.** Use when the preamble itself collides with anvil-paper — custom theorem environments, `xcolor`/`hyperref`/`caption`/`amsthm` package-option clashes, or a citation style anvil-paper does not support even with `numeric`. Set `documentclass: article` (or the paper's original class) in the brief frontmatter and keep the paper's preamble in `main.tex` unchanged. This is a **sanctioned path on equal footing with the venue-style-file override**, not a deviation to note apologetically.

**The lifecycle is class-agnostic.** `draft → review → revise → audit → figures`, the /44 rubric scoring, and the `render_gate.py` pre-flight all operate on the compiled artifact — **none of them inspect or require `anvil-paper.cls` specifically**, and no rubric dimension penalizes not using it. Keeping your own class costs you the free styling anvil-paper provides, nothing else.

**Decision guidance:** use `\documentclass[numeric]{anvil-paper}` when only the citation style is the blocker; keep the original `\documentclass` verbatim when the preamble itself collides (theorem environments, package-option clashes, or highly customized macros). See `commands/paper-draft.md` § "Documentclass overrides" for how the brief frontmatter selects the class.

## Anonymous / double-blind submission

When the brief sets `anonymous: true`, the drafter:
1. Uses `\documentclass[anonymous]{anvil-paper}` (or the venue override's equivalent option).
2. Replaces author names and affiliations with `Author Name(s) Withheld` and `Affiliation Withheld`.
3. Scrubs identifying language in acknowledgements and self-citations (`\citet{ourpriorwork}` becomes `\citet{anonprior}` with a note in `changelog.md`).

Venue overrides handle their own anonymization on top of this.

## Git sync hook (opt-in, off by default)

Consumers running anvil under an external orchestrator (a sphere channel-agent, a Loom-style daemon) can opt in to a per-phase git commit hook so every lifecycle phase leaves the working tree clean: a repo-level `.anvil/config.json` with `git.commit_per_phase: true` (and optionally `git.push: true`) has each write-bearing paper command end its phase by staging only the dirs it wrote and committing as `anvil(paper/<phase>): <thread>.{N} [<state>]`. The full contract — knob shape, defaults-off rule, commit-message format, staging scope, warn-and-continue failure semantics, and ordering after the `_progress.json` `done` write and the #350 sidecar atomic rename — lives in `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md` in an installed consumer repo). All 7 write-bearing paper commands adopt it; the read-only `paper` portfolio orchestrator is exempt by definition. When `.anvil/config.json` is absent or the knob is false, behavior is byte-identical to a pre-#426 install — the hook is **default off**.
