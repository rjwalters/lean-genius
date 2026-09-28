# anvil/lib/

Framework primitives consumed by Anvil skills.

This directory holds two complementary kinds of primitive:

1. **Markdown snippets** under `snippets/` — the canonical text fragments
   skill commands reference so the conventions ( `_progress.json` shape,
   timestamp format, version-dir naming, `scorecard_kind` discriminator,
   etc.) live in one place rather than duplicated across every skill.
   Skills themselves are markdown that an LLM reads directly, so
   referencing a snippet is the right primitive for LLM-side
   coordination. Landed by #10.
2. **Python types** for the critic-output contract: `review_schema.py`,
   `review_schema.json`, and `critics.py`. These are the machine-readable
   export of the same `scorecard_kind` discriminator the snippets
   describe, intended for non-LLM consumers (CLI orchestrators, CI
   verifiers, future TypeScript callers). Landed by #26.

The snippets are the source of truth for LLM-driven authoring; the
Python types are the source of truth for programmatic validation and
aggregation. They MUST agree. When they diverge, treat it as a bug.

## Review vs audit

Two sibling critic classes share the same `_review.json` payload but
serve different roles. **Review critics** (`<thread>.{N}.review/`,
plus judgment-class specialists like `deck-narrative`, `ip-uspto-s101`)
score subjective rubric dimensions — clarity, structure, argument
coherence — from the text alone. Their payloads carry `kind: judgment`.
**Audit critics** (`<thread>.{N}.audit/`) verify dimensions that
require external tool calls — citation resolution, numeric
consistency, build cleanliness, regulatory checks. Their payloads
carry `kind: tool_evidence` and every finding records the tool
invocation that produced its evidence (see `Review._validate_kind_required_fields`).
This is the CRITIC tool-augmented-critique split applied to the
review/revise loop: audit runs post-`READY`, against a draft that has
already converged on subjective quality, so the expensive tool-call
budget is spent only where it matters. See `snippets/audit.md` for the
full distinction, load-bearing field list, and per-skill mapping.

## Layout

```
anvil/lib/
  README.md                    This file.
  snippets/                    Canonical markdown text fragments (#10).
    progress.md                _progress.json schema, merge rule, crash recovery.
    timestamp.md               ISO-8601 UTC format convention.
    version_layout.md          <thread>.{N}/ + sibling naming rules.
    thread_state.md            Derive state-machine position from on-disk evidence.
    state_machine.md           Base state machine + canonical extension points.
    rubric.md                  Weighted-dimension scoring shape (per-skill `total`;
                                /40 and /44 are the v0 observed shapes) + per-review
                                rubric_id version stamping + convergence logic.
    critics.md                 Sibling discovery + aggregation rules, plus the
                                "Orchestrator output-file guard collisions" note
                                (why required critic outputs like findings.md /
                                verdict.md are whitelisted, not renamed, under
                                harnesses with "no report files" guards).
    scorecard_kind.md          human-verdict | machine-summary discriminator.
    audit.md                   .review/ (judgment) vs .audit/ (tool-evidence)
                                distinction; load-bearing tool_calls contract;
                                perishable-vs-durable verification contract
                                (Probe / probes.json / freshness statuses, #863).
    git_sync.md                Opt-in, default-off per-phase git commit/sync
                                hook for consumers running anvil under an
                                external orchestrator (.anvil/config.json
                                `git.commit_per_phase` / `git.push` knobs,
                                commit-message shape, staging scope,
                                warn-and-continue failure semantics). (#426)
    brand-theme-porting.md     Brand-theme porting: LaTeX beamer .sty → Marp CSS.
    cite.md                    Citation primitive — on-disk shape and convention.
    directed_revision.md       Operator-directed revision (`--polish "<reason>"`).
    pending_marker.md          Pending-measurement placeholder convention.
    perspective.md             Perspective phase: pre-draft external-substrate sibling.
    provenance.md              Claim provenance: local-corpus ground-truth verification.
    voice_grounding.md         Voice grounding: persona docs as drafting/review substrate.
  figures/                     Figure conventions: palette.py + palette.json +
                                anvil.mplstyle + mermaid-theme.json.
  latex/                       Shared LaTeX substrate for LaTeX-source skills
                                (anvil-doc.cls + anvil-doc.tex.j2).
  marp/                        Marp renderer pin shared by deck + slides (#32).
    config.yml                 Canonical Marp config consumed via
                                `marp --config-file <path>` by both skills.
  memo/                        anvil:memo PDF render-chain substrate
                                (Epic #158 Phase 1). Pinned default styles +
                                pandoc HTML / xelatex templates consumed by
                                the memo-render command
                                (anvil/skills/memo/commands/memo-render.md).
    styles.css                 Pinned default theme (Helvetica/Arial, 11pt,
                                0.75in margins, @page footer page numbers).
    template.html              Pandoc HTML template (loads $title$,
                                $author$, $date$; references styles.css).
    template.tex               xelatex fallback template (minimal).
    README.md                  Override discipline + "why pinned" doc block.
  review_schema.py             Pydantic models for the unified `_review.json`
                                payload (the machine-readable canonicalization
                                of the markdown snippets above). (#26)
  review_schema.json           Auto-generated JSON Schema export of the
                                pydantic models. Regenerate with
                                `python3 -m anvil.lib.export_schema`. (#26)
  rubric.py                    Pydantic models for the rubric YAML shape
                                (generic gate rubrics — per-skill declared
                                ``total``, /40 and /44 are the v0 observed
                                shapes — plus advisory venue overlays),
                                YAML loader, three-tier venue discovery. (#33)
  rubric_schema.json           Auto-generated JSON Schema export of the
                                rubric pydantic models. Regenerate with
                                `python3 -m anvil.lib.export_schema`. (#33)
  critics.py                   Discovery, loading, aggregation, verdict
                                computation, and a legacy adapter that reads
                                the memo prose triple and the ip-uspto
                                _summary/findings/_meta triple. (#26)
  convergence.py               Pure functions for multi-iteration termination
                                decisions: `check_stable` and
                                `decide_termination`. Produces `Verdict.STALLED`
                                for plateaued threads. (#27)
  render.py                    Rendering helpers (Marp → PDF, PDF → PNGs,
                                pandoc → PDF, matplotlib figure walker)
                                consumed by per-skill vision critics. (#30)
  vision.py                    `VisionCritic` + `VisionRubric` — the
                                VLM-critique framework primitive that
                                produces `Review` objects with
                                `kind=Kind.VISION`. (#30)
  export_schema.py             One-shot exporter for review_schema.json AND
                                rubric_schema.json.
  ai_byline.py                 Opt-in AI-authorship byline renderer. (#941)
  cross_thread_refs.py         Cross-thread reference resolver. (#287)
  evidence_check.py            Quoted-evidence verifier for critic scoring
                                tables. (#464)
  evidence_drift.py            Deterministic BRIEF/refs evidence-drift
                                advisory. (#857)
  figure_content.py            Figure-content VLM critic. (#340)
  hyperlink_resolver.py        Hyperlink resolver critic. (#335, promoted
                                under #460)
  inventorship_evidence.py     Deterministic git-history evidence mining for
                                inventorship. (#445)
  latest_resolution.py         Canonical `.latest` resolution for thread
                                version directories.
  latex_render.py              Shared XeLaTeX render primitive for
                                Markdown-substrate skills.
  marp_lint.py                 Static lint mirroring the marp-vscode
                                slide-content-overflow diagnostic.
  numeric_consistency.py       Deterministic numeric-consistency gate. (#462)
  parity.py                    Pre-flight lint: shared hard claims between
                                sibling deck.md and memo.md.
  pending_marker.py            Deterministic pending-measurement placeholder
                                gate. (#841/#842)
  probe_freshness.py           Perishable-claim freshness advisory for audit
                                siblings. (#863)
  project_brief/               Typed parser for the project-level BRIEF.md
                                (package: loader/models/voice/…). (#285, #1124)
  project_detect.py            Project shape detection. (#297, #407)
  project_discovery.py         Project-as-thread-root discovery. (#284, #295)
  prose_diff.py                Word-level prose diff engine + self-contained
                                HTML renderer. (#925)
  provenance_anchor.py         Deterministic provenance.md anchor-drift
                                advisory. (#868)
  render_gate/                 Deterministic render-gate for paginated
                                artifacts (LaTeX-skill analog of marp_lint).
                                (#1129)
  revise_consistency.py        Deterministic stale-token sweep for the
                                *-revise lifecycle.
  rhetoric_lint.py             Deterministic rhetoric lint (anti-trope /
                                banned-phrase / AI-tell scan).
  rubric_overrides_suffix.py   Calibration-suffix attachment for
                                rubric_overrides reviewer integration.
  scorecard_check.py           Deterministic scorecard arithmetic validation.
                                (#392)
  sidecar.py                   staged_sidecar context manager + atomic rename
                                for crash-safe critic-sibling writes. (#350)
  skill_lib_loader.py          Shared loader for a skill's hyphenated lib/
                                package. (#879)
  tex_includes.py              Recursive \input/\include resolver for
                                multi-file LaTeX threads.
  theme.py                     Per-company theme primitive. (#322)
  vocab_reminder.py            Precision-vocabulary REMINDER tool. (#579)
  examples/
    review-example.json        Fully-populated worked example fixture.
    vision-review-example.json Fully-populated `kind: vision` example. (#30)
```

## Marp renderer pin

The framework pins **Marp** as the canonical renderer for both shipped
presentation skills (`anvil:deck`, `anvil:slides`) per the
`Presentation renderer` convention in `CLAUDE.md`. The pin has two
load-bearing halves:

1. **`anvil/lib/marp/config.yml`** — CLI-side pin. Every `marp ...`
   invocation in both skills passes
   `--config-file anvil/lib/marp/config.yml` (resolved to
   `.anvil/anvil/lib/marp/config.yml` in an installed consumer repo). Marp accepts
   this directly via its `--config-file` flag — no Python shim required;
   config-not-code lands cleanly.
2. **Per-document frontmatter** — every `deck.md` produced by either skill
   includes `math: mathjax` and `html: true` in its top frontmatter block
   (via `anvil/skills/{deck,slides}/templates/deck.md.j2`). This keeps the
   markdown source self-describing: a `deck.md` checked into a consumer
   repo renders correctly under plain `marp deck.md --pdf` even when the
   config file is missing.

When the two halves disagree, Marp's own precedence rule wins
(frontmatter > config-file > CLI flag). The framework treats divergence
as a bug — issue against this repo so the pin gets re-aligned.

### What is pinned and why

| Option | Pinned value | Why load-bearing |
|---|---|---|
| `math` | `mathjax` | Marp v3 default. Covers a wider LaTeX subset than KaTeX (the v2 default), which matters for talk-grade theorem statements and fundraising-deck unit-economics formulas. Pinned in frontmatter for self-describing source; `config.yml` omits it so the Marp default tracks any future version change without a config-file update. |
| `html` | `true` | Lets raw HTML in the source pass through into the rendered output. NOTE (verified, issue #65): `html: true` does NOT make fenced ```mermaid blocks render as diagrams in the canonical `--pdf` output — an inline ```mermaid fence emits as raw monospace code in the PDF. `--html` only passes raw HTML through; it does not execute mermaid.js during Marp's PDF render. Diagrams must be pre-rendered to PNG via `mmdc` (see `anvil/skills/{deck,slides}/commands/{deck,slides}-figures.md`). `html: true` remains pinned for genuine raw-HTML slides. |
| `allowLocalFiles` | `true` | Required for Marp to inline `![](figures/foo.png)` references. Without it, every embedded PNG renders as a broken-image icon. |
| `themeSet` | both shipped themes | Lets the per-document `theme: anvil-deck` / `theme: anvil-slides-theme` references resolve without a `--theme-set` CLI flag. Consumer overrides (`.anvil/skills/{deck,slides}/templates/<their-theme>.css`) are still respected via the per-command `--theme-set` flag, which Marp merges with this set. |

### `mmdc → PNG` as the default for diagrams

**Diagrams are rendered to PNG via `mmdc` and referenced from `deck.md` as
`![alt](figures/<name>.png)`.** Inline fenced ```mermaid blocks do NOT render
as diagrams in the canonical `--pdf` output (verified, issue #65) — they emit
as raw monospace code, because `html: true` only passes raw HTML through and
does not execute mermaid.js during Marp's PDF render. `mmdc` is therefore a
**required** dependency for any deck containing a diagram, not a fallback.

The figure commands preflight `mmdc` before any render and, if it is absent,
emit a `[blocker]` with remediation (`npm install -g @mermaid-js/mermaid-cli`,
the ~300MB+ Chromium download note, and `--puppeteerConfigFile`
`{"args":["--no-sandbox"]}` for CI/containers) plus a proactive
`<name>.png-FAILED.md` stub — rather than producing a deck that references a
nonexistent PNG. See:

- `anvil/skills/deck/commands/deck-figures.md` step 4 — `mmdc → PNG` procedure
  and required-`mmdc` preflight for the deck skill (primary, fully wired).
- `anvil/skills/slides/commands/slides-figures.md` § "Mermaid (default for
  diagrams)" — matching diagram path for the slides skill.

### Cross-reference to issue #23

The Marp renderer pin (this issue, #32) and matplotlib-side figure
conventions (issue #23, lands at
`anvil/skills/deck/assets/figure-conventions.md`) are independent. This
pin owns the Marp/renderer side: math engine, html flag, mermaid routing.
Issue #23 owns the matplotlib-side: `$`-escape conventions in axis labels,
color palette helpers, DPI defaults, accessibility (color-blind-safe
palettes).

They share the figure pipeline but touch different files. The per-skill
`assets/marp-renderer.md` cheat-sheets cross-reference both, so a deck or
slides author who needs the full pipeline view can navigate to either side
without reading the issue tracker.

### Cheat-sheets

Per-skill author-facing reference at:

- `anvil/skills/deck/assets/marp-renderer.md`
- `anvil/skills/slides/assets/marp-renderer.md`

Each documents the three figure paths (matplotlib PNG, Mermaid PNG via
`mmdc`, MathJax) with one minimal worked example per path, plus the canonical
CLI render line.

### Smoke tests

Each skill's `tests/` directory contains a `test_marp_smoke.py` that
asserts the smoke fixture (`tests/fixtures/marp-smoke/deck.md`) parses
with the pinned frontmatter and passes the `slide-content-overflow` lint.
A conditional check renders the fixture via Marp CLI when the binary is on
`PATH` and skips otherwise — matching the existing skill-test discipline
(no hard dependency on Node tooling at CI time).

## How skills consume snippets

Skills reference snippets by path. The reference is resolvable at
read-time by an LLM (which can read the file directly when needed) and
is also a clear pointer for human readers.

In SKILL.md or a command file:

> The `_progress.json` schema and the read-merge-write convention live in
> `anvil/lib/snippets/progress.md` (or `.anvil/anvil/lib/snippets/progress.md`
> in an installed consumer repo). Every command in this skill follows
> that convention.

Skill commands MAY also embed short reminders of the convention inline
(e.g., the expected JSON shape) for ease of reading, but the canonical
definition lives in the snippet file. When the snippet and an inline
copy diverge, the snippet wins.

## Install-time copying

The install script (`scripts/install-anvil.sh`) copies `anvil/lib/` to
`<consumer>/.anvil/anvil/lib/` in stage 5 (`copy framework code`). Both the
markdown snippets and the Python modules land alongside each other; the
consumer repo's commands reference them by the `.anvil/anvil/lib/snippets/<name>.md`
relative path.

## Why the original 8 snippets?

Each of the original v0 snippets corresponds to one source of duplication
observed across the six v0 skill implementations (later snippets — cite,
audit, git_sync, provenance, voice_grounding, … — were added by their own
issues and documented above). The short version per file:

| Snippet | Why |
|---|---|
| `progress.md` | Every command embedded `_progress.json` read-merge-write inline; consumer agents invented divergent JSON shapes. |
| `timestamp.md` | Each command picked its own timestamp format. |
| `version_layout.md` | `<thread>.{N}/` and sibling rules were redocumented per skill. |
| `thread_state.md` | Drafter, reviser, and orchestrator each reimplemented thread enumeration. |
| `state_machine.md` | Base state machine + extension points (pre-draft, mid-loop, post-AUDITED terminal) were rewritten per skill. |
| `rubric.md` | Per-skill weighted-dimension scoring shape + convergence logic was rewritten per skill (with subtle divergences); also documents the per-review `rubric_id` version-stamping convention so threads spanning a rubric migration record which rubric scored which iteration. |
| `critics.md` | Glob discovery + per-dim mean aggregation was rewritten per skill. |
| `scorecard_kind.md` | The 5+ critic schema shapes collapse to 2 canonical kinds via a discriminator field; this is the load-bearing primitive that unifies the others. |

## The canonical `_review.json` contract (Python types)

The Python schema in `review_schema.py` is a **single typed JSON shape**
that captures the machine-readable subset of the markdown snippets:

- It folds `_meta.json` (ip-uspto), `verdict.md` (memo) and
  `_summary.md` (ip-uspto / deck) into one payload, removing the
  per-skill divergence in disk layout.
- It pins the `kind` field reserved values (`judgment`,
  `tool_evidence`, `vision`) so #29 and #30 can ship without a
  schema-version bump.
- It pins the `verdict` enum (`ADVANCE`, `REVISE`, `BLOCK`, `STALLED`)
  to match the snippet `rubric.md` decision rule, reserving `STALLED`
  for #27's stable-score termination.

Writing `_review.json` is optional in v1: shipped skills continue to
emit the prose triples documented in `snippets/scorecard_kind.md`, and
the legacy adapter in `critics.py` bridges them. New skills SHOULD write
`_review.json` directly; migrations of the six shipped skills happen as
separate per-skill PRs.

### Field reference

#### `Review` (per-critic payload)

| Field | Type | Required | Notes |
|---|---|---|---|
| `schema_version` | `"1"` literal | yes | Pinned. Bumps require a schema-version-rolling PR; additive fields do not. |
| `kind` | `"judgment" \| "tool_evidence" \| "vision"` | yes (default `judgment`) | Distinguishes review-class critics from audit-class critics. `judgment` is the default for `.review/` siblings (subjective scoring from the text alone). `tool_evidence` is the audit-class value for `.audit/` siblings (every finding carries a `tool_calls[]` array). `vision` is reserved for #30 (rendered-artifact review). See `snippets/audit.md` and the `tool_evidence` row in the `kind` field table below. |
| `version_dir` | string | yes | Name of the version dir under review, e.g. `"acme-seed.3"`. Lets the file travel out of its sibling dir and remain locatable. |
| `critic_id` | string | yes | Stable identifier for this critic (`"memo-review"`, `"deck-market"`, `"ip-uspto-s112"`). |
| `model` | string | no | Model identifier (`"claude-opus-4-7"`). Strongly recommended for reproducibility. |
| `rubric` | string | no | Rubric identifier (`"anvil-memo-v1"`). The aggregator uses this only to surface mismatched-rubric warnings. |
| `scores` | `Score[]` | yes (non-empty) | One row per rubric dimension, including dimensions this critic doesn't own (`score: null`). |
| `findings` | `Finding[]` | no | Itemized critique items beyond the scorecard. Empty is valid (clean review). |
| `critical_flags` | `CriticalFlag[]` | no | Top-level critical flags. Any non-empty list forces `Verdict.BLOCK`. |
| `total` | int | no | This critic's own sum-of-non-null. Informational on a per-critic basis; the aggregator recomputes. |
| `threshold` | int | no | Echoed from the rubric. Required on `AggregatedReview`. |
| `verdict` | `Verdict` enum | no | Per-critic verdict, optional and ignored by the aggregator (the aggregator recomputes from the merged scorecard). |
| `rendered_artifact` | string | conditional | Required when `kind == "vision"`; path of the rendered artifact (relative to `version_dir`). |
| `probes` | `Probe[]` or null | no | Perishable external verifications performed by this critic (#863). `null` (the default, and every pre-#863 review) means **unknown freshness**, not "nothing perishable"; an explicit `[]` declares the artifact durable-only. Optional even for `kind == "tool_evidence"`. |

#### `Score` (one rubric dimension)

| Field | Type | Required | Notes |
|---|---|---|---|
| `dimension` | string | yes | Dimension identifier. Skills choose convention (memo: `"evidence_quality"`; deck: `"2_problem_clarity"`). Opaque to the lib. |
| `score` | int or null | yes | Integer in `[0, max]`, or `null` if this critic doesn't own this dim. Use `null` (not `0`) for unowned dims. |
| `max` | int (>= 1) | yes | Per-dim weight from the rubric. Echoed here so a stand-alone `_review.json` is self-contained. |
| `critical` | bool | yes (default `false`) | True when this dim has a critical-flag-worthy defect. Aggregation is logical OR. |
| `evidence_span` | string | no | Pointer to source location. Format: `"<path>:L<start>-L<end>"` for text; `"<path>:slide=<N>"` for deck/slides. |
| `fix` | string | no | One-sentence actionable revision instruction. The reviser reads this. |
| `justification` | string | no | 1–3 sentence rationale. When `score is None`, use this to point at the owning critic (`"n/a — see deck-market"`). |

#### `Finding` (one actionable critique item)

| Field | Type | Required | Notes |
|---|---|---|---|
| `severity` | `"blocker" \| "major" \| "minor" \| "nit"` | yes | `blocker` implies critical. |
| `dimension` | string | no | Dim this finding contributes to. Optional — cross-cutting findings (e.g. "fix all citations") need not name one. |
| `evidence_span` | string | no | Same format as `Score.evidence_span`. |
| `rationale` | string | yes | 1–2 sentences explaining the defect. |
| `suggested_fix` | string | yes | One sentence: what the reviser should do. |
| `tool_calls` | `ToolCall[]` | conditional | Required when parent `Review.kind == "tool_evidence"`. |

#### `Probe` (one perishable external verification, #863)

The existence of a `Probe` row **is** the perishability marker — durable
verifications (BOM arithmetic, internal consistency) simply have none. The
four required fields are the minimum a later pass needs to re-run the
check without re-deriving what to check. See `snippets/audit.md`
§"Perishable vs durable verifications" and `probe_freshness.py`.

| Field | Type | Required | Notes |
|---|---|---|---|
| `target` | string | yes | What was probed, as a stable re-addressable identifier (URL, DOI, SKU, `host:port`). The identity key across passes — keep it byte-stable. |
| `method` | string | yes | How. Free-form tag; no enforced vocabulary. Observed: `http_status`, `sha256`, `version_string`, `content_match`, `quote_validity`. |
| `observed` | string | yes | What it returned then, verbatim enough to diff against a re-probe (`"200"`, `"sha256:ab12…"`, `"working draft v8"`). |
| `checked_at` | string | yes | ISO-8601 UTC timestamp. Validated as parseable — an unreadable timestamp looks fresh to a reader and is uncheckable by a tool. |
| `claim` | string | no | The artifact claim that depends on this probe, in one line. Lets a staleness report name what would become false. |
| `evidence_span` | string | no | Same format as `Score.evidence_span`. |
| `recheck_command` | string | no | Literal command that re-runs the probe. Optional — not every probe is shell-reproducible. |
| `max_age_days` | int (>= 0) | no | Per-probe freshness budget overriding the caller's default (14). Set it for a claim with a known expiry. |

#### `ProbeLog` (the standalone `probes.json` re-probe list, #863)

The second carrier for `Probe` rows, for the prose-era auditors that do
not yet write `_review.json` (see `snippets/audit.md` §"Migration
status"). `probe_freshness.py` reads both and unions them.

| Field | Type | Required | Notes |
|---|---|---|---|
| `schema_version` | `"1"` literal | yes | Pinned, same as `Review`. |
| `version_dir` | string | yes | Name of the version dir probed. |
| `critic_id` | string | yes | Stable identifier of the critic that probed. |
| `probes` | `Probe[]` | yes (default `[]`) | An **empty** list declares "audited; nothing perishable" — materially different from an absent `probes.json`, which is unknown freshness. |

#### `CriticalFlag` (verdict-blocking flag)

| Field | Type | Required | Notes |
|---|---|---|---|
| `type` | string | yes | Short tag (`"fabricated_traction"`, `"factual_error"`). Skill-defined. |
| `justification` | string | yes | One paragraph: why this is a critical flag. |
| `evidence_span` | string | no | Pointer to the source location. |

### `evidence_span` format

The reviser uses spans to locate text for revision without re-reading the
whole artifact. v1 documents two conventions but does NOT enforce them via
regex — skills disagree on path prefixes.

| Artifact type | Format | Example |
|---|---|---|
| Text (memo, paper, report, ip-uspto spec) | `<path>:L<start>-L<end>` | `"memo.3/memo.md:L42-L58"` |
| Deck / slides | `<path>:slide=<N>` | `"deck.1/deck.md:slide=4"` |
| Drawings / figures (ip-uspto) | `<path>:fig=<N>` (suggested) | `"acme-widget.2/drawings/fig-3.svg:fig=3"` |

### `kind` field

| Value | Meaning | Schema requires |
|---|---|---|
| `judgment` | Standard rubric-scored review from text alone (review-class critics — `<skill>-review` and judgment specialists like `deck-narrative`, `ip-uspto-s101`). | Nothing extra. |
| `tool_evidence` | Audit-class review backed by external tool calls (citation resolution, build verification, numeric audit). Each finding records the tool invocations that produced its evidence. | Non-empty `tool_calls` array on every entry in `findings[]`. Enforced by `Review._validate_kind_required_fields`. |
| `vision` | Vision-model review of a rendered artifact (#30). Actively used by `anvil/lib/vision.py` and `anvil/skills/deck/commands/deck-vision.md`; reserved for slides/paper/report/ip-uspto vision critics tracked as per-skill follow-ups to #30. | `rendered_artifact`. |

The `judgment` / `tool_evidence` split codifies the `.review/` vs
`.audit/` sibling-directory distinction documented in
`snippets/audit.md`. New audit critics MUST set `kind: tool_evidence`;
the five v0 audit commands (paper, report, deck, slides, ip-uspto) ship
prose-only output today and migrate to the canonical contract via
separate per-skill follow-up issues. The `vision` value is now actively
used by `VisionCritic` (see `anvil/lib/vision.py` and the
"Rendered-artifact review" subsection below).

### `verdict` enum

| Value | Meaning |
|---|---|
| `ADVANCE` | `total >= threshold` AND no critical flag. |
| `REVISE` | `total < threshold` AND no critical flag. |
| `BLOCK` | Any critical flag is set (regardless of total). |
| `STALLED` | Stable-score termination: successive aggregated totals are within `± window` (default `1`) across the last `lookback` iterations (default `2`) AND below threshold. Produced by `anvil.lib.convergence.decide_termination` and surfaced via `compute_verdict` when `history` is provided. |

The single-iteration decision rule (ADVANCE / REVISE / BLOCK) is
implemented in `critics.py::compute_verdict` and is a pure function over
the aggregated scorecard. The multi-iteration decision (which can also
return `STALLED` or surface `termination_reason: "MAX_ITERATIONS"`) is
implemented in `convergence.py::decide_termination`; `compute_verdict`
delegates to it when called with the optional `history`, `iteration`, and
`max_iterations` arguments. Per-critic `verdict` values are ignored by
the aggregator — only the merged total + flags + history decide. This
matches the canonical decision rule documented in `snippets/rubric.md`
and the resolution order documented in `snippets/state_machine.md`.

## The discovery and aggregation API

```python
from pathlib import Path
from anvil.lib.critics import (
    discover_critics,
    load_review,
    aggregate,
    compute_verdict,
)

# 1. Walk for sibling critic dirs at this version.
sibling_dirs = discover_critics(Path("acme-seed.3"))
# -> [Path('acme-seed.3.review'), Path('acme-seed.3.market'), Path('acme-seed.3.narrative')]

# 2. Parse each sibling's _review.json (or legacy triple via the adapter).
reviews = [load_review(d) for d in sibling_dirs]

# 3. Aggregate. Pure function; no filesystem access.
agg = aggregate(reviews)

# 4. Verdict. Pure function; uses agg.threshold by default.
verdict = compute_verdict(agg)
```

### Aggregation rules

For each rubric dimension across the N per-critic `Review` objects:

- **`score`**: mean of non-null per-critic scores, rounded to nearest int
  with banker's rounding (Python `round`). The float mean is preserved on
  `AggregatedReview.score_means[dim]` so reporting doesn't lose precision.
  When no critic scored a dimension, the aggregated score is `None` and
  contributes 0 to the total.
- **`critical`**: logical OR across critics for that dim.
- **`fix`**: deduplicated union of non-null per-critic `fix` strings,
  joined with `"; "` for human readability.
- **`evidence_span`**: first non-null span in critic order.
- **`justification`**: first non-null justification in critic order.
- **`max`**: required consistent across critics for a given dim; a
  mismatch raises `ValueError`.

`findings` and `critical_flags` are deduplicated by exact-string equality
on `(severity, dimension, rationale, suggested_fix)` and
`(type, justification)` respectively. Two critics emitting *almost* the
same finding will both surface — by design, so the reviser sees both
phrasings.

These rules match the aggregation pseudocode in `snippets/critics.md` and
`snippets/scorecard_kind.md`.

### Worked example — three critics, partial ownership

Suppose three deck critics with overlapping ownership:

| Dim | deck-review (general) | deck-narrative | deck-market | mean | aggregated |
|---|---|---|---|---|---|
| 1_recommendation | 4/5 | 5/5 (owned) | null | 4.5 | 4 (banker's) |
| 2_problem_clarity | 3/6 (owned) | 4/6 | null | 3.5 | 4 (banker's) |
| 3_market_framing | null | null | 4/4 (owned, with critical=true) | 4 | 4, critical=true |
| 4_thesis | 5/6 (owned) | null | null | 5 | 5 |
| 5_evidence | 4/6 (owned) | null | null | 4 | 4 |
| 6_competitive | null | null | 3/5 (owned) | 3 | 3 |
| 7_design | 3/4 (owned) | null | null | 3 | 3 |
| 8_polish | 3/4 (owned) | null | null | 3 | 3 |
| | | | | **total** | **30** |

Banker's rounding (Python `round`): 4.5 → 4 and 3.5 → 4 (round-half-to-even).

If the threshold is `28`, the aggregated total is `30 >= 28` so the
score-based decision is ADVANCE. But dim 3 has `critical=true`, so
`compute_verdict` returns **BLOCK**. The critical flag short-circuits
regardless of total.

If dim 3's critical flag is dropped, the verdict becomes ADVANCE. If the
threshold were `32` instead of `28`, total `30 < 32` so the verdict would
be REVISE.

## Rendered-artifact review (`kind: vision`)

`anvil/lib/vision.py` ships the framework primitive for VLM critique of
rendered artifacts (decks, slides, figures). It is the architectural
answer to #23 / #24 / #25 — vision-only defects that markdown-source
critics cannot catch (mathtext italicization, vertical overflow, label
cropping, palette drift).

The vision critic is **a critic, not a new sibling family**. It writes
to `<thread>.{N}.vision/` (sibling tag = `vision`), participates in the
existing glob discovery (`discover_critics`), and contributes its
scorecard to the existing aggregator (`aggregate`) with no schema or
discovery changes. The `Kind.VISION` enum value and the
`rendered_artifact` field were reserved in #26 / PR #39 for exactly this
critic.

### Library shape

```python
from pathlib import Path
from anvil.lib.render import render_marp_to_pdf, render_pdf_to_pngs
from anvil.lib.vision import VisionCritic, default_vision_rubric

# 1. Render the deck source to PDF, then PDF to per-page PNGs.
pdf = render_marp_to_pdf(Path("acme-seed.1/deck.md"),
                         Path("acme-seed.1/deck.pdf"))
pngs = render_pdf_to_pngs(pdf, Path("acme-seed.1.vision/slides/"))

# 2. Critique. Default constructor uses the Anthropic SDK; CI/offline
#    consumers inject callback= to bypass.
critic = VisionCritic(critic_id="deck-vision")
review = critic.critique(
    images=pngs,
    rubric=default_vision_rubric(),
    version_dir="acme-seed.1",
    rendered_artifact="deck.pdf",
    context="This is a 12-slide pitch deck for a seed-stage startup.",
)

# 3. Persist. The returned Review is already validated.
(Path("acme-seed.1.vision/_review.json")
   .write_text(review.model_dump_json(indent=2)))
```

The result file is discovered and aggregated by the existing critics
primitives with zero changes — `discover_critics(Path("acme-seed.1"))`
returns `acme-seed.1.vision/` among its peers, `load_review` parses the
canonical JSON, and `aggregate` merges the vision dimensions into the
composite scorecard.

### Default rubric

The shipped rubric is six dimensions, each scored 0..5 (max_total = 30):

| Dim | What it catches |
|---|---|
| `vertical_overflow` | Content cut off below the slide bottom. The deeper companion to `marp_lint`'s slide-content-overflow rule. |
| `label_cropping` | Chart axis labels, legends, annotations truncated by the border. |
| `axis_legibility` | Font size of chart labels and tick marks vs projection scale. |
| `palette_adherence` | Figures match the theme palette (not the default matplotlib palette). |
| `mathtext_artifacts` | Italic letters adjacent to dollar signs (#23 catch); LaTeX rendered literally. |
| `slide_density` | Walls of text exceeding ~30 words / ~6 bullets per slide. |

Skills may compose their own rubric by constructing a `VisionRubric`
with a custom dimension list. The six defaults are appropriate for any
presentation-class artifact (deck, slides); paper/report/ip-uspto vision
critics may extend or replace the list.

### Critical flags

Two initial verdict-blocking flag types short-circuit the aggregated
verdict to `BLOCK`:

- `rendered_overflow_unrecoverable` — visual overflow that drops
  load-bearing information (numbers, citations, names).
- `mathtext_artifact_breaks_meaning` — `$X` rendered as italic `X`
  where the dollar sign carries semantic weight. Direct catch for #23.

These flags are vision-critic-only; other rendered defects surface as
`Finding` items with severity major/minor/nit.

### Callback injection (CI / offline / tests)

The default `VisionCritic(...)` constructor uses the Anthropic Python
SDK. Consumers without an API key (CI environments, offline development,
deterministic test suites) inject a callback:

```python
def stub_callback(images, prompt):
    return {
        "scores": [
            {"dimension": "vertical_overflow", "score": 5, "critical": False},
            {"dimension": "label_cropping",    "score": 4, "critical": False},
            {"dimension": "axis_legibility",   "score": 5, "critical": False},
            {"dimension": "palette_adherence", "score": 4, "critical": False},
            {"dimension": "mathtext_artifacts","score": 5, "critical": False},
            {"dimension": "slide_density",     "score": 4, "critical": False},
        ],
        "findings": [],
        "critical_flags": [],
    }

critic = VisionCritic(critic_id="deck-vision", callback=stub_callback)
review = critic.critique(images=[...], rubric=default_vision_rubric(),
                         version_dir="thread.1", rendered_artifact="deck.pdf")
```

The test suite in `tests/lib/test_vision.py` exercises this path
exclusively; the real Anthropic call is gated behind
`ANVIL_ENABLE_VLM_TESTS=1` for opt-in smoke testing.

### Rendering pipeline (`anvil/lib/render.py`)

The vision critic depends on `anvil/lib/render.py`, which wraps four
subprocess shell-outs:

- `render_marp_to_pdf(deck_md, out_pdf, config=None)` — Marp Markdown to
  PDF. Invokes `marp --pdf --html --config-file <config>
  --allow-local-files` so the rendered output matches what the user
  actually sees in production. The default config is
  `anvil/lib/marp/config.yml` per #32.
- `render_pdf_to_pngs(pdf, out_dir, dpi=150)` — PDF to per-page PNGs.
  Default path: `pdftoppm -r <dpi> -png ...` (poppler-utils). Fallback:
  the `pdf2image` Python wrapper, attempted only when `pdftoppm` is not
  on PATH.
- `render_pandoc_to_pdf(source_md, out_pdf, defaults=None)` — prose
  Markdown to PDF via pandoc. Reserved for future paper-vision and
  report-vision critics.
- `render_matplotlib_figures(figures_dir)` — enumerates already-rendered
  `figures/*.png`. No re-execution; the skill's `figures` command owns
  generation.

All renderers raise `RenderError` on subprocess failure or missing
binary. Tests stub via fixture PNGs and pre-built PDFs; no system
binaries are required for `pytest`.

## Legacy adapter and migration path

The lib reads three on-disk shapes today:

1. **Canonical** — `_review.json` (this contract). Preferred.
2. **Memo prose triple** — `verdict.md` + `scoring.md` + `comments.md`.
   This is the `human-verdict` shape per `snippets/scorecard_kind.md`,
   used by memo, report, paper.
3. **ip-uspto hybrid** — `_summary.md` + `findings.md` + `_meta.json`.
   This is the `machine-summary` shape per `snippets/scorecard_kind.md`,
   used by ip-uspto and the deck specialists.

When a critic sibling contains both `_review.json` and a legacy triple,
the canonical JSON wins and the legacy files are treated as stale (with a
`DeprecationWarning`). When only a legacy triple exists, the adapter
parses it into a `Review` and emits a `DeprecationWarning` per call so the
migration backlog is visible.

The adapter is a **bridge**, not a permanent home. Each shipped skill
should migrate its `<skill>-review` command to write `_review.json` in a
separate PR; the adapter exists so this issue can land without a six-skill
coordinated rewrite.

### Migration path for shipped skills

The skill migrations are out of scope for the issue that landed the
Python lib (#26). They are tracked as separate per-skill follow-up
issues. The expected sequence per skill:

1. Update `<skill>-review.md` (the review-command spec) to require writing
   `_review.json` in the canonical schema, in addition to the existing
   prose siblings.
2. (Optionally) Stop writing the prose siblings, once the reviser is
   verified to ignore them entirely.
3. Update `<skill>-revise.md` to consume `_review.json` via
   `anvil.lib.critics.load_review` instead of parsing prose.
4. Update the skill's `SKILL.md` to document the JSON contract.
5. Add an `anvil/skills/<skill>/examples/_review.example.json` for that
   skill's specific rubric.

The lib's API surface is stable from the moment #26 lands; skill
migrations can land in any order.

## Re-exporting the JSON Schema

After any change to `review_schema.py`, regenerate the JSON Schema:

```bash
python3 -m anvil.lib.export_schema
```

This rewrites `anvil/lib/review_schema.json`. The export is deterministic
(sorted keys, fixed indent) so the diff is reviewable.

## Tests

Unit tests live in `tests/lib/`:

- `tests/lib/test_review_schema.py` — schema validation, partial scorecard
  round-trip, schema rejection on missing fields and out-of-bounds scores.
- `tests/lib/test_critics.py` — discovery, loading, aggregation across
  multi-critic fixtures, verdict at threshold boundary, legacy adapter for
  both memo and ip-uspto shapes.

Run with `pytest tests/lib/` from the repo root.

## Citations: `cite.py`

The citation primitive lives in `anvil/lib/cite.py`. It is the
machine-side companion to the markdown convention documented in
`snippets/cite.md`. Public API:

```python
from pathlib import Path
from anvil.lib.cite import (
    cite,
    resolve,
    parse_identifier,
    bib_key,
    Identifier,
    BibRecord,
    IdentifierKind,
    CiteResolutionError,
    UnsupportedIdentifierError,
)

# 1. Top-level convenience: parse, resolve, write, return @key.
key = cite("10.1038/nature12373", Path("acme-seed.3"))
# -> "@kucsko2013nanometre"
# refs.bib has gained one entry; calling again is a no-op (idempotent).

# 2. Lower-level: parse + resolve separately.
identifier = parse_identifier("https://arxiv.org/abs/1706.03762")
record = resolve(identifier)
# record is a BibRecord with entry_type="misc", eprint="1706.03762", ...

# 3. Generate a bib key without writing.
plain_key = bib_key(record)             # 'vaswani2017attention'
collision_safe = bib_key(record, refs_bib=Path("acme-seed.3/refs.bib"))
```

### Supported identifier kinds (v0)

| Kind | Status | Resolver |
|---|---|---|
| `DOI` | supported | Crossref (`https://api.crossref.org/works/{doi}`) |
| `ARXIV` | supported | arXiv API (`https://export.arxiv.org/api/query?id_list=...`) |
| `PMID` | parses, raises `UnsupportedIdentifierError` on `resolve()` | follow-up |
| `URL` | parses, raises `UnsupportedIdentifierError` on `resolve()` | follow-up |

`parse_identifier` returns `IdentifierKind.URL` for any well-formed
`http(s)://` URL it does not recognize as a DOI or arXiv ID. The
`UnsupportedIdentifierError` then comes from `resolve()` so callers can
distinguish "garbage input" (raises `ValueError` at parse) from "valid
URL but no scraper in v0" (raises `UnsupportedIdentifierError` at
resolve).

### Cache

Resolved records cache to `~/.cache/anvil/cite/<kind>/<urlquoted-value>.json`.
Atomic writes (`.tmp` then `os.rename`); directory mode is `0700`. No
TTL — bibliographic records are stable. Set `CITE_CACHE_BYPASS=1` to
disable both read and write (useful when debugging the live resolver
against test cassettes).

### BibTeX shape

The writer emits BibTeX 0.99 entries with a fixed field order
(`author`, `title`, `journal`, `year`, `volume`, `number`, `pages`,
`doi`, `eprint`, `eprinttype`, `url`). Empty fields are omitted
entirely. Multi-author lists use ` and ` as the separator. One blank
line between entries.

`@article` is used for Crossref journal articles; `@misc` for arXiv
preprints (with `eprint` + `eprinttype=arxiv`). `inproceedings` and
`book` are reserved in the `BibRecord.entry_type` literal so a future
resolver can populate them without a schema bump.

### Citation-quality rubric dimensions

Skills that produce sourced artifacts opt in to two canonical rubric
dimensions:

- **`citation_recall`** — claims-with-citations / total-claims.
- **`citation_precision`** — claims-supported-by-cited-source /
  claims-with-citations.

These are first-class dimensions, not sub-fields of any other dim,
because the `Score` model enforces one integer score per dimension.
Adding them is **per-consumer rubric work**, not lib work — the lib
documents the naming convention but does not split any existing skill
rubric. See `snippets/rubric.md` for the migration pattern (split an
existing citation-related dimension to preserve the skill's declared
`total` envelope, whether /40 or /44).

### The CSL boundary

**`cite.py` produces BibTeX. CSL is per-skill.** The lib ships zero
CSL files and zero CSL knowledge. Consumer skills that want
CSL-rendered citations (e.g. `anvil:paper`, `anvil:report`) ship an
`apa-7.csl` or similar under their own `assets/` directory and the
skill's render command picks it up.

`anvil:ip-uspto` uses a custom BibTeX style (USPTO formal-requirements
formatting); the lib does not need to know about that either.

### Tests

Unit tests live in `tests/lib/test_cite.py`. Cassettes
(hand-curated Crossref JSON + arXiv Atom XML) are committed under
`tests/lib/cassettes/cite/`. `urllib.request.urlopen` is patched at
test time to return cassette content; no live network calls happen in
CI. A single `@pytest.mark.network` test against a live DOI is
provided for smoke testing and is skipped by default.

To record additional cassettes:

```bash
curl -H "User-Agent: anvil-cite/0.0.1 (https://github.com/rjwalters/anvil)" \
  "https://api.crossref.org/works/10.xxx/xxx" \
  > tests/lib/cassettes/cite/crossref-10.xxx_xxx.json

curl -H "User-Agent: anvil-cite/0.0.1 (https://github.com/rjwalters/anvil)" \
  "https://export.arxiv.org/api/query?id_list=YYMM.NNNNN" \
  > tests/lib/cassettes/cite/arxiv-YYMM.NNNNN.xml
```

## Rubric YAMLs: `rubric.py`

The rubric primitive lives in `anvil/lib/rubric.py`. It is the
machine-side companion to the rubric shape documented in
`snippets/rubric.md`. Public API:

```python
from pathlib import Path
from anvil.lib.rubric import (
    Rubric,
    RubricDimension,
    CriticalFlagDefinition,
    load_rubric,
    discover_venue_rubric,
)

# 1. Load a YAML rubric.
rubric = load_rubric(Path("anvil/skills/paper/rubrics/neurips.yaml"))
# rubric.id == "anvil-pub-neurips-v1"
# rubric.advisory == True

# 2. Discover the venue overlay for a thread (reads <thread>/.anvil.json).
overlay = discover_venue_rubric(
    thread_dir=Path("portfolio/q3-method"),
    skill_root=Path(".anvil/skills/paper"),  # or anvil/skills/paper in dev
)
# Returns the loaded Rubric, or None if .anvil.json has no venue field
# (or the venue YAML cannot be found in any tier).
```

### Two rubric kinds, one model

The same `Rubric` pydantic model serves both rubric kinds; the
discriminator is the `advisory` field:

| `advisory` | Use | sum-to-total | threshold |
|---|---|---|---|
| `false` (default) | Generic convergence-gate rubric (per-skill declared `total` — /40 and /44 are the v0 observed shapes) | enforced | required |
| `true` | Venue-pinned advisory overlay (e.g. NeurIPS, Nature) | not enforced | optional |

Advisory rubrics produce supplementary scoring the reviser consumes
for additional signal, but do NOT contribute to the convergence-gate
decision. This preserves the per-skill gate-rubric invariant — "the
skill's declared `total` means the same thing across versions of that
skill's reviewer" — while letting venue overlays declare their own
totals (NeurIPS /16, Nature /15, arXiv /10) honestly.

### Venue discovery search order

`discover_venue_rubric` reads `<thread>/.anvil.json` for the `venue`
field. When set, it searches three tiers in order — first hit wins:

1. **Per-thread**: `<thread>/.anvil/rubrics/<venue>.yaml`.
   For a single thread that wants a non-shipped venue overlay
   without modifying the consumer install.
2. **Consumer-installed**:
   `<consumer>/.anvil/skills/paper/rubrics/<venue>.yaml`
   (where `<consumer>` defaults to `<thread>.parent`, i.e., the
   portfolio dir). For consumer-wide custom venues.
3. **Skill-shipped**: `<skill_root>/rubrics/<venue>.yaml`
   (`anvil/skills/paper/rubrics/` in source; `.anvil/skills/paper/rubrics/`
   in an installed consumer repo). The framework defaults
   (`neurips`, `nature`, `arxiv`).

When the venue field is set but no matching YAML is found,
`discover_venue_rubric` returns `None`. The caller is responsible
for warning and proceeding without the overlay (the generic gate is
still in force).

### Shipped venue overlays

The `anvil:paper` skill ships three venue YAMLs at
`anvil/skills/paper/rubrics/`:

| Venue | Dimensions | Total | Critical flags |
|---|---|---|---|
| `neurips` | soundness, presentation, contribution, novelty, reproducibility | /16 | unverified_reproducibility_claim, missing_baseline, prior_work_omission |
| `nature` | broad_significance, accessibility, evidence_strength, novelty | /15 | incremental_only, jargon_inaccessible, single_experiment_claim |
| `arxiv` | citation_completeness, reproducibility, clarity_of_contribution, scope_classification | /10 | category_mismatch, unstated_contribution |

Each YAML has a header comment citing its public source so the
overlay can be updated when venue guidelines change.

### Consumer override pattern

To ship a custom venue overlay (e.g., `iclr`), a consumer drops a
`Rubric`-shaped YAML into one of:

- `<portfolio>/.anvil/skills/paper/rubrics/iclr.yaml` (portfolio-wide), or
- `<thread>/.anvil/rubrics/iclr.yaml` (single thread).

Set `venue: iclr` in `<thread>/.anvil.json` to activate. The
`Rubric` model validates `advisory: true` plus the dimensions/critical
flags exactly as for shipped overlays.

### Tests

Unit tests live in `tests/lib/test_rubric.py`. Coverage: shipped YAML
load + per-dim id pinning, advisory vs non-advisory validation,
duplicate-id rejection, three-tier discovery (including per-thread vs
consumer-installed precedence), explicit `consumer_root` argument,
malformed `.anvil.json` handling, and JSON Schema export.

## Deferred (NOT in v0)

The following are explicitly out of scope and are tracked as separate
follow-up issues:

- **`citation_lint`** — deterministic count of unsourced numeric
  claims. Skill-specific (memo/paper care; deck/slides much less).
- **`voice_lint`** — ban LLM tics ("available on request",
  "reference TBD"). Skill-agnostic but better implemented per-skill
  first to establish the pattern.
- **Two-stage terminal-state runtime hook** — the
  `AUDITED → CUSTOMER-READY` (report) and `AUDITED → FINALIZED`
  (ip-uspto) pattern is currently inline per-skill. Will be promoted
  to a first-class lib primitive when a third skill needs it.
- **Per-skill audit-command migration to `kind: tool_evidence`** —
  the five v0 audit commands (`paper-audit`, `report-audit`,
  `deck-audit`, `slides-audit`, `ip-uspto-audit`) currently emit prose
  output plus `scorecard_kind` metadata; migrating each to write
  `_review.json` with `kind: tool_evidence` and `tool_calls[]` per
  finding lands as five separate follow-up issues. The framework-level
  contract is documented in `snippets/audit.md`; the legacy adapter in
  `critics.py` bridges the gap until migrations land.

## See also

- `anvil/skills/*/SKILL.md` — each skill's authoritative definition,
  with cross-references back to the snippets.
- `anvil/skills/README.md` — skill layout convention.
- `anvil/lib/examples/review-example.json` — fully-populated example
  of the `_review.json` contract.
- Repository `README.md` — anvil's overall design principles.
