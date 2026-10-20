---
name: deslop
description: Iterate arbitrary AI-drafted prose (website copy, README fragments, existing markdown/HTML, pasted text) clean of AI-tell rhetoric and voice mismatch — text anvil doesn't own the lifecycle of. Deterministic rhetoric lint + LLM critique loop to convergence; NEVER auto-edits the source, emits cleaned text + rationale + a ready-to-apply diff instead.
domain: anvil
type: skill
user-invocable: true
---

# anvil:deslop — Iterate arbitrary prose clean of AI tells

The `deslop` skill is a **utility skill** (alongside `anvil:project-share`,
`anvil:project-scout`, `anvil:project-photos`, `anvil:project-book`,
`anvil:help`) — not an artifact class. It lets a consumer clean up
AI-drafted prose that lives **outside any anvil-authored project**: website
copy, a README section, an existing markdown or HTML file, or text pasted
directly into the conversation. There is no owned lifecycle, no rubric.md,
no versioned artifact identity that outlives one run — the input is
whatever prose the operator points at, and the output is a cleaned
revision plus a diff the operator applies by hand.

```
/anvil:deslop <path-or-pasted-text> [<path-or-pasted-text> ...]
    [--project <dir>]     # honor this project's voice.rhetoric_rules / voice: docs
    [--scratch <dir>]     # scratchpad root (default: a disposable temp dir)
    [--max-iterations N]  # default 4
```

Each positional argument is either an existing file path (ingested per its
suffix — see "Ingest") or, when it does not resolve to a file, treated as
pasted text verbatim.

## Why it exists

Anvil's deterministic rhetoric lint (`anvil/lib/rhetoric_lint.py`, ~28
default AI-tell rules) and the voice/persona grounding-docs contract
(`anvil/lib/project_brief.py::resolve_voice_docs`, issue #461) both already
exist and are proven across `memo`/`essay`. But they only run **inside** an
anvil artifact lifecycle — as an advisory gate on a memo render, or a
dim-2/dim-9 critic pass on an essay review. A canary consumer with
AI-drafted **website copy** (React component prose, landing-page HTML) has
no anvil-owned artifact to attach that lint/critique loop to: the text
lives in files anvil does not draft, review, or version. `deslop` is the
missing entry point — same deterministic lint, same voice-grounding
resolution, same iterate-until-converged machinery, wired to arbitrary
prose instead of a versioned thread.

## Ingest — v1 scope: markdown, HTML body, pasted text

Each input resolves to an `IngestedItem` (`lib/ingest.py`):

| Input | Extraction | `origin` |
|---|---|---|
| `.md` / `.markdown` / `.mdx` / `.txt` file | Body passed through unchanged — the file content IS the prose | Absolute file path |
| `.html` / `.htm` file | Reader-visible text only, via a minimal stdlib `html.parser` walk (`<script>`/`<style>`/`<head>`/`<title>` dropped; block-tag boundaries become paragraph breaks) | Absolute file path |
| Anything else that is not an existing file | Treated as pasted text verbatim | `None` (no file to diff against) |

**JSX/TSX/JS/TS/Vue/Svelte source files are explicitly OUT OF SCOPE for
v1** (`ingest_path` raises `UnsupportedInputError` naming the file). A
repo-wide search against the tree at issue #898's curation time found zero
existing precedent for JSX/HTML-in-source-literal parsing anywhere in
`anvil/lib/` or any skill — that is net-new parsing infrastructure, not
composition of what already exists, and is tracked as a separate follow-up.
To clean prose that lives in a JSX string literal today: extract the
target string to a markdown/HTML/plain-text file (or paste it directly),
run `deslop`, then apply the cleaned copy back into the component by hand.

Ingestion is **strictly read-only** over every input — nothing under
`lib/ingest.py` ever opens a file for writing.

## Iterate — draft → lint → critique → revise, to convergence

The loop runs inside a **scratchpad thread**, versioned exactly like every
other anvil artifact so it can reuse `anvil.lib.critics` unmodified:

```
<scratch>/<slug>/
  <slug>.1/<slug>.md          Iteration 1: the ingested prose, verbatim
  <slug>.1.critic/_review.json   Critic sibling (canonical _review.json)
  <slug>.2/<slug>.md          Iteration 2: the revised prose
  <slug>.2.critic/_review.json
  ...
  emit/
    cleaned.txt                Final prose (the operator's deliverable)
    rationale.md                Per-change rationale
    changes.diff                 Ready-to-apply diff (file inputs only)
```

`<slug>` is derived from the input's label (`lib/orchestrate.py::slugify`) —
the file basename without its extension, or `pasted-text-<N>` for pasted
input.

Per iteration:

1. **Deterministic lint pass** — `lib/orchestrate.py::lint_body` calls
   `anvil.lib.rhetoric_lint.lint_rhetoric` over the current iteration's
   prose. When `--project <dir>` is given and that project's `BRIEF.md`
   declares `voice.rhetoric_rules`, the consumer's rule file is resolved
   via `anvil.lib.project_brief.resolve_rhetoric_rules` and merged over
   the ~28 framework defaults (id collision → consumer wins; a
   declared-but-missing file surfaces as a warning finding, never a
   crash). No `--project` (or no declaration) → framework defaults only.
2. **Critic pass (LLM judgment)** — the agent scores deslop's
   two-dimension mini rubric against the lint findings and, when
   `--project <dir>` resolves voice-grounding docs
   (`lib/orchestrate.py::voice_context`, wrapping `resolve_voice_docs` —
   values → style_guide → vocabulary → corpus, the same #461 load order
   essay uses), against those docs too:
   - `rhetorical_economy` (max 10) — reuses the existing dim-9 pattern
     from `memo`/`essay`: does the prose earn its length, or pad with
     hedges/tropes/AI-tell phrasing? Every lint finding is evidence but
     the score is a holistic judgment, not a mechanical deduction.
   - `voice_adherence` (max 10) — scored **only** when `voice_context`
     resolved at least one grounding doc; otherwise **`None`** (unowned
     dimension — the schema's documented "this critic does not own this
     dim" value, never a fabricated 0). No `--project` → this dim is
     always `None` and the achievable threshold scales down accordingly
     (see below).
   The agent builds the review with `lib/orchestrate.py::new_review` and
   writes it with `write_critic_review` — both wrap the canonical
   `anvil.lib.review_schema.Review` / `_review.json` contract directly
   (this is a new skill; there is no legacy prose-triple to bridge).
3. **Aggregate + decide** — `lib/orchestrate.py::aggregate_reviews` calls
   `anvil.lib.critics.discover_critics` / `load_review` / `aggregate`
   unmodified (multiple critic siblings at one iteration mean-of-non-null
   exactly like every other skill). `decide_next` wraps
   `anvil.lib.convergence.decide_termination` directly — no convergence
   logic is reimplemented. Threshold: **16/20 (80%)** when both dims are
   scored, or **8/10 (80%)** when `voice_adherence` is unowned (an
   unowned dim must not make the achievable max unreachable) — matching
   essay's ~80% general-tier bar. Default iteration cap: 4
   (`--max-iterations`).
4. **Revise (LLM)** — below threshold and under the cap: the agent
   addresses the critic's findings/fix strings, writes the next iteration
   via `write_version`, and the loop repeats from step 1.
5. **Deterministic no-fabrication gate** (issue #922) — immediately after
   step 4 writes the next iteration, `lib/orchestrate.py::check_no_fabrication`
   diffs it against the iteration it revised and names every numeral,
   proper-noun-shaped phrase, and citation-shaped token (bracketed ref,
   URL, quoted string) that appears in the new iteration but not in the
   prior one, any resolved voice-grounding doc, or an explicit
   operator-supplied detail (`extra_allowed_tokens`). This is the
   **deterministic** counterpart to `blader/humanizer`'s LLM self-audit
   question (mining report `docs/research/919-ai-humanizer-mining.md`
   bucket c.1) — a named, mechanical finding, not something only caught if
   the critique step happens to notice it. Advisory like the lint pass;
   findings carry forward into the next iteration's critique step so they
   must be explicitly addressed or dismissed, never silently dropped.

Termination follows the framework-standard resolution order
(`anvil.lib.convergence`): a `critical_flags`-typed `no_go` short-circuits
to `NO_GO`; any other critical flag `BLOCK`s; threshold met `ADVANCE`s;
iteration cap exhausted stays `REVISE` with `MAX_ITERATIONS`; a plateaued
score (last 2 iterations within ±1, still below threshold) is `STALLED`.
`STALLED` and `MAX_ITERATIONS` are not failures — they mean "converged as
far as automated iteration usefully gets"; the operator reviews the latest
iteration's findings and either accepts it, waives a specific finding, or
iterates manually.

## Emit — cleaned text + rationale + diff, NEVER the source

`lib/orchestrate.py::emit` writes exactly three things under
`<scratch>/<slug>/emit/`, and **nothing else, anywhere**:

- `cleaned.txt` — the final iteration's prose.
- `rationale.md` — one bullet per change, in the operator's own words
  (the agent supplies this list; `emit` just renders it).
- `changes.diff` — a unified diff, **file inputs only** (`item.origin is
  not None`). For a markdown/plain-text source the diff is directly
  patch-applicable (the extracted prose IS the file body). For an HTML
  source the diff is between the *extracted* text and the cleaned text —
  this v1 does not reconstruct HTML — and the diff header says so
  explicitly (`apply manually to the HTML source`); the operator
  re-applies the wording change into the HTML by hand. Pasted-text input
  has no `changes.diff` (there is no file to diff against) — `cleaned.txt`
  is the whole deliverable.

**`deslop` never opens an ingested source file for writing, at any point
in the loop.** This is verified in tests by hashing every source before
and after a full ingest → lint → review → emit pass and asserting
byte-for-byte equality — the same read-only discipline
`anvil:project-photos` / `anvil:project-scout` apply to their own source
trees.

## Lib primitives composed

Skill-local `lib/` (per CLAUDE.md's "skill-local first, lib promotion
later" — nothing here is promoted, everything below is a direct call into
an existing `anvil/lib/` primitive):

- `ingest.py` — markdown/HTML-body/pasted-text extraction with an origin
  map (new).
- `orchestrate.py` — scratchpad-thread management, the
  `anvil.lib.rhetoric_lint.lint_rhetoric` wrapper, the
  `anvil.lib.project_brief.resolve_voice_docs` /
  `resolve_rhetoric_rules` wrappers, the `_review.json` builder/writer,
  `anvil.lib.critics.discover_critics` / `load_review` / `aggregate`
  composition, `anvil.lib.convergence.decide_termination` wiring, the
  diff/rationale emitter, and the `check_no_fabrication` wrapper (new
  orchestration; every judgment/convergence primitive it calls already
  existed).
- `no_fabrication.py` — the deterministic no-fabrication diff gate (issue
  #922): extracts numerals / proper-noun-shaped phrases / citation-shaped
  tokens through `anvil.lib.rhetoric_lint.scannable_lines`'s
  fenced-code/HTML-comment/inline-code exclusion mask (a second consumer
  of the same exclusion scope `lint_rhetoric` uses — composes with it,
  does not duplicate it), then diffs iteration N against N+1 with two
  documented exception paths: tokens resolvable from a voice-grounding doc,
  and explicit operator-supplied detail.

## State machine

There is no persistent, versioned artifact identity across separate
invocations — `deslop` is a **utility**, not a lifecycle skill. Each run's
scratchpad thread is a disposable working area (default: a temp dir; pass
`--scratch <dir>` to keep it around for inspection). State within one run
is the ordinary iterate-until-converged loop above, terminating at
`ADVANCE`, `BLOCK`, `STALLED`, or `MAX_ITERATIONS`.

## Out of scope

- **JSX/TSX/JS/TS/Vue/Svelte source-literal string extraction** — see
  "Ingest" above. Tracked as a follow-up once this v1's iterate-loop
  wiring is proven.
- **Auto-applying the diff to the source.** `deslop` computes it;
  the operator applies it. This is a hard invariant, not a default that
  can be flagged away.
- **Full HTML round-tripping.** The HTML path extracts and diffs
  *visible text*, not markup — a consumer wanting the cleaned copy woven
  back into the exact HTML structure does that by hand.

## Tests

Fixtures are shared sample text in `tests/_deslop_fixtures.py`; the lib
loads under the unique package name `deslop_lib` via
`tests/_deslop_skill_lib.py` (the #362/#367 cross-skill collision
pattern). Files (per the #58 distinct-filename convention):

- `test_deslop_ingest.py` — markdown/plain-text passthrough, HTML
  visible-text extraction (script/style/title dropped, paragraph breaks
  preserved), pasted-text ingestion, mixed-input dispatch, the
  JSX/TSX-family out-of-scope refusal.
- `test_deslop_orchestrate.py` — thread/version management, the lint pass
  (defaults, a consumer-declared `rhetoric_rules` override, and the
  no-BRIEF graceful fallback), voice-context resolution, the
  `_review.json` round trip through `anvil.lib.critics` (single- and
  multi-critic aggregation), the convergence loop's ADVANCE / REVISE /
  BLOCK / STALLED / MAX_ITERATIONS outcomes via
  `anvil.lib.convergence.decide_termination`, and diff/rationale
  emission for markdown, HTML, and pasted-text inputs.
- `test_deslop_readonly.py` — a full ingest → lint → review → emit pass
  never mutates the source file (SHA-256 before/after), and ingestion
  alone writes nothing to the source's directory.
- `test_deslop_no_fabrication.py` — the deterministic no-fabrication gate
  (issue #922): a clean revision (no new facts) passes silently, a
  revision that invents a number/name/citation is flagged, a revision
  that pulls a specific detail from a resolved voice-grounding doc is NOT
  flagged, and the fenced-code/HTML-comment/inline-code exclusion scope
  suppresses false positives on embedded code samples.
