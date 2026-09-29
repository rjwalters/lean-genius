---
name: paper-draft
description: Drafter command for the paper skill. Produces a new paper version directory from a brief and any pre-draft litsearch sibling. When BRIEF.md is absent in an interactive session, bootstraps one via a structured interview. Output is LaTeX (main.tex + refs.bib + figures/).
---

# paper-draft — Drafter

**Role**: drafter.
**Reads**: `<thread>/BRIEF.md`, `<thread>/refs/`, `<thread>/refs.bib` (if present), AND any `<thread>.0.litsearch/` sibling. For revise-from-feedback fallback path: also the latest `<thread>.{N}/` and all `<thread>.{N}.*/` critic siblings (but the canonical revise path is `paper-revise`).
**Writes**: `<thread>.{N+1}/` containing `main.tex`, `refs.bib`, `figures/`, and `_progress.json`. Bootstrap path only: `<thread>/BRIEF.md` synthesized from the BRIEF bootstrap interview (see below).

## Inputs

- **Thread slug** (positional argument).
- **`--no-interview`** (optional flag): deterministic opt-out of the BRIEF bootstrap interview. With this flag, a missing `BRIEF.md` always fails fast — automation gets predictable behavior without relying on the executing agent's interactivity judgment (precedent: `report-promote`'s interactive-prompt vs `--ack-file` split).
- **Brief** (`<thread>/BRIEF.md`): freeform prose with optional YAML frontmatter. If absent in an interactive session, the drafter conducts the **BRIEF bootstrap interview** (see section below) and writes the brief before proceeding. Recognized frontmatter keys (all optional):
  - `title` — paper title
  - `author` / `authors` — author list (single string or list)
  - `affiliation` — author affiliation(s)
  - `venue` — target venue (e.g., `NeurIPS-2026`, `arXiv`, `IEEE-TPAMI`)
  - `documentclass` — override the default `anvil-paper` class (e.g., `neurips_2024`, supplied by the consumer repo via `.anvil/skills/paper/templates/`)
  - `anonymous` — boolean; if `true`, drafter renders author block as `Author Name(s) Withheld` and uses the class's anonymous mode
  - `claim` — one-sentence statement of the paper's main contribution
  - `keywords` — list of keywords
- **References** (`<thread>/refs/**`): any supporting material (datasets, prior drafts, transcripts, supplied source PDFs). Treated as read-only context.
- **Author-supplied bibliography** (`<thread>/refs.bib`): copied into the version dir as the starting `refs.bib`. Additional entries from the litsearch sibling are merged.
- **Litsearch sibling** (`<thread>.0.litsearch/`): if present, the drafter consumes `notes.md` (for positioning) and `candidates.bib` (entries available to cite).

## Outputs

```
<thread>.{N+1}/
  main.tex                 Paper body (LaTeX, uses templates/anvil-paper.cls or overridden documentclass)
  refs.bib                 Bibliography (BibTeX; merged from <thread>/refs.bib and litsearch candidates.bib as needed)
  figures/                 Figure assets and source scripts (created as needed)
    src/                   Optional source scripts (e.g., Python plot scripts)
    *.tex / *.pdf / ...    Rendered figures (TikZ .tex or rasterized; paper-figures fills these)
  _progress.json           Phase state with draft: done after successful write
```

For a new thread, `N+1 == 1` so the output is `<thread>.1/`. (Note: a `<thread>.0.litsearch/` may exist as a pre-draft sibling, but `<thread>.0/` is **not** a version dir.)

## Procedure

1. **Discover thread state**: enumerate existing `<thread>.{N}/` dirs. Compute the next `N`.
2. **Resume check**: if `<thread>.{N+1}/_progress.json.draft.state == done` AND `main.tex` + `refs.bib` exist, the version is already drafted — exit early with a notice (idempotent). If `draft.state == in_progress` with no complete `main.tex`, treat as a crashed prior run: delete any partial output and re-draft.
3. **Read inputs**: load `BRIEF.md`, enumerate `<thread>/refs/`, load `<thread>/refs.bib` if present, load `<thread>.0.litsearch/notes.md` and `candidates.bib` if present. If `BRIEF.md` is **missing**, branch on interactivity (a judgment instruction for the executing agent, plus the deterministic flag):
   - **Interactive** — an operator is present who can answer AskUserQuestion-style prompts, AND `--no-interview` was NOT passed: conduct the **BRIEF bootstrap interview** (see section below), write the synthesized `<thread>/BRIEF.md`, then continue with the written brief as the contract — drafting proceeds through the remaining steps unchanged.
   - **Non-interactive** — batch / CI / orchestrated runs where no operator can answer, OR `--no-interview` was passed: fail fast with a helpful message — papers need at least a one-line claim and a target venue. The error message MUST name both remedies: (a) write `<thread>/BRIEF.md` by hand (model it on `assets/example-brief.md`), or (b) re-run `paper-draft <thread>` interactively to use the BRIEF bootstrap interview. No `BRIEF.md` is written on the fail-fast path.
   - If `BRIEF.md` **exists**, the interview never fires — the existing path is unchanged.
3b. **Load corpus grounding (conditional — issue #612)**: invoke `anvil/lib/project_brief.py::resolve_corpus_dirs(<project_dir>)` (the project root carrying the `BRIEF.md` whose frontmatter declares the top-level `corpus:` key — the same project-layout resolution `paper-review`'s `web_search` knob reads; the **corpus tier activates independently** of any other BRIEF field) per `anvil/lib/snippets/provenance.md` §Section 1. This is the project-level read-only factual ground truth, orthogonal to (and coexisting with) the per-thread `<thread>/refs/` PDFs of step 3 — see the snippet's §"Relationship to `<thread>/refs/` and `cite.py`".
   - **When active** (≥1 resolved dir): write `<thread>.{N+1}/provenance.md` **before the LaTeX body** (before step 6 instantiates `main.tex`), per `anvil/lib/snippets/provenance.md` §Section 2 — the claim→source map with one markdown table row per attributed quote (verbatim, in quotes) and per checkable factual claim (named dates, names, events, places, measured values), each mapping to its supporting corpus passage (`Source file` relative to a declared corpus dir + `Line range` + an `Anchor` — a short verbatim quoted snippet from the cited passage, per §Section 2 "Anchor: the stable identity", issue #868). The `Line range` is a hint, refreshed mechanically by `paper-revise` when it drifts; the `Anchor` is the row's stable identity, searched exhaustively by `paper-audit` step 5b's anchor-drift pre-pass. Leave `Anchor` blank only on a `NOT_FOUND` row. **Fabricating a source-line mapping is prohibited** — if no corpus passage supports a claim, cut the claim or record it with a `NOT_FOUND` source note; do NOT invent a citation. **Record the resolved corpus dir paths in `_progress.json.metadata.corpus_dirs_resolved`** (a list of path strings) so the reviewer (step 4d) and the corpus auditor (step 5b) can verify the drafter ran.
   - **When inactive** (no `corpus:` key, `corpus: null`, or `corpus: []`): omit `metadata.corpus_dirs_resolved` entirely and draft without a provenance map. Do NOT invent a provenance contract. **Byte-identical to pre-#612 behavior** — the existing `<thread>/refs/` claim-support path is unchanged.
   - **Declared-but-missing dirs**: proceed with whatever resolved (`resolve_corpus_dirs` returns `missing: true` entries, never raises); the reviewer surfaces the broken declaration as a `major` finding.
3c. **Load subject voice grounding (conditional — issue #598)**: invoke `anvil/lib/project_brief.py::resolve_subject_voice_docs(<project_dir>)` (the same `<project_dir>` as step 3b; the **subject voice tier activates independently** of the `corpus:` provenance tier and of any author-tier `voice:` keys — a `subjects`-only `voice:` block returns `[]` from `resolve_voice_docs` but entries here) per `anvil/lib/snippets/voice_grounding.md` §"Subject voice tier". A paper that renders dialogue or verbatim quotes from named study participants / interview subjects grounds those lines in the speaker's recorded register — this is the **voice/cadence-fidelity** half only; the substance-verification half (does the underlying fact/quote actually appear in the corpus?) is the step 3b provenance map's job (#612), not this tier's.
   - **When active** (≥1 declared subject): for each subject whose speech you will render in this paper, load its resolved `corpus` (spoken transcripts — the speaker's ground-truth cadence, register, characteristic openers) and its `voice_doc` when present (cadence rules + named failure modes). Ground every reconstructed line in that speaker's recorded register: the exact words are authorial license, but the line must *sound like how this speaker would say it* (clipped declaratives stay clipped; do not smooth speech into balanced multi-clause prose). **Record the consulted transcript paths in `_progress.json.metadata.subject_voice_exemplars`** — a per-subject map `{"<name>": ["<transcript path>", …], …}` — so the reviewer (step 4e) can verify grounding happened.
   - **When inactive** (no `subjects` list, empty list, or no BRIEF): omit `metadata.subject_voice_exemplars` entirely and draft without subject calibration. Do NOT invent a subject voice contract. **Byte-identical to pre-#613 behavior.**
   - **Declared-but-missing corpora**: proceed with whatever resolved (`resolve_subject_voice_docs` returns `missing: true` entries, never raises); the reviewer surfaces the broken declaration as a `major` finding.
4. **Initialize `_progress.json`**: write `phases.draft.state = in_progress`, `phases.draft.started = <ISO timestamp>`, `metadata.iteration = N+1`, `metadata.max_iterations` (inherit from `<thread>/.anvil.json` if set, else 4). When the corpus tier is active (step 3b), also record `metadata.corpus_dirs_resolved`; when the subject voice tier is active (step 3c), also record `metadata.subject_voice_exemplars`; omit each entirely when its tier is inactive.
5. **Choose documentclass**:
   - If brief frontmatter sets `documentclass`, use that. This covers both a **venue style file** (e.g., `\documentclass{neurips_2024}`, where the consumer drops the matching `.cls` / `.sty` into `.anvil/skills/paper/templates/` in their repo) **and the paper's own original class when migrating an existing paper** (e.g., `documentclass: article`, where the paper's hand-authored preamble is kept verbatim in `main.tex`). Keeping the paper's original class is an explicitly supported value, not just venue styles — see the "Documentclass overrides" section below.
   - Otherwise, use `\documentclass{anvil-paper}` (which is shipped at `anvil/skills/paper/templates/anvil-paper.cls`).
   - If `anonymous: true` in the brief, append the `anonymous` option: `\documentclass[anonymous]{anvil-paper}` (or pass through to the venue override's anonymous mechanism if known).
   - If the paper uses **numeric `[7]`-style citations** and anvil-paper is otherwise suitable, append the `numeric` option: `\documentclass[numeric]{anvil-paper}` (composes with `anonymous`: `\documentclass[numeric,anonymous]{anvil-paper}`). This is preferable to a full keep-original-class migration when citation style is the only blocker.
6. **Build `main.tex`**: instantiate `templates/main.tex.j2` with the brief's frontmatter, then write the paper body — applying the plain-language-first framework throughout: state an idea in ordinary language before naming it formally, introduce a technical term only when it adds precision or connects to prior work, and keep the plain restatement alongside the term once introduced, per `anvil/lib/snippets/plain_language.md` §"The 7-point framework" (points 1–4). This composes with, and does not relax, the "Citation-command choice" and reproducibility discipline below — precise method/notation vocabulary earns its place under point 3's exception (b) (the reader needs a compact handle to reason later in the document):
   - `\title{}`, `\author{}` (or `Author Name(s) Withheld`), `\date{}`.
   - `\begin{abstract} ... \end{abstract}` — 100–200 words; restates the claim, the method in one sentence, the key result, the contribution. Lead with the strongest honest claim from the brief's `## Strongest claim` section, not the narrowest easily-defended sub-claim.
   - `\section{Introduction}` — **states the strongest honest claim from the brief's `## Strongest claim` section in the opening paragraph, before the defensive literature apparatus** (a survey of prior constraints, a wall of qualifications, or an extended related-work-style preamble). Motivate the problem briefly, then lead with the claim; only after the claim is stated does the introduction unpack scope, method, and caveats. States the contribution explicitly (bullet list of named contributions is preferred over a single muddled paragraph), forward-references the experimental setup. When the brief's strongest-claim inventory labels a synthesis/framing/research-program claim (verbs like "we propose," "we organize," "we build," "we argue," "we conjecture," "we test" — see `rubric.md` §"Ambition is not novelty inflation"), state it at that scope and label which ingredients are inherited vs. new rather than narrowing it down to the easiest-to-defend sub-claim — a bold, properly labeled claim is not overclaiming.
   - `\section{Related Work}` — positions against prior work as informed by the litsearch sibling's `notes.md`. Cites only entries that are in `refs.bib`. Honest engagement with the closest 1–3 papers per cluster; do not pad with weakly related work. When you name an author in the prose here (common in related work), pick the cite command per the "Citation-command choice under natbib author-year" rule below — do NOT write `Name~\cite{key}`, which doubles the author name under the default class.
   - `\section{Method}` (or domain-appropriate equivalent: `\section{Approach}`, `\section{Theory}`, etc.) — describes the method with enough detail for an independent group to replicate (reproducibility dimension). Algorithms in `algorithm` environment where appropriate.
   - `\section{Experiments}` (or `\section{Results}`) — describes the experimental setup, then the results. Tables and figures are referenced from the body; the actual rendering is handled by `paper-figures` (figurer creates `figures/*.pdf` from `figures/src/*.py` or TikZ).
   - `\section{Discussion}` — interprets the results, names limitations honestly, discusses threats to validity.
   - `\section{Conclusion}` — restates the contribution and named results; no new arguments.
   - `\bibliographystyle{plainnat}` and `\bibliography{refs}` at the end (or whatever the venue override expects).
7. **Build `refs.bib`**:
   - Start with `<thread>/refs.bib` if present.
   - Merge entries from `<thread>.0.litsearch/candidates.bib` that the drafter actually cites in `main.tex`. Uncited entries stay in the litsearch sibling only — do not bloat `refs.bib` with unused entries.
   - Every `\cite{key}` in `main.tex` must have a matching `@type{key, ...}` in `refs.bib`. The drafter verifies this before marking `draft.state = done`.
   - **Cite *command* choice matters, not just resolution.** Under the default `anvil-paper` class (natbib author-year mode) bare `\cite{key}` prints "Author (Year)", so choose among `\citet` / `\citeyearpar` / `\citep` per the "Citation-command choice under natbib author-year" rule below rather than defaulting to bare `\cite{key}`.
8. **Create `figures/` skeleton**: `mkdir -p figures/src/`. Insert `\includegraphics{figures/<name>}` or `\input{figures/<name>.tex}` placeholders in the body where the brief or the structure calls for a figure. Actual figure generation is `paper-figures`'s job. If the brief supplies a `figures/src/` directory of scripts, copy them into the version dir's `figures/src/` so the figurer can pick them up.
9. **Update `_progress.json`**: `phases.draft.state = done`, `phases.draft.completed = <ISO timestamp>`.
9b. **Record the evidence-drift baseline (issue #857)**: invoke `uv run --project .anvil python -m anvil.lib.evidence_drift record <thread>/ <thread>.{N+1}/` (auto-detects the thread root as this version dir's parent). This computes the current `BRIEF.md` mtime and the max mtime under `<thread>/refs/**` and merges them into `<thread>.{N+1}/_progress.json.metadata.evidence_snapshot` — the baseline `paper-review` compares against later to detect thread-root evidence that changed after this version was drafted. Purely additive bookkeeping: never fails the draft, never gates anything. **Tooling-unavailable fallback**: when `uv` is not on `PATH` (mirrors step 4c/4b's fail-open ordering — issue #646) **or this step's write is blocked** (e.g. a consumer-repo hook that blocks Bash-channel writes — issue #1018), skip this step with a one-line notice. Do **not** hand-type a snapshot into `_progress.json` as a substitute — a hand-transcribed mtime float loses precision and can produce a false-positive drift report later (see `DRIFT_TOLERANCE_SECONDS` in `anvil/lib/evidence_drift.py`, which absorbs ordinary float noise but is not a substitute for skipping when the tool itself cannot run). The next successful draft/revise pass records the baseline instead (see `anvil/lib/evidence_drift.py`'s bootstrap-safety contract — a missing snapshot is reported as clean, never a false positive).
10. **Report**: print the path to the new version dir and a one-line status (e.g., `Drafted q3-method.1/ (main.tex: 4200 words, refs.bib: 18 entries, 3 figure placeholders)`).

## Citation-command choice under natbib author-year

The default `anvil-paper` class loads natbib in **author-year / round** mode (`templates/anvil-paper.cls:56` — `\RequirePackage[round,sort&compress,authoryear]{natbib}`). In this mode **bare `\cite{key}` is aliased to `\citet{key}`** and prints "Author (Year)" — NOT the parenthetical "(Author, Year)". So writing `Name~\cite{key}` **doubles the author name** in the rendered PDF (e.g. `Chung and Miller~\cite{chung2020}` renders as "Chung and Miller Chung and Miller (2020)"). The `.tex` source reads idiomatically, so this defect is invisible in every text-only review pass and surfaces only in the rendered PDF — prevent it at draft time by choosing the cite command from whether the author is already named in the surrounding prose:

| Author named in prose? | Use | Renders as |
|---|---|---|
| Yes | `\citeyearpar{key}` | "Chung and Miller (2020)" |
| No | `\citet{key}` | "Chung and Miller (2020) show..." |
| N/A (fully parenthetical) | `\citep{key}` | "...prior work (Chung and Miller, 2020)" |
| — | ~~bare `\cite{key}`~~ | **avoid** — aliases to `\citet{}` under author-year mode; doubles the name when the author is already named in prose |

The **`numeric` documentclass option** (`\documentclass[numeric]{anvil-paper}`) is **unaffected**: there bare `\cite{key}` renders `[N]` and there is no doubling risk, so this rule is scoped to the default (author-year) path only.

## BRIEF bootstrap interview (when BRIEF.md is absent)

When `<thread>/BRIEF.md` is absent and the session is interactive (and `--no-interview` was not passed), the drafter interviews the author and synthesizes the brief before drafting begins. The interview output is a **normal BRIEF.md** — the lifecycle is unchanged after bootstrap: no new state, no `_progress.json` schema change (the interview happens before step 4 initializes progress), and the written `BRIEF.md` is the durable, git-diffable record of the interview (consistent with the memo-revise plan-artifact philosophy).

### Question set

Conduct the interview as AskUserQuestion-style prose prompts, one topic at a time:

| # | Question | BRIEF destination | Required? |
|---|----------|-------------------|-----------|
| 1 | **Target venue** (and any venue style file the consumer has dropped into `.anvil/skills/paper/templates/`) | `venue` frontmatter (+ `documentclass` if a venue style is named) | Yes |
| 2 | **Thesis** — one-sentence statement of the main contribution | `claim` frontmatter + `## Claim` prose section | Yes |
| 3 | **Strongest-claim inventory** — the six questions in "Strongest-claim inventory (required before drafting)" below | `## Strongest claim` prose section | Yes — see that section for the no-fabrication fallback when an answer is skipped |
| 4 | **Evidence inventory** — what results/data/figures exist, where source material lives | `## Method (sketch)` + `## Experiments` prose; pointers to `refs/`, `refs.bib`, `figures/src/` | Yes (answer may be "none yet" → `# TODO(operator)` markers) |
| 5 | **Scope** — audience, rough page bound, double-blind?, keywords | `anonymous`, `keywords` frontmatter + prose framing | Yes |
| 6 | **Title / authors / affiliation** | `title`, `author`, `affiliation` frontmatter | Optional (`# TODO(operator)` markers if skipped) |
| 7 | **Web-search appetite** for litsearch (default **no** — anti-hallucination posture) | `web_search: true` emitted ONLY on explicit opt-in; the key is omitted otherwise | Optional |

### Strongest-claim inventory (required before drafting — issue #1046/#1047)

Whether `BRIEF.md` comes from this interview or is hand-authored, it MUST answer the following six questions before drafting proceeds to step 6 — these are the same questions that motivate the underclaiming/buried-lede finding the reviewer checks for in `paper-review.md`:

1. What is the strongest honest statement this work lets the authors make?
2. Why might a thoughtful reader find it surprising or generative?
3. What new experiments, arguments, or systems could that statement inspire?
4. Which part is demonstrated, which part is derived, which part is synthesis, and which part is conjecture?
5. Is the paper's opening organized around that statement, or around the easiest claim to defend?
6. If the paper succeeds, what intellectual territory will readers associate with the authors?

The brief's `## Strongest claim` section additionally states a one-paragraph **"reader should remember"** statement and a list of interesting ideas **deliberately excluded for focus** — selectivity should sharpen the central claim, not replace it with a smaller one. See `assets/example-brief.md` for a fully worked example of this section.

**Hand-authored brief, section absent**: the drafter does NOT fabricate answers on the author's behalf (same no-fabrication rule as below). It adds a `## Strongest claim` section with `# TODO(operator)` markers under each of the six questions, drafts using the `claim` frontmatter / `## Claim` prose as the interim best-available signal of the strongest claim, and notes in its step 10 report that the strongest-claim inventory was skipped and should be filled in before the next revision.

**Interactive bootstrap path**: this inventory is asked as part of the interview (question 3 in the table above); the synthesized `## Strongest claim` section is written from the author's answers, `# TODO(operator)`-marking anything skipped, per the same no-fabrication rule.

### Synthesized BRIEF shape

Model the output on `assets/example-brief.md`. The synthesized brief MUST contain:

- **Frontmatter** with at least `venue` + `claim` — the two inputs this command's step 3 declares mandatory. Other recognized keys (`title`, `author`, `affiliation`, `anonymous`, `keywords`, `documentclass`, `web_search`) appear only when the author supplied them.
- **Prose body** with the example-brief section shape: `## Motivation`, `## Claim`, `## Strongest claim` (the six-question inventory above), `## Method (sketch)`, `## Experiments` (the evidence inventory), and `## Related work` hooks.
- **`# TODO(operator)` markers** for anything the author deferred or skipped (the #408 `project-migrate` starter-synthesis precedent) — deferred answers are marked, **never fabricated**.

Note the per-thread `<thread>/BRIEF.md` is freeform prose + optional YAML frontmatter with **no strict parser** — the strict parser (`anvil/lib/project_brief.py`) governs the project-level BRIEF only. Mirroring the example-brief shape is a convention, not a schema gate.

### No-fabrication rule

The interview synthesizes structure, never substance. The drafter MUST NOT invent evidence, results, figures, datasets, or citations to fill gaps in the author's answers. A skipped or vague answer becomes a `# TODO(operator)` marker, full stop. `web_search` defaults to off and is emitted only on the author's explicit opt-in (preserving the #424 anti-hallucination posture — see `SKILL.md` § "Opt-in web search").

### Scope exclusion: project-level BRIEF

This interview bootstraps the **per-thread** `<thread>/BRIEF.md` only. It has no interplay with the post-#295 project-BRIEF `documents:` entry: project-layout enrollment stays `anvil:project-migrate --enroll` territory, and the per-thread BRIEF remains the primary carrier for this command's inputs.

## Voice and style overrides

If `.anvil/skills/paper/voice.md` exists in the consumer repo, load it and apply its guidance during drafting. This is how a lab or author customizes voice without forking the skill.

## Documentclass overrides

The skill ships `templates/anvil-paper.cls`, a generic single-column class that compiles cleanly with `pdflatex` + `bibtex`. Venue-specific styles (NeurIPS, IEEE, ACM, arXiv) are NOT vendored — licensing and staleness make that fragile. To use a venue style:

1. The consumer drops the venue style file into `.anvil/skills/paper/templates/` in their own repo (e.g., `.anvil/skills/paper/templates/neurips_2024.sty`).
2. The brief sets `documentclass: neurips_2024` (or the appropriate value).
3. The drafter emits `\documentclass{neurips_2024}` (with options as needed) and the venue style is found by `pdflatex` because it lives in the consumer's `.anvil/` overlay.

The `documentclass:` frontmatter is **not restricted to venue styles**. When migrating an existing paper with a load-bearing preamble (custom theorem environments, `xcolor`/`hyperref`/`caption`/`amsthm` option clashes, or a citation style anvil-paper does not support even with the `numeric` option), the brief MAY set `documentclass: article` (or the paper's original class) and keep the paper's preamble verbatim in `main.tex`. This is a first-class, sanctioned value — the drafter's step-5 branch has no allowlist, and the lifecycle, rubric, and render-gate are all class-agnostic. See `SKILL.md` § "Migrating an existing paper" for the full decision guidance.

This is the standard anvil override pattern — see `SKILL.md` "Defaults and overrides" and the consumer's `.anvil/skills/paper/` layout.

## Idempotence and resumability

- A completed draft (`_progress.json.draft.state == done` AND `main.tex` + `refs.bib` exist) is never overwritten. Re-running `paper-draft <thread>` on a `DRAFTED` thread is a no-op with a notice.
- A crashed draft (`_progress.json.draft.state == in_progress` with no complete `main.tex`) is re-runnable after deleting any partial output.
- Validation is by file existence (does `main.tex` exist? does `refs.bib` parse?), not solely by the progress flag.

## `_progress.json` snippet

This command writes the version-dir shape documented in `anvil/lib/snippets/progress.md`. Specifically, after a successful draft:

```json
{
  "version": 1,
  "thread": "<slug>",
  "phases": {
    "draft": { "state": "done", "started": "<ISO>", "completed": "<ISO>" }
  },
  "metadata": {
    "iteration": <N>,
    "max_iterations": 4,
    "evidence_snapshot": { "brief_mtime": 1732000000.0, "refs_mtime": null }
  }
}
```

`metadata.evidence_snapshot` is written by step 9b (`anvil/lib/evidence_drift.py::record_evidence_snapshot`, issue #857) — the BRIEF/refs mtime baseline `paper-review` compares against to detect thread-root evidence changed after this draft. Advisory bookkeeping only; absent on pre-#857 threads.

Merge rule (shallow): read existing `_progress.json` if present, update only `phases.draft` and `metadata`, preserve all other fields. Use the read-merge-write recipe in `anvil/lib/snippets/progress.md`; use ISO-8601 UTC timestamps per `anvil/lib/snippets/timestamp.md`.

## Git sync (opt-in, off by default)

Per `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md` in an installed consumer repo): if `.anvil/config.json` exists and `git.commit_per_phase` is `true`, end this phase: stage only the dirs this phase wrote, commit as `anvil(<skill>/<phase>): <thread>.{N} [<state>]`, push if `git.push` is `true`. Git failures warn and continue — never fail the phase. When the config or knob is absent, skip this step entirely (default off).

This phase's specifics:

- **Ordering**: after `_progress.json` records `phases.draft.state = done`.
- **Staging target**: ONLY the new `<thread>.{N+1}/` version dir — plus, on the BRIEF bootstrap path only, the synthesized `<thread>/BRIEF.md` staged explicitly by path (a thread-level file per the snippet's staging rules).
- **Commit**: `anvil(paper/draft): <thread>.{N+1} [DRAFTED]`.
