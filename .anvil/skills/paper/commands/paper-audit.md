---
name: paper-audit
description: Fact and citation auditor for the paper skill. Verifies every cite resolves, spot-checks claim support, flags numerical inconsistencies, and verifies the LaTeX compiles to a clean PDF. Critical for paper credibility.
---

# paper-audit — Fact / citation auditor

**Role**: auditor (sibling critic, read-only).
**Reads**: latest `<thread>.{N}/main.tex`, `<thread>.{N}/refs.bib`, `<thread>.{N}/figures/`, AND `<thread>/refs/` for any author-supplied source PDFs / notes used to verify claim support.
**Writes**: `<thread>.{N}.audit/` with `citation-audit.md`, `numerical-audit.md`, `flags.md`, `compile-log.txt`, and `_progress.json`. **Conditionally** (corpus tier active — issue #612), also a SEPARATE `<thread>.{N}.corpus-audit/` sibling with `_review.json` (`kind: tool_evidence`), `_meta.json`, `_progress.json`, and `corpus-audit.md`.

This is the **mandatory final-quality phase** for papers. Unlike memo (where auditor is optional), no paper reaches `AUDITED` without `paper-audit`. The auditor's findings carry equal weight to the reviewer's critical flags and block advancement until resolved.

## Why this exists as a distinct phase

The reviewer's job is to score a paper against the rubric (rigor, evidence, clarity, ...). The auditor's job is **fact-check**: every `\cite{}` resolves, cited papers actually support the surrounding claim, numerical values are consistent across text/figures/tables, and the paper compiles cleanly. These are mechanical or near-mechanical checks that benefit from a separate pass without the reviewer's scoring overhead.

## Inputs

- **Thread slug** (positional argument).
- **Latest version directory**: highest `N` with `<thread>.{N}/main.tex`. The auditor runs after the reviewer marks `advance: true` (i.e., the paper has reached `READY`). It is acceptable (and sometimes useful) to run the auditor earlier — e.g., on a draft that has not yet been reviewed — to surface fact issues before review effort is spent.
- **Author-supplied sources** (`<thread>/refs/**`): any PDFs, notes, or transcripts the author supplied. Used to verify claim support. **Citations whose source is not on disk are flagged "claim-support unverified — source not on disk" rather than fabricating a verification.**
- **Build toolchain**: `pdflatex`, `bibtex` (or `biber` if the consumer's documentclass uses biblatex). The auditor verifies the LaTeX compiles cleanly.

## Outputs

```
<thread>.{N}.audit/
  citation-audit.md    Per-cite{} resolution check + claim-support spot-check results
  numerical-audit.md   Numbers-in-text vs figures/tables consistency check
  flags.md             Critical flags (unresolved cites, claim-support failure, numerical inconsistency, build failure)
  compile-log.txt      Captured stdout/stderr from the pdflatex + bibtex compile cycle
  _meta.json           { critic, scorecard_kind: "human-verdict", started, finished, model, schema_version }
  _progress.json       Phase state (phase: audit)

<thread>.{N}.corpus-audit/   (conditional — corpus tier active, issue #612; a SEPARATE sibling)
  _review.json         kind: tool_evidence; per-row five-way classification findings with
                       non-empty tool_calls on every MISMATCH / NOT_FOUND / FABRICATED; the
                       five fabrication-class critical_flags route through Verdict.BLOCK
  _meta.json           { critic: "paper-corpus-audit", scorecard_kind: "tool_evidence", started, finished, model, schema_version }
  _progress.json       Phase state + metadata.provenance_summary (six counters, §Section 7)
  corpus-audit.md      Human-readable classification table (Claim | Source file | Line range | Classification | Notes)
```

**Atomicity** (issue #350, #376): the audit sibling dir is written **atomically** via the staged-sidecar primitive at `anvil/lib/sidecar.py`. The six files (`citation-audit.md`, `numerical-audit.md`, `flags.md`, `compile-log.txt`, `_meta.json`, `_progress.json`) are staged under a leading-dot sibling `.<thread>.{N}.audit.tmp/` during writing; on clean completion the staging dir is renamed (one atomic `Path.rename`) to the final `<thread>.{N}.audit/` name. A mid-cycle interrupt leaves a `.<thread>.{N}.audit.tmp/` dir on disk that the next invocation's `cleanup_one_staging(<thread>.{N}.audit)` per-critic sweep removes; the final-named dir never exists in partial form. Discovery (`anvil/lib/critics.py::discover_critics`) is unchanged — the leading-dot staging shape is invisible to the discovery glob.

## Procedure

1. **Discover state**: find the highest `N` with `<thread>.{N}/main.tex`. Then **sweep a stale staging dir from a prior interrupt of THIS critic on THIS version** by invoking `anvil/lib/sidecar.py::cleanup_one_staging(<thread>.{N}.audit)` (the per-critic, parallel-safe sweep — issue #376). This removes ONLY a leftover `.<thread>.{N}.audit.tmp/` from a previously-killed run of this same critic on THIS version. Sibling critics' in-flight staging dirs under the same portfolio root are NOT touched (issue #350, #376). The sweep is idempotent and logs at INFO level when it removes a dir. If `<thread>.{N}.audit/` exists (the atomic-rename contract guarantees the dir only exists when complete), exit early with a notice (idempotent).
2. **Resume check**: per the staged-sidecar shape introduced in issue #350, a partial audit left behind by a mid-cycle interrupt manifests as a leading-dot `.<thread>.{N}.audit.tmp/` directory (NOT as a partially-filled `<thread>.{N}.audit/`). The sweep in step 1 has already removed any such partial. Backwards-compat: if a legacy pre-#350 `<thread>.{N}.audit/` exists WITHOUT `flags.md`, delete the dir and re-audit.
3. **Open the staged sidecar** for the audit dir by invoking the context manager `anvil/lib/sidecar.py::staged_sidecar(final_dir=<thread>.{N}.audit, required_files=["citation-audit.md", "numerical-audit.md", "flags.md", "compile-log.txt", "_meta.json", "_progress.json"])`. Every file write below MUST land **inside the yielded staging directory** (the path of the shape `.<thread>.{N}.audit.tmp/`), NOT inside the final `<thread>.{N}.audit/` path. On clean context exit, the primitive verifies the manifest, then atomically renames the staging dir to its final name (issue #350). Then, **inside the staging dir**, initialize `_progress.json`: `phases.audit.state = in_progress`, `phases.audit.started = <ISO>`, `for_version = N` (per `anvil/lib/snippets/progress.md`). Also initialize `_meta.json` with `scorecard_kind: human-verdict` (see `anvil/lib/snippets/scorecard_kind.md`); paper-audit ships task-specific files (`citation-audit.md`, `numerical-audit.md`, `compile-log.txt`, `flags.md`) alongside the scorecard-kind declaration.

   **Non-Python-driver ordering (fail-open, manual fallback)** — issue #645: `staged_sidecar` is a Python context manager. A manual/agent session with **no orchestrating Python driver** cannot hold its `with` block open across the file writes below (it writes files with its own editing tool between discrete steps), so it MUST use the equivalent CLI shim rather than writing straight into the final `<thread>.{N}.audit/` dir (which silently reopens the #350 partial-write defect this primitive exists to close). Two tiers, in preference order:

   1. **Primary — `python -m anvil.lib.sidecar` CLI shim** (the common case). In an installed consumer repo (anvil vendored under `.anvil/`, not on `sys.path`), prefix every invocation below with `uv run --project .anvil` (the `.anvil/pyproject.toml` + `uv sync --project .anvil` shipped by the installer since #230 make the module resolvable from the consumer root — the same shape the other `anvil.lib.*` critics already use); in the anvil source repo the bare `python -m anvil.lib.sidecar` form works as-is. This wraps the *exact same* `staged_sidecar` code, so the manifest check + single atomic `Path.rename` are enforced by code, not agent discipline:
      - `uv run --project .anvil python -m anvil.lib.sidecar stage <thread>.{N}.audit` → prints the staging path (`.<thread>.{N}.audit.tmp/`). (Refuses with a nonzero exit if `<thread>.{N}.audit/` already exists — matching `staged_sidecar`'s `FileExistsError` refuse-to-overwrite guard.)
      - Write **all** required files (`citation-audit.md`, `numerical-audit.md`, `flags.md`, `compile-log.txt`, `_meta.json`, `_progress.json`) into that printed staging path — never into the final `<thread>.{N}.audit/` name.
      - `uv run --project .anvil python -m anvil.lib.sidecar commit <thread>.{N}.audit --required citation-audit.md,numerical-audit.md,flags.md,compile-log.txt,_meta.json,_progress.json` → verifies the manifest, then atomically renames staging → final. **Nonzero exit (1) leaves the staging dir in place with no partial final dir** if any required file is missing — the `SidecarIncompleteError` analog; fix the gap and re-`commit`.
      - The stale-staging sweep of step 1 has an exact CLI analog: `uv run --project .anvil python -m anvil.lib.sidecar cleanup <thread>.{N}.audit` (the parallel-safe per-critic sweep, issue #376).
   2. **Last resort — manual `mv`-based staging** when even `python`/`uv` is unavailable. Reproduce the staging contract by hand: (a) at entry, sweep any leftover `rm -rf .<thread>.{N}.audit.tmp/` (the `cleanup_one_staging` analog); (b) `mkdir .<thread>.{N}.audit.tmp/` and write **every** required file into it — writing `_progress.json` **last**, so a mid-write interrupt is caught by the missing-manifest check rather than producing a final-named partial; (c) confirm the staging dir holds the full required set — use a count check (`[ "$(ls -1 .<staging-dir> | wc -l)" -eq <N> ]`) or an `ls`-based presence check rather than per-file `[ -f ]`, which can false-negative under a restricted-`stat` sandbox — **then** `mv .<thread>.{N}.audit.tmp <thread>.{N}.audit` as the **last** step (POSIX `mv` on a same-filesystem dir-to-dir rename is atomic, matching `Path.rename`). Do NOT create `<thread>.{N}.audit/` before all files are staged. **Record the fallback durably** so a reader can tell atomicity was reproduced by hand rather than tool-verified: stamp `_meta.json` with `"atomicity_fallback": "manual-mv"` (e.g. `sidecar: staged_sidecar CLI unavailable (uv/python not on PATH); atomicity reproduced via manual mv this pass`). Absent this note the manual staging is indistinguishable from an unsafe direct write.

   The two tiers land a byte-identical on-disk result to the `staged_sidecar` context-manager path; they exist only to give a Python-less session a code-enforced (tier 1) or contract-faithful (tier 2) route to the same atomicity guarantee. When an orchestrating Python driver IS present, use `staged_sidecar` directly as documented above — the CLI shim is not needed. (If your agent harness pattern-matches and rejects a findings-style critic filename such as `flags.md` on a `Write`, a Bash-heredoc write into the staging dir is an accepted fallback — see `anvil/lib/snippets/critics.md` §"Orchestrator output-file guard collisions".)

4. **Compile the paper** (build verification) — **convergence loop, not a fixed pass count**:

   A fixed `pdflatex → bibtex → pdflatex → pdflatex` cycle is a heuristic that converges for the common case but is **not** LaTeX's actual termination condition. LaTeX's own convergence signal is the line `LaTeX Warning: Label(s) may have changed. Rerun to get cross-references right.`, emitted at the end of any pass whose `.aux` output differs from the previous pass's. A numeric-cite paper (`[1]`, `[2]`, …) whose citation resolution (`[?] → [16]`) changes line lengths near a page boundary can shift a page break on the *second* post-bibtex pass, so its `.aux` still differs and a *third* post-bibtex pass is needed to stabilize. Stopping at the fixed two post-bibtex passes can ship a stale `\pageref` and make a log-grepping audit report a false-clean paper (the emitted rerun warning is real, but nothing acts on it). Run to the `.aux` fixpoint instead — latexmk semantics:

   - Run `pdflatex -interaction=nonstopmode main.tex` in `<thread>.{N}/`.
   - Run `bibtex main` (or `biber main` if biblatex is in use).
   - **Then repeat `pdflatex -interaction=nonstopmode main.tex`** until **either** (a) the most recent pass's log does **not** contain `Label(s) may have changed. Rerun to get cross-references right.`, **or** (b) **5 total `pdflatex` passes** have run (the latexmk-style safety cap — prevents an infinite loop on a genuine oscillating reference, e.g. a `\pageref` cycle that never stabilizes). The **floor is unchanged**: a minimum of 2 `pdflatex` passes always run after `bibtex` (bibtex needs pass 1's `.aux` to resolve cites; pass 2 needs the `.bbl` to render them). No further `bibtex` reruns are needed — the citation list is stable after pass 1; only `pdflatex` reruns to settle page breaks.
   - **Detecting convergence**: grep the **most recent** pass's log (not the concatenated log) for the literal string `Label(s) may have changed. Rerun to get cross-references right.`. Its **absence** at the end of a pass IS the fixpoint signal (exactly latexmk's rerun-detection heuristic). *Optional stronger cross-check* the auditor MAY run if log-grepping is ambiguous (a custom document class could suppress the warning text while still mutating `.aux`): diff the `.aux` file between the two most recent passes — byte-identical `.aux` is a robust fixpoint signal, matching the canary's own "pass-4 `.aux` byte-identical to pass-3" verification.
   - Capture all stdout and stderr from **every** pass actually run (now a variable 2–5 `pdflatex` invocations) to `<thread>.{N}.audit/compile-log.txt` — unchanged file-write contract (issue #668/#677's overfull-box dedup keys on `(line, amount, kind)` and already tolerates a variable, not fixed, pass count in the concatenated log).

     **Non-Python-driver ordering (binary/bulk-asset channel, issue #1017)**: the file-write contract above assumes the raw compiler bytes land in `compile-log.txt` — not a re-typed summary. A manual/agent session with no orchestrating Python driver cannot pipe subprocess stdout/stderr straight into the open `staged_sidecar` context, and re-typing the log with its own editing tool degrades the contract to a summary the agent composed, not the compiler's real output (and a consumer hook may separately block the Bash redirection this would otherwise use). Route the real bytes through the same code-enforced copy primitive the `stage`/`commit` shim above uses:

     1. Redirect each `pdflatex`/`bibtex` pass's combined stdout+stderr to a scratch path OUTSIDE the checkout (e.g. `/tmp/anvil-compile-<thread>-pass<N>.log`) as the passes run — concatenate passes into one scratch file if the harness allows sequential appends there.
     2. Land the real bytes inside the open staging dir with `uv run --project .anvil python -m anvil.lib.sidecar copy /tmp/anvil-compile-<thread>.log <staging-dir>/compile-log.txt` (bare `python -m anvil.lib.sidecar copy ...` in the anvil source repo) — staged then atomically renamed into place, with post-copy byte-identity verification by default (refuses rather than landing an unverified copy).

     This is the same primitive `commands/paper-revise.md` step 8 uses for figure carry-forward — one `copy` subcommand covers both "move existing bytes into a staging dir" cases. When an orchestrating Python driver IS present, redirect the subprocess output straight into the staging dir (or call `anvil.lib.sidecar.copy_bytes()` if the compiler was invoked with output captured elsewhere first) — the CLI shim exists for the driverless case only.
   - Inspect the resulting `main.pdf` (or compile log) for unresolved citations (`[??]`) and unresolved cross-references (`Section ??`, `Figure ??`).
   - If the toolchain is not available in the environment, write a `compile-log.txt` entry: `SKIPPED — pdflatex not available in environment` and set a NON-critical note (rather than a critical flag) in `flags.md`. The acceptance test environment IS expected to have the toolchain.
   - A non-zero exit from any pdflatex/bibtex invocation, OR any `[??]` in the final PDF, sets a **critical flag** in `flags.md`.
   - **Non-convergence at the cap** (new critical-flag case): if the 5-pass cap is reached while the most recent pass's log **still** contains the `Label(s) may have changed. Rerun to get cross-references right.` warning, the paper did NOT converge — set a **critical flag** in `flags.md`: `compile did not converge after 5 passes — possible reference cycle; inspect compile-log.txt for the oscillating label.` The auditor MUST NOT report the paper as compiled-clean in this case.
5. **Citation audit** (`citation-audit.md`):
   - Enumerate every `\cite{key}`, `\citep{key}`, `\citet{key}` (and any other natbib cite commands) in `main.tex` **and every `\input`/`\include` child** (issue #643 — a multi-file paper cites from its section files; resolve the tree via `anvil/lib/tex_includes.py::resolve_tex_inputs(<thread>.{N}/main.tex)` so cite keys in `sections/*.tex` are enumerated too, not just the master's).
   - For each `key`, verify it has a matching `@type{key, ...}` in `refs.bib`. List unresolved keys in `citation-audit.md` and add a critical flag for each.
   - For each resolved citation, attempt **claim-support spot-check**:
     - Extract the surrounding sentence(s) — the claim the citation backs.
     - If the cited paper has source material in `<thread>/refs/` (a PDF or notes file whose name or content references the BibTeX key), read it and assess: does the cited paper support the surrounding claim? Record a verdict per citation: `supports`, `does-not-support`, `partial`, `unverified — source not on disk`.
     - For `does-not-support`, set a critical flag (citation error).
     - For `unverified`, record but do NOT flag (this is a known limitation of LLM-based audit; the human author is responsible for off-disk verification).
   - Format `citation-audit.md` as a markdown table: `| Key | Resolved | Surrounding claim | Verdict | Notes |`.
5b. **Corpus-provenance audit (conditional — issue #612)**: invoke `anvil/lib/project_brief.py::resolve_corpus_dirs(<project_dir>)` (the project root whose `BRIEF.md` frontmatter declares the top-level `corpus:` key — the same project-layout resolution `paper-review`'s `web_search` knob and `paper-draft` step 3b read) per `anvil/lib/snippets/provenance.md` §Section 1. This is the **exhaustive** five-way verification the reviewer (`paper-review` step 4d) only samples — it verifies every `provenance.md` row against the on-disk corpus. It is **orthogonal to** the `<thread>/refs/` per-thread claim-support spot-check in step 5: `refs/` holds per-thread author-supplied PDFs; `corpus:` is a project-level read-only evidence base (see the snippet's §"Relationship to `<thread>/refs/` and `cite.py`").
   - **When inactive** (no `corpus:` key, `corpus: null`, or `corpus: []`): **byte-identical to pre-#612 paper-audit behavior** — no `.corpus-audit/` sidecar is written, the `.audit/` sidecar (steps 3–9) is unchanged, no new output. Skip the rest of this step entirely.
   - **When active** (≥1 resolved dir), open a **SEPARATE** staged sidecar for the corpus-audit dir — nested INSIDE the still-open `.audit/` sidecar from step 3, each with its own independent staging dir (the framework supports concurrent nested `staged_sidecar` contexts). Invoke `anvil/lib/sidecar.py::staged_sidecar(final_dir=<thread>.{N}.corpus-audit, required_files=["_review.json", "_meta.json", "_progress.json", "corpus-audit.md"])`. Every file write below lands **inside this second staging directory** (`.<thread>.{N}.corpus-audit.tmp/`), NOT inside the `.audit/` staging dir and NOT inside the final `<thread>.{N}.corpus-audit/` path. The `.corpus-audit/` sibling **coexists** with `.audit/` — it is the substance-verification specialist, not a replacement (per `anvil/lib/snippets/provenance.md` §Section 8 sibling-dir naming). Sweep any stale staging via `cleanup_one_staging(<thread>.{N}.corpus-audit)` first, mirroring step 1.
     - **Initialize `_meta.json`** with `scorecard_kind: "tool_evidence"`, `critic: "paper-corpus-audit"`, and the standard `started` / `finished` / `model` / `schema_version` fields (see `anvil/lib/snippets/scorecard_kind.md`).
     - **Inventory** every attributed quote and checkable factual claim (named dates, names, events, places, measured values) in `main.tex` **and its `\input`/`\include` children** (issue #643 — the paper body lives in the section files for a multi-file thread; resolve via `anvil/lib/tex_includes.py::resolve_tex_inputs`), and every row in `<thread>.{N}/provenance.md`. **A claim in the artifact with no `provenance.md` row is a finding in itself** (an unmapped claim) per `anvil/lib/snippets/provenance.md` §Section 4. A missing `provenance.md` when the tier is active is itself a finding (broken contract, not a crash).
     - **Anchor-resolution pre-pass (§Section 4a, issue #868)**: before classifying, run `python -m anvil.lib.provenance_anchor check <thread>.{N}/provenance.md <corpus_root> [...]` (one invocation over the whole table; prefix `uv run --project .anvil` in an installed consumer repo) — it searches each `Anchor`-bearing row's cited file in FULL, not just the hinted `Line range`, and reports `NO_ANCHOR` / `FILE_NOT_FOUND` / `NOT_FOUND` / `RESOLVED` / `DRIFTED` per row. A `DRIFTED` row emits a distinct `corpus-audit.md`/`_review.json` finding worded as **anchor drift** ("Line range hint stale; quoted text still present at line `<X>`") — NOT `MISMATCH`/`NOT_FOUND`, and NOT a `critical_flags` entry. A `NO_ANCHOR` row (legacy) skips straight to classifying against the cited `Line range`, exactly as before #868.
     - For **each** `provenance.md` row, open the resolved passage — the anchor's ACTUAL location when the pre-pass found drift, otherwise the cited `Line range` — in the resolved corpus and **classify** it with the five-way vocabulary (`anvil/lib/snippets/provenance.md` §Section 5): `VERIFIED` (exact/near-exact match), `PARAPHRASE_OK` (substance present, authorial wording), `MISMATCH` (passage exists but does not support the claim as written), `NOT_FOUND` (no matching passage in the range or surrounding context), `FABRICATED` (the claim conflicts with, or is contradicted by, the corpus). `VERIFIED` and `PARAPHRASE_OK` are passing; `MISMATCH` and `NOT_FOUND` are findings; `FABRICATED` is a finding **and** a critical flag. A drifted row's content classification is independent of the drift finding — once relocated, it is scored on its own merits.
     - Write `_review.json` with **`kind: tool_evidence`** (the `Kind.TOOL_EVIDENCE` shape already in `anvil/lib/review_schema.py`; the schema validator already enforces `tool_calls` on every `tool_evidence` finding — no schema change). Every `MISMATCH` / `NOT_FOUND` / `FABRICATED` row, and every `DRIFTED` anchor finding, emits a finding with a **non-empty `tool_calls`** array recording the file-read/tool operation that produced the evidence (the passage read, the lines inspected, or the `provenance_anchor.py check` invocation). `findings == []` is valid — a corpus whose every claim is VERIFIED / PARAPHRASE_OK with zero drift is a clean audit.
     - **Fabrication-class critical flags**: each `FABRICATED` entry (and any inventory finding that is unambiguously invented) additionally emits a `critical_flags` entry using the five `CriticalFlag.type` strings from `anvil/lib/snippets/provenance.md` §Section 6: `fabricated_quote`, `fabricated_fact`, `misattribution_of_substance`, `anachronism`, `unattributed_paraphrase`. Each flag's `justification` quotes the offending `main.tex` text and the corpus evidence (or its explicit absence). These land in `<thread>.{N}.corpus-audit/_review.json.critical_flags` and route through the existing verdict machinery — `anvil/lib/critics.py::_compute_verdict_impl` short-circuits any `critical_flags` → `Verdict.BLOCK` (discovered by the normal `discover_critics` → `aggregate` → `compute_verdict` path; no lib change).
     - Write **`corpus-audit.md`** — the human-readable classification table, one row per claim: `| Claim | Source file | Line range | Classification | Notes |` (plus a distinct anchor-drift row per drifted claim, per §Section 4a).
     - **Update `_progress.json`** (LAST write in this sidecar) with `phases.audit.state = done`, `for_version = N`, and `metadata.provenance_summary` — the six-counter roll-up per `anvil/lib/snippets/provenance.md` §Section 7: `{total_claims, verified, paraphrase_ok, mismatch, not_found, fabricated}` (the six counts sum to `total_claims`), plus `anchor_drift_count` (issue #868, a separate bookkeeping count — drift is orthogonal to content classification). Then **exit this nested `staged_sidecar` context**: the primitive verifies the four-file manifest and atomically renames `.<thread>.{N}.corpus-audit.tmp/` → `<thread>.{N}.corpus-audit/`.
   - **Declared-but-missing dirs**: proceed with whatever resolved (`resolve_corpus_dirs` returns `missing: true` entries, never raises); surface the broken declaration as a finding in `_review.json`.
6. **Numerical audit** (`numerical-audit.md`):
   - Enumerate numerical values in the abstract, results section, conclusion, and any explicit comparisons (e.g., "5x speedup", "87.3% accuracy").
   - For each, find the corresponding figure or table (typically referenced by `\ref{tab:results}`, `\ref{fig:scaling}`) and verify the text matches.
   - Record discrepancies in `numerical-audit.md` as a table: `| Text claim | Source (Tab/Fig) | Source value | Match | Notes |`.
   - For each mismatch, set a critical flag in `flags.md` (numerical inconsistency).
6b. **Pending-marker terminal gate (deterministic, unconditional) — issue #842**: invoke `uv run --project .anvil python -m anvil.lib.pending_marker <thread>.{N}/ --write-review` (same tool and same invocation shape as `paper-review` step 4g; auto-detects `main.tex`, `--body <path>` override for adopted-in-place legacy threads). This re-runs the deterministic `[PENDING <source>]` marker gate as the **terminal check** before `AUDITED` — genuinely useful independent of step 4g when the auditor runs on a draft that has not yet been reviewed (see this file's Inputs section: "acceptable ... to run the auditor earlier"), and as defense-in-depth when it has. `--write-review` writes (overwrites, per the deterministic-regeneration carve-out documented in the module) `<thread>.{N}.pending/_review.json`, carrying the specially-resolved `pending_dependency` flag whenever any active marker remains. **The terminal gate is the tool's exit code / `pass` field, NOT a `Verdict.BLOCK`**: the `pending_dependency` flag is visible-but-non-blocking (`convergence.blocking_critical_flags` filters it out; `convergence.has_pending_dependency_flag(aggregate.critical_flags)` is the query), so it does not tank the audit verdict the way a numerical-inconsistency flag does — instead, **while the pending gate has not passed (exit 1 / `pass: false`), the thread does NOT advance to `AUDITED`**, exactly as `paper-review` step 7 holds READY. A well-formed marker is an honest disclosure, not a defect (see `rubric.md`) — do NOT add a corresponding entry to `numerical-audit.md`'s mismatch table, and do NOT fabricate a value to clear it; note any outstanding marker in `flags.md`'s **outstanding-dependencies** list instead (see the example below), naming the source label(s) from the tool's `outstanding_sources` output. **Clean result** (no active markers in the body): sidecar still writes with empty findings/flags, byte-identical in effect to a pre-#842 audit. **Tooling-absent fail-open**: mirrors step 4 toolchain-absent handling — when `uv`/the module is unavailable, emit a stdout notice and manually scan for the literal `[PENDING <source>]` / `[PENDING: <source>]` shape (a source-less `[PENDING]` is malformed, not a marker), hold `AUDITED` on any found marker exactly as the tool would (without fabricating), and record the fallback with a one-line note.
7. **Figure source-of-truth check** (informational — does not flag unless explicitly stale):
   - For each `\includegraphics{figures/<name>.pdf}` reference, check whether `figures/src/<name>.py` (or analogous source) exists.
   - If a source script exists and its mtime is newer than the rendered figure, note in `numerical-audit.md` as "figure may be stale — script newer than render". This is informational; the reviser or figurer is responsible for re-rendering. Set a non-critical note in `flags.md` if any stale figures are detected.
8. **Write `flags.md`**: a markdown list of critical flags, each with one-paragraph justification and the specific evidence (line numbers, table references, log excerpts) needed for the reviser to act.

   ```markdown
   # Audit flags for <thread>.{N}

   ## Critical flags (block advancement to AUDITED)

   - **Unresolved citation** (`\cite{smith2024}`): no matching entry in refs.bib. Surrounding claim: "...".
   - **Claim-support failure** (`\cite{jones2023}`): paper does not support the surrounding claim. Evidence: <excerpt from refs/jones2023.pdf or notes>.
   - **Numerical inconsistency** (Sec. 5 vs Table 2): text says 87.3%, table says 87.1%.
   - **Build failure**: bibtex main exited non-zero. See compile-log.txt lines 142–158.

   ## Outstanding dependencies (hold AUDITED; not scored defects — issue #842)

   - **Pending marker** (`[PENDING benchmark-run-2024-11]`, Sec. 5): a well-formed pending marker remains in the body — an honest disclosure, **not a defect and NOT a blocking critical flag** (it carries the specially-resolved `pending_dependency` type: visible here but never forcing `Verdict.BLOCK`, never lowering a dimension score). It holds the `AUDITED` terminal transition (step 6b) until the value genuinely resolves and the marker is replaced — never fabricate a value to clear it. See `<thread>.{N}.pending/_review.json`. Omit this section entirely when no active markers remain.

   ## Non-critical notes

   - **Stale figure**: figures/scaling.pdf is older than figures/src/scaling.py — re-render recommended.
   - **Unverified citations** (4): claim-support could not be verified because source PDFs are not in <thread>/refs/. Author should verify off-disk.
   ```
9. **Update `_progress.json`** inside the staging dir: `phases.audit.state = done`, `phases.audit.completed = <ISO>`. Record summary counts in metadata: `metadata.audit_summary = { critical_flags: <N>, unverified_citations: <M>, ... }`. This is the LAST file write before the context manager exits — the manifest verification + atomic rename at exit (issue #350) requires `_progress.json` to be present. Then **exit the `staged_sidecar` context block**: the primitive verifies every name in the required-files manifest exists in the staging dir, then atomically renames `.<thread>.{N}.audit.tmp/` → `<thread>.{N}.audit/`. The final-named dir only ever exists in **complete** form.
10. **Report**: print the path to the (now-renamed) audit dir and a one-line status (e.g., `Audited q3-method.2 → q3-method.2.audit/ (0 critical flags, 3 unverified citations, build OK)`).

## State machine impact

- If `flags.md` records **zero critical flags** AND **no outstanding pending dependency** (step 6b's gate passed) AND the paper was already `READY`, the thread is now `AUDITED` (terminal).
- If `flags.md` records any **critical flag**, the thread remains `READY-WITH-AUDIT-FLAGS` (not terminal). The orchestrator recommends `paper-revise`, which consumes the audit sibling alongside the review sibling to produce the next version.
- If `flags.md` records **zero critical flags** but step 6b's pending gate did NOT pass (an active `[PENDING <source>]` marker remains), the thread does NOT reach `AUDITED` — it is held pending the outstanding dependency (issue #842). This is not a defect to revise away; the value must genuinely resolve (the drafter replaces the marker with the real number) before the terminal transition. Never fabricate the value to force `AUDITED`.
- A version that reaches `AUDITED` is the deliverable. There is no `READY` → `AUDITED` re-review loop unless the reviser produces a new version.

## Idempotence and resumability

- A completed audit (`audit.state == done` AND `flags.md` exists) is never re-run automatically. A new `<thread>.{N+1}.audit/` is created only after a new version dir exists.
- A crashed audit is re-runnable after deleting partial output.

## Notes for the auditor agent

- **Do not fabricate verifications.** If a cited paper's source material is not in `<thread>/refs/`, mark the citation `unverified` and move on. A `supports` verdict that is actually a hallucination is worse than an honest `unverified`.
- **Build failures are critical.** A paper that does not compile is not a paper. Even a single unresolved `??` citation in the rendered PDF is a critical flag — the reader will see it.
- **Numerical audit is mechanical.** When the abstract claims 87.3% and Table 2 shows 87.1%, flag it. Do not try to figure out which is "really" right — the reviser will fix the inconsistency. Both `87.3` and `87.1` cannot be the same number.
- **Stale figures are advisory, not critical.** A rendered figure older than its source script may or may not be stale (the script may not have changed in a meaningful way). Surface as a non-critical note for the reviser to investigate; do not block.

## `_progress.json` snippet (audit sibling)

```json
{
  "version": 1,
  "thread": "<slug>",
  "for_version": <N>,
  "phases": {
    "audit": { "state": "done", "started": "<ISO>", "completed": "<ISO>" }
  },
  "metadata": {
    "audit_summary": {
      "critical_flags": 0,
      "unresolved_citations": 0,
      "claim_support_failures": 0,
      "numerical_inconsistencies": 0,
      "unverified_citations": 3,
      "stale_figures": 1,
      "build_status": "ok"
    }
  }
}
```

## Git sync (opt-in, off by default)

Per `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md` in an installed consumer repo): if `.anvil/config.json` exists and `git.commit_per_phase` is `true`, end this phase: stage only the dirs this phase wrote, commit as `anvil(<skill>/<phase>): <thread>.{N} [<state>]`, push if `git.push` is `true`. Git failures warn and continue — never fail the phase. When the config or knob is absent, skip this step entirely (default off).

This phase's specifics:

- **Ordering**: after the staged-sidecar atomic rename (issue #350) lands the final-named `<thread>.{N}.audit/` — so only complete sidecars are ever committed.
- **Staging target**: this command's own `<thread>.{N}.audit/` sidecar (never sibling critics' dirs — the narrow scope keeps the hook safe under parallel critic fan-out) AND the compiled `<thread>.{N}/main.pdf` this phase's step 4 produced in the version dir. `paper-audit` is the only paper command that writes into BOTH a critic sidecar and the version dir in the same run (its mandatory compile-verification step builds `main.pdf` into `<thread>.{N}/`) — stage **both** explicitly by path (`<thread>.{N}.audit/` and `<thread>.{N}/main.pdf`), never `<thread>.{N}/` wholesale (that could sweep in unrelated out-of-band edits to `figures/` or `main.tex` the audit did not make). Leaving `main.pdf` unstaged would leave the tree dirty after every audit on a `main.tex` thread, defeating the hook's clean-tree purpose (`git_sync.md` §"Why this exists").
- **Commit**: `anvil(paper/audit): <thread>.{N} [<state>]` (the bracket carries the thread's derived state per SKILL.md §State machine after the audit lands — `AUDITED` when the audit passes alongside a `READY` version).
