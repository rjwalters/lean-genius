---
name: paper-figures
description: Figurer command for the paper skill. Generates TikZ/PGFPlots diagrams, matplotlib data plots, and table assets for the latest paper version. Idempotent on resume. Never invents data.
---

# paper-figures — Figurer

**Role**: figurer.
**Reads**: latest `<thread>.{N}/main.tex` and `<thread>.{N}/figures/src/` (any author-supplied or revision-supplied source scripts).
**Writes**: rendered figures into `<thread>.{N}/figures/`. Idempotent.

## Inputs

- **Thread slug** (positional argument).
- **Latest version directory**: highest `N` with `<thread>.{N}/main.tex` existing.
- **Figure specifications**: extracted from `main.tex` by scanning for `\includegraphics{figures/<name>}` and `\input{figures/<name>.tex}` references.
- **Source scripts**: `<thread>.{N}/figures/src/*.py` (matplotlib) or `<thread>.{N}/figures/src/*.tex` (TikZ standalone) or `<thread>.{N}/figures/src/*.sh` (shell wrapper for an external tool).

## Outputs

```
<thread>.{N}/figures/
  fig-scaling.pdf          Rendered matplotlib plot (from src/fig-scaling.py)
  fig-scaling.csv          (if applicable) Source data for the plot, alongside the script
  diagram-arch.tex         TikZ source for architecture diagram (included via \input{...})
  example-screenshot.png   Author-supplied raster asset (figurer leaves untouched)
  src/                     Source scripts and data (preserved across revisions)
    fig-scaling.py
    fig-scaling.csv
```

The version dir's `_progress.json` is updated with `phases.figures.state = done`.

## Procedure

1. **Discover state**: find the highest `N` with `<thread>.{N}/main.tex`. Read `<thread>.{N}/_progress.json` to see if `phases.figures.state == done`.
2. **Resume check**: enumerate `\includegraphics{figures/<name>}` and `\input{figures/<name>.tex}` references in `main.tex`. For each referenced figure, check if the file exists in `figures/`. If all referenced figures exist AND `phases.figures.state == done` AND no source script is newer than its rendered output, exit early — no work needed.
3. **Initialize `_progress.json`**: write `phases.figures.state = in_progress`, `phases.figures.started = <ISO>`.
4. **For each missing or stale figure**:
   - **TikZ / PGFPlots** (`figures/<name>.tex`): if a source `.tex` file exists in `figures/src/<name>.tex` or directly in `figures/<name>.tex`, no rendering step is needed — TikZ is compiled inline by `pdflatex` via `\input{figures/<name>.tex}`. The figurer's job for TikZ is to verify the file exists and is syntactically valid (`pdflatex --output-directory=/tmp` on a tiny wrapper document is the standard way; if not available, skip the syntax check and surface in `notes` field).
   - **Matplotlib data plots** (`figures/<name>.pdf` from `figures/src/<name>.py`):
     - The source script MUST produce a `.pdf` (or `.svg`) output file at the path `figures/<name>.pdf` (or `.svg`).
     - The source script SHOULD load its data from `figures/src/<name>.csv` or another co-located data file. If no data file exists and the script does not embed its data, the figurer **refuses** and surfaces a request in the report: the reviser must add a `.csv` source. Do not invent data.
     - Execute the script: `python3 figures/src/<name>.py` from `<thread>.{N}/` as the working directory (so the script can write to `figures/<name>.pdf` with a relative path).
     - If execution fails (missing dependency, runtime error), write a stub `figures/<name>.pdf.MISSING` text file with the error and continue with other figures. Set `phases.figures.state = failed` at the end if any required figure could not be produced.
   - **External raster assets** (`.png`, `.svg`, `.jpg` dropped into `figures/`): the figurer leaves these untouched. They are author-supplied artifacts.
5. **Tooling**: the figurer SHOULD prefer self-contained tools (`python3` + `matplotlib`, native TikZ) over network-dependent services. Failing renders should produce a stub `<name>.MISSING` text file with the diagnostic, rather than silently leaving a broken `\includegraphics` reference.
6. **Update `_progress.json`**: `phases.figures.state = done` (or `failed` if any required figure could not be produced), `phases.figures.completed = <ISO>`.
7. **Report**: print a one-line status (e.g., `Rendered 4 figures for q3-method.2/ (2 matplotlib, 1 TikZ, 1 external asset, 0 missing)`). If any are missing, list them.

## Idempotence and resumability

- Re-running `paper-figures <thread>` on a thread where all referenced figures exist AND no source script is newer than its render is a no-op.
- Re-running on a thread where some figures are missing fills the gaps without touching existing figures.
- Re-running when a source script's mtime is newer than its render re-runs THAT figure only.
- The figurer never deletes figures. Stale figures from prior versions of the paper (no longer referenced in `main.tex`) are left in place; cleanup is out of scope.

## Validation by file existence

The auditor (`paper-audit`) verifies that every `\includegraphics{figures/<name>}` and `\input{figures/<name>.tex}` in `main.tex` resolves to a file on disk. The figurer's job is to make that check pass. Validation rule: for every figure reference in `main.tex`, the corresponding file must exist in `figures/` (or `figures/<name>.tex` for TikZ). The figurer enumerates and fills this list.

## Figure source-of-truth policy

This skill's policy: **both** the source script and the rendered output are tracked artifacts.

- Source scripts and data go in `figures/src/<name>.{py,csv,sh,tex}`.
- Rendered outputs go in `figures/<name>.{pdf,svg,png}` (or directly in `figures/<name>.tex` for TikZ, since TikZ has no separate render step).
- The auditor can re-run scripts in `figures/src/` to verify rendered outputs are current. The auditor flags stale figures as non-critical notes.
- The reviser preserves `figures/src/` across revisions verbatim unless the revision deletes the corresponding figure.

## Notes for the figurer agent

- **Never invent data.** If a chart is requested without source data, refuse and surface the gap to the reviser. A figurer that fabricates data poisons the paper's evidence and reproducibility dimensions — both heavy in the rubric.
- **Prefer TikZ / PGFPlots for diagrams and small plots.** Vector-native in the PDF, no rasterization artifacts, no external dependency. Reserve matplotlib for genuine data plots from real datasets.
- **Keep `.csv` source files alongside rendered charts.** This makes regeneration (after a reviser updates the numbers) trivial and supports the auditor's stale-figure check.
- **A failed render is loud, not silent.** A `.MISSING` stub file is better than a broken `\includegraphics` reference that surfaces only at compile time. The auditor will pick up the failure and flag it.

## `_progress.json` snippet

This command updates `phases.figures` only, per the shallow merge rule documented in `anvil/lib/snippets/progress.md`:

```json
{
  "phases": {
    "figures": { "state": "done", "started": "<ISO>", "completed": "<ISO>" }
  }
}
```

Merge rule (shallow): preserve all other phases and all `metadata` fields. The figurer only touches `phases.figures`. Use ISO-8601 UTC timestamps per `anvil/lib/snippets/timestamp.md`.

## Git sync (opt-in, off by default)

Per `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md` in an installed consumer repo): if `.anvil/config.json` exists and `git.commit_per_phase` is `true`, end this phase: stage only the dirs this phase wrote, commit as `anvil(<skill>/<phase>): <thread>.{N} [<state>]`, push if `git.push` is `true`. Git failures warn and continue — never fail the phase. When the config or knob is absent, skip this step entirely (default off).

This phase's specifics:

- **Ordering**: after `_progress.json` records `phases.figures.state = done`.
- **Staging target**: ONLY the `<thread>.{N}/` version dir this phase wrote into.
- **Commit**: `anvil(paper/figures): <thread>.{N} [<state>]` (the bracket carries the thread's current derived state per SKILL.md §State machine — the figures phase does not advance the state machine).
