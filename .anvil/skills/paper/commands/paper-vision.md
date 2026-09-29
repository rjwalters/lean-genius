---
name: paper-vision
description: Vision-model critic for the paper skill. Renders the paper source to PDF and per-page PNGs, then uses a vision-language model to score rendered-only defects (figure legibility, table overflow, palette adherence, mathtext artifacts) that the prose/citation critics never see.
---

# paper-vision — Vision-language-model critic

**Role**: rendered-artifact critic.
**Reads**: `<thread>.{N}/main.tex` (LaTeX, default) or `<thread>.{N}/main.md` (Markdown source); renders to `paper.pdf` + per-page PNGs on demand.
**Writes**: `<thread>.{N}.vision/` with `_review.json` (canonical schema, `kind=vision`), `_meta.json`, `_progress.json`, and per-page PNGs in `pages/`.

This critic exists because Anvil's source-side critics never *look at* the compiled paper. The `paper-review` reviewer scores the rubric off `main.tex`; the `paper-audit` auditor verifies citations and numerical consistency against the source. Neither sees the rendered PDF: whether the scaling-law plot's axis labels are legible at print size, whether the wide results table runs off the right margin, whether a `$11B` token got eaten by a MathJax/mathtext span. For a paper this gap is sharper than for a deck — **LaTeX is the source-of-truth, so a rendered equation that does not match the author's intent is a correctness defect, not a polish one.** This critic closes that gap by scoring the rendered pages directly.

This critic is a sibling of `paper-review` and `paper-audit` in the "N parallel critics, one reviser" pattern. It does not gate the state machine on its own; its `_review.json` is aggregated by `paper-revise` alongside the other critic siblings via `anvil/lib/critics.py`.

## Owned vision dimensions (subset of the shipped six, /20 total)

This critic owns a **vision rubric subset** alongside the paper's main 9-dimension /44 rubric (`rubric.md`). The vision dims appear in the aggregated scorecard via the existing mean-of-non-null aggregator (`anvil/lib/critics.py::aggregate`); no schema or aggregation changes are required.

The paper vision rubric is a **four-dimension subset** of the framework's shipped `DEFAULT_VISION_DIMENSIONS` (the six in `anvil/lib/vision.py`), composed by passing the relevant dims to `VisionRubric(dimensions=[...])`. The dropped two (`vertical_overflow`, `slide_density`) are slide-centric and do not apply to a paginated, reflowing paper. The four paper-owned dims, scored 0–5 each (/20 total):

| Dim | Name | What it catches (paper-tuned) |
|---|---|---|
| v1 | `label_cropping` | **Figure legibility**: chart axis labels, legends, annotations, and **caption text** truncated by the figure box or page margin. A `\caption{}` that runs under the figure and gets clipped, or a legend cut off at the figure's right edge, is the load-bearing case for a paper. |
| v2 | `axis_legibility` | **Figure legibility (font scale)**: axis labels and tick marks too small to read at print size. A scaling-law plot whose x-axis is illegible at 100% on the rendered PDF fails the figure-quality bar (rubric dim 6). |
| v3 | `palette_adherence` | **Palette adherence for plots**: data plots use a consistent, print-safe palette rather than raw matplotlib defaults. For papers this also catches color-only encodings that fail in grayscale print (a reproducibility / accessibility concern). |
| v4 | `mathtext_artifacts` | **Mathtext artifacts (most critical for paper)**: rendered equations that do not match the LaTeX source intent — `$X` rendered as italic math where literal text was meant, a broken `\(\)`/`$$` span, an overfull display equation running off the right margin, garbled subscripts/superscripts. Because LaTeX is the source-of-truth, a rendered-equation mismatch is a *correctness* defect. |

**Table overflow** — wide tables (`tabular`/`longtable`) whose right-most columns cross the page's right margin or are clipped — is caught under `label_cropping` (the table's clipped content is "cropping" at the page boundary). A table-overflow finding cites the table by its `\label{}` or caption and is paired with the `rendered_overflow_unrecoverable` critical flag when the clipped cells carry load-bearing numbers (e.g. the best-result column dropping off the page).

The four vision dims are scored 0–5 each. The vision critic puts `null` on the paper's 8 main-rubric dimensions (it does not own them); other critics put `null` on v1–v4. The aggregator merges the two scorecards cleanly per the existing rules.

**Default rubric for this critic**: the four dims above, passed explicitly to `VisionRubric(dimensions=[...], rubric_id="anvil-pub-vision-v1")`. The framework default `default_vision_rubric()` ships all six; the paper critic narrows it.

## Critical flags (two shipped categories)

The two framework critical-flag types (from `anvil/lib/vision.py`) short-circuit the aggregated verdict to `BLOCK`:

- **`rendered_overflow_unrecoverable`** — content cut off in a way that loses load-bearing information. For a paper this is most commonly a **wide table whose right columns are clipped at the page margin** (e.g. the best-method column or a confidence-interval column dropping off the page), or a figure caption truncated such that the figure's takeaway is lost. Raised when the VLM identifies that specific named/numeric content was lost in the clipped region.
- **`mathtext_artifact_breaks_meaning`** — a rendered equation that diverges from the LaTeX source intent in a way that changes meaning: a `$X` rendered as italic `X` where the dollar sign or literal text carried semantic weight, a broken math span, or a display equation whose right-hand side is clipped by an overfull `hbox`. **For a paper this is the highest-stakes vision flag** — the whole premise of a LaTeX paper is that the rendered math is the claim.

Other vision findings surface as `Finding` items with severity `major` / `minor` / `nit`.

## Inputs

- **Thread slug** (positional argument).
- **Latest version directory**: highest `N` with `<thread>.{N}/main.tex` (or `main.md`).
- **Rendered PDF**: `<thread>.{N}/paper.pdf`.
  - If `main.tex` is the source, the PDF is produced by the convergence-loop compile that `paper-audit` already runs (`pdflatex`/`bibtex` rerun to the "Label(s) may have changed. Rerun" fixpoint, capped at 5 `pdflatex` passes — see `paper-audit.md` step 4); the vision critic reuses that `paper.pdf` when present and current.
  - If the source is Markdown (`main.md`), or no `pdflatex`-built PDF exists, the critic renders via `anvil.lib.render.render_pandoc_to_pdf(source_md, out_pdf)`.
- **Per-page PNGs**: produced by `anvil.lib.render.render_pdf_to_pngs(pdf, out_dir, dpi=200)` from the PDF. Paper uses **200 DPI** by default (vs the deck's 150) — fine-grained axis-label and small-caption legibility evaluation needs the extra resolution at print scale.
- **VLM**: Anthropic SDK by default; consumers without an API key inject a callback per `anvil/lib/vision.py`.

## Outputs

```
<thread>.{N}.vision/
  pages/
    page-1.png, page-2.png, ...    Per-page PNGs at 200 DPI (configurable)
  _review.json                     Canonical schema, kind=vision, rendered_artifact=paper.pdf
  _meta.json                       { critic, role, started, finished, model, scorecard_kind }
  _progress.json                   { version, thread, phases.vision.{state,started,completed} }
```

**Atomicity** (issue #350, #376): the vision sibling dir is written **atomically** via the staged-sidecar primitive at `anvil/lib/sidecar.py`. The three top-level files (`_review.json`, `_meta.json`, `_progress.json`) are staged under a leading-dot sibling `.<thread>.{N}.vision.tmp/` during writing; on clean completion the staging dir is renamed (one atomic `Path.rename`) to the final `<thread>.{N}.vision/` name. A mid-cycle interrupt leaves a `.<thread>.{N}.vision.tmp/` dir on disk that the next invocation's `cleanup_one_staging(<thread>.{N}.vision)` per-critic sweep removes; the final-named dir never exists in partial form. Discovery (`anvil/lib/critics.py::discover_critics`) is unchanged — the leading-dot staging shape is invisible to the discovery glob. The `pages/` subdirectory is staged inside the staging dir but is NOT validated by the required-files manifest (per `staged_sidecar`'s flat-manifest contract — subdirectories like `pages/` are not validated).

> **`pages/` is a regenerable render intermediate — safe to gitignore (issue #738).** The per-page PNGs are pure output of `render_pdf_to_pngs(pdf, out_dir, dpi=200)` from a regenerable PDF; they are NOT part of the canonical committed critic output (that is the three top-level JSONs — the reviser only needs `_review.json`). `scripts/install-anvil.sh` seeds a root-`.gitignore` rule (`**/*.vision/pages/`) so a `git add <thread>.{N}.vision/` never commits them. If you already committed them, `git rm -r --cached <thread>.{N}.vision/pages` untracks them (gitignore does not un-track already-tracked paths).

## Procedure

1. **Discover state** + **resume check** (per `anvil/lib/snippets/progress.md`). Then **sweep a stale staging dir from a prior interrupt of THIS critic on THIS version** by invoking `anvil/lib/sidecar.py::cleanup_one_staging(<thread>.{N}.vision)` (the per-critic, parallel-safe sweep — issue #376). This removes ONLY a leftover `.<thread>.{N}.vision.tmp/` from a previously-killed run of this same critic on THIS version. Sibling critics' in-flight staging dirs under the same portfolio root are NOT touched (issue #350, #376). The sweep is idempotent. The "completed" check is satisfied when the final-named `<thread>.{N}.vision/` exists — the atomic-rename contract guarantees the dir only exists when complete.
2. **Open the staged sidecar** for the vision dir by invoking the context manager `anvil/lib/sidecar.py::staged_sidecar(final_dir=<thread>.{N}.vision, required_files=["_review.json", "_meta.json", "_progress.json"])`. Every file write below MUST land **inside the yielded staging directory** (the path of the shape `.<thread>.{N}.vision.tmp/`), NOT inside the final `<thread>.{N}.vision/` path. On clean context exit, the primitive verifies the manifest, then atomically renames the staging dir to its final name (issue #350). Then, **inside the staging dir**, initialize `_progress.json`:
   ```json
   {
     "version": 1,
     "thread": "<slug>",
     "for_version": <N>,
     "phases": { "vision": { "state": "in_progress", "started": "<ISO>" } }
   }
   ```
   and **`_meta.json`**:
   ```json
   {
     "critic": "vision",
     "role": "paper-vision.md",
     "started": "<ISO>",
     "finished": null,
     "model": "claude-opus-4-7-20251022",
     "schema_version": 1,
     "scorecard_kind": "machine-summary"
   }
   ```
   See `anvil/lib/snippets/progress.md` and `anvil/lib/snippets/scorecard_kind.md` for the canonical shapes.

   **Non-Python-driver ordering (fail-open, manual fallback)** — issue #645: `staged_sidecar` is a Python context manager. A manual/agent session with **no orchestrating Python driver** cannot hold its `with` block open across the file writes below (it writes files with its own editing tool between discrete steps), so it MUST use the equivalent CLI shim rather than writing straight into the final `<thread>.{N}.vision/` dir (which silently reopens the #350 partial-write defect this primitive exists to close). Two tiers, in preference order:

   1. **Primary — `python -m anvil.lib.sidecar` CLI shim** (the common case). In an installed consumer repo (anvil vendored under `.anvil/`, not on `sys.path`), prefix every invocation below with `uv run --project .anvil` (the `.anvil/pyproject.toml` + `uv sync --project .anvil` shipped by the installer since #230 make the module resolvable from the consumer root — the same shape the other `anvil.lib.*` critics already use); in the anvil source repo the bare `python -m anvil.lib.sidecar` form works as-is. This wraps the *exact same* `staged_sidecar` code, so the manifest check + single atomic `Path.rename` are enforced by code, not agent discipline:
      - `uv run --project .anvil python -m anvil.lib.sidecar stage <thread>.{N}.vision` → prints the staging path (`.<thread>.{N}.vision.tmp/`). (Refuses with a nonzero exit if `<thread>.{N}.vision/` already exists — matching `staged_sidecar`'s `FileExistsError` refuse-to-overwrite guard.)
      - Write **all** required files (`_review.json`, `_meta.json`, `_progress.json`) into that printed staging path — never into the final `<thread>.{N}.vision/` name.
      - `uv run --project .anvil python -m anvil.lib.sidecar commit <thread>.{N}.vision --required _review.json,_meta.json,_progress.json` → verifies the manifest, then atomically renames staging → final. **Nonzero exit (1) leaves the staging dir in place with no partial final dir** if any required file is missing — the `SidecarIncompleteError` analog; fix the gap and re-`commit`.
      - The stale-staging sweep of step 1 has an exact CLI analog: `uv run --project .anvil python -m anvil.lib.sidecar cleanup <thread>.{N}.vision` (the parallel-safe per-critic sweep, issue #376).
   2. **Last resort — manual `mv`-based staging** when even `python`/`uv` is unavailable. Reproduce the staging contract by hand: (a) at entry, sweep any leftover `rm -rf .<thread>.{N}.vision.tmp/` (the `cleanup_one_staging` analog); (b) `mkdir .<thread>.{N}.vision.tmp/` and write **every** required file into it — writing `_progress.json` **last**, so a mid-write interrupt is caught by the missing-manifest check rather than producing a final-named partial; (c) confirm the staging dir holds the full required set — use a count check (`[ "$(ls -1 .<staging-dir> | wc -l)" -eq <N> ]`) or an `ls`-based presence check rather than per-file `[ -f ]`, which can false-negative under a restricted-`stat` sandbox — **then** `mv .<thread>.{N}.vision.tmp <thread>.{N}.vision` as the **last** step (POSIX `mv` on a same-filesystem dir-to-dir rename is atomic, matching `Path.rename`). Do NOT create `<thread>.{N}.vision/` before all files are staged. **Record the fallback durably** so a reader can tell atomicity was reproduced by hand rather than tool-verified: stamp `_meta.json` with `"atomicity_fallback": "manual-mv"` (e.g. `sidecar: staged_sidecar CLI unavailable (uv/python not on PATH); atomicity reproduced via manual mv this pass`). Absent this note the manual staging is indistinguishable from an unsafe direct write.

   The two tiers land a byte-identical on-disk result to the `staged_sidecar` context-manager path; they exist only to give a Python-less session a code-enforced (tier 1) or contract-faithful (tier 2) route to the same atomicity guarantee. When an orchestrating Python driver IS present, use `staged_sidecar` directly as documented above — the CLI shim is not needed.

3. **Ensure `paper.pdf` exists**:
   - If `<thread>.{N}/paper.pdf` exists and is newer than the source (`main.tex` and any `figures/` it includes), use it.
   - Otherwise render it:
     - **LaTeX source**: run the convergence-loop compile (the same one `paper-audit` runs — `pdflatex`/`bibtex`, then rerun `pdflatex` to the "Label(s) may have changed. Rerun" fixpoint, capped at 5 `pdflatex` passes; see `paper-audit.md` step 4) and copy/rename the result to `paper.pdf`. A non-zero exit is surfaced as a finding (the prose/audit critics will also catch the build failure).
     - **Markdown source**: call `anvil.lib.render.render_pandoc_to_pdf(main_md, out_pdf)`.

4. **Render per-page PNGs**:
   - Call `anvil.lib.render.render_pdf_to_pngs(pdf, out_dir=<thread>.{N}.vision/pages/, dpi=200)`.
   - Returns a sorted list of PNG paths (`page-1.png`, `page-2.png`, ...).

5. **Run the vision critic** with the paper-specific four-dim rubric:
   ```python
   from anvil.lib.vision import (
       VisionCritic,
       VisionRubric,
       DEFAULT_VISION_DIMENSIONS,
   )

   # Narrow the shipped six to the four that apply to a paginated paper.
   _PUB_DIM_NAMES = {
       "label_cropping",
       "axis_legibility",
       "palette_adherence",
       "mathtext_artifacts",
   }
   pub_rubric = VisionRubric(
       dimensions=[d for d in DEFAULT_VISION_DIMENSIONS if d.name in _PUB_DIM_NAMES],
       rubric_id="anvil-pub-vision-v1",
   )

   critic = VisionCritic(critic_id="paper-vision")
   review = critic.critique(
       images=page_pngs,
       rubric=pub_rubric,
       version_dir="<thread>.<N>",
       rendered_artifact="paper.pdf",
       context=(
           "This is a rendered research paper. LaTeX/Markdown is the "
           "source-of-truth: rendered equations MUST match author intent. "
           "Watch for wide tables clipped at the right margin and figure "
           "captions / axis labels that are illegible or cropped at print "
           "size."
       ),
   )
   ```
   Consumers without an Anthropic API key (CI, offline development) construct the critic with a `callback=` instead — this is the path the `paper-vision` unit tests use.

6. **Write `_review.json`**:
   - The constructor in step 5 already validated the `Review`.
   - Serialize with `review.model_dump_json(indent=2)` to `<thread>.{N}.vision/_review.json`.

7. **Update `_progress.json`** and `_meta.json` inside the staging dir to `state: done` / `finished: <ISO>`. The `_progress.json` write MUST be the LAST file write before the context manager exits — the manifest verification + atomic rename at exit (issue #350) requires it to be present. Then **exit the `staged_sidecar` context block**: the primitive verifies every name in the required-files manifest exists in the staging dir, then atomically renames `.<thread>.{N}.vision.tmp/` → `<thread>.{N}.vision/`. The final-named dir only ever exists in **complete** form.

8. **Report**: one-line status, e.g. `Vision critic on q3-method.1 → q3-method.1.vision/ (vision total 14/20; 3 findings; 1 critical flag: rendered_overflow_unrecoverable on Table 2)`.

## Idempotence and resumability

- Standard: completed = no-op; crashed = re-runnable after deleting partial output.
- **Stale render**: if `<thread>.{N}/paper.pdf` is older than `<thread>.{N}/main.tex` (source updated since render), re-render and re-evaluate. The PDF is the source of truth for this critic.
- **Stale PNGs**: if PNGs in `pages/` are older than the PDF, re-render.

## Renderer dependencies

- **LaTeX toolchain** (LaTeX source path): a TeX distribution providing `pdflatex` + `bibtex` (TeX Live / MacTeX). This is already a `paper-audit` dependency.
- **pandoc** (Markdown source path): `brew install pandoc` (macOS) / `apt-get install pandoc` (Debian). Used by `anvil.lib.render.render_pandoc_to_pdf`.
- **pdftoppm** (poppler): `brew install poppler` (macOS) / `apt-get install poppler-utils` (Debian). The `anvil.lib.render` helper falls back to `pdf2image` if installed.

## VLM dependencies

- **Anthropic SDK** (default path): `pip install anthropic`. The default model is `claude-opus-4-7-20251022`; pass a different `model=` to override.
- **No SDK required** (callback path): consumers without an API key inject a `callback=` per `anvil/lib/vision.py`. This is the path the paper-vision unit tests use.

## Aggregation behavior

This critic's `_review.json` is discovered by `anvil.lib.critics.discover_critics` exactly like `paper-review` and `paper-audit`. The aggregator merges its scorecard into the composite verdict per the existing rules:

- The vision dims (v1–v4) appear in the aggregated scorecard alongside the paper's 8 main-rubric dims.
- Per-dim `critical=True` ORs across critics; non-empty `critical_flags` forces `Verdict.BLOCK`.
- The `paper-revise` command (with no code changes) consumes the vision findings via the same discover-glob → aggregate pattern documented in `paper-revise.md`.

The vision overlay is **additive evidence**, not a change to the /44 convergence gate: like the venue overlay, it contributes findings the reviser acts on. The generic 9-dimension `_review.json` from `paper-review` remains the sole driver of the `advance` decision; vision critical flags participate in the same critical-flag short-circuit the rubric already defines.

See `anvil/lib/README.md` § "Rendered-artifact review (`kind: vision`)" for the worked example.

## Notes for the paper-vision agent

- **Always evaluate the rendered PNGs, not the source.** The entire point of this critic is that figure legibility, table overflow, and equation rendering are invisible in `main.tex`.
- **Vision findings almost always require fixing `figures/src/*.py` (or the `tabular`/equation in `main.tex`), not the prose.** A mathtext or palette finding on a plot is a matplotlib-script fix; an axis-legibility or label-cropping finding is a `figsize`/`fontsize`/DPI change in the same script; a table-overflow finding is a `tabular` column-spec or `\resizebox`/`\small` fix in `main.tex`; a display-equation overflow is a line-break (`\\` / `align`) fix in `main.tex`. The `paper-revise` command surfaces this guidance to the reviser explicitly.
- **Mathtext is the highest-stakes dim for a paper.** LaTeX is the source-of-truth; a rendered equation that diverges from intent is a correctness defect. Be willing to raise `mathtext_artifact_breaks_meaning` when the rendered math changes the claim.
- **Be specific.** A finding that says "Table 2's right two columns are clipped at the page margin; the best-F1 column is unreadable" is actionable; "the paper has table issues" is not. Cite figures/tables by their `\label{}` or caption and pages by `paper.pdf:page=<N>`.

**Scorecard kind declaration**: This critic's `_meta.json` SHOULD include `"scorecard_kind": "machine-summary"` per `anvil/lib/snippets/scorecard_kind.md`. The canonical payload is `_review.json` per #26 (the prose siblings are not produced — the vision critic ships `_review.json` directly).

## Git sync (opt-in, off by default)

Per `anvil/lib/snippets/git_sync.md` (`.anvil/anvil/lib/snippets/git_sync.md` in an installed consumer repo): if `.anvil/config.json` exists and `git.commit_per_phase` is `true`, end this phase: stage only the dirs this phase wrote, commit as `anvil(<skill>/<phase>): <thread>.{N} [<state>]`, push if `git.push` is `true`. Git failures warn and continue — never fail the phase. When the config or knob is absent, skip this step entirely (default off).

This phase's specifics:

- **Ordering**: after the staged-sidecar atomic rename (issue #350) lands the final-named `<thread>.{N}.vision/` — so only complete sidecars are ever committed.
- **Staging target**: ONLY this command's own `<thread>.{N}.vision/` sidecar (never sibling critics' dirs — the narrow scope keeps the hook safe under parallel critic fan-out).
- **Commit**: `anvil(paper/vision): <thread>.{N} [<state>]` (the bracket carries the thread's current derived state per SKILL.md §State machine — vision is a non-gating critic and does not advance the state machine on its own).
