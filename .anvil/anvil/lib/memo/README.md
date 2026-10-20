# anvil/lib/memo/

Canonical pinned renderer substrate for `anvil:memo` PDF rendering.

This directory is the framework-level pin for the `anvil:memo` markdown
→ PDF chain. It is the memo-side analog of `anvil/lib/marp/` (the
pinned Marp config shared by `anvil:deck` and `anvil:slides`).

## Status

This is the **Phase 1 substrate** of Epic #158 (the `anvil:memo`
markdown → PDF rendering pipeline). Phase 1 ships the pinned config
files and renderer availability detection. The state machine, the
`memo-render` command, and the reviewer-side rubric wiring land in
Phases 2-4.

Until Phase 3 lands, these files exist for two reasons:

1. They are the **single source of truth** for the chosen typography
   and page-layout pin — when later phases land, they consume these
   files verbatim rather than re-deriving defaults inline.
2. They are referenced by the `MEMO_RENDERER_REMEDIATION` string in
   `anvil/lib/render.py` so the renderer availability check can point
   operators at the right files when an install gap is detected.

## Files

| File | Purpose |
|---|---|
| `styles.css` | Pinned default theme. Helvetica/Arial fallback, 11pt body, 0.75in margins, `@page` rule with footer page numbers. Consumed by the HTML chain (pandoc → weasyprint OR wkhtmltopdf). |
| `template.html` | Pandoc HTML template loading `$title$ / $author$ / $date$` from frontmatter and referencing `styles.css`. Consumed by the HTML chain. |
| `template.tex` | xelatex fallback template. Minimal `\documentclass{article}` with `geometry`, `fancyhdr`, `lastpage`, `hyperref`. Consumed only when neither weasyprint nor wkhtmltopdf is on PATH. |

## The rendering chain

The memo render path, from Phase 3 onward, is:

```
memo.md
  │
  ├── pandoc --template template.html --css styles.css → memo.html
  │       │
  │       ├── weasyprint memo.html memo.pdf   (preferred)
  │       └── wkhtmltopdf memo.html memo.pdf  (fallback)
  │
  └── pandoc --pdf-engine=xelatex --template template.tex → memo.pdf
          (fallback when neither HTML engine is available)
```

### Why this chain (and not some other one)

Each branch addresses a real install constraint observed on the
canary side. The chain was selected by the architect in Epic #158 and
is pinned here so Phase 3's command code is config-not-code.

- **`pandoc` is the common front-end.** It owns frontmatter parsing,
  citation rendering (when memos start using `cite.py`), table
  formatting, and `--metadata` injection. It is already a documented
  Anvil dependency (`anvil/lib/render.py::render_pandoc_to_pdf`); we
  are not adding a new tool, just naming a new path through it.
- **`weasyprint` is the preferred HTML-to-PDF engine.** It is a
  Python package (`pip install weasyprint`), supports the full CSS
  paged-media spec (the `@page` rule + counter(page) used in
  `styles.css`), and produces high-fidelity output. The cost is a
  Python install and a handful of native deps (cairo, pango).
  **Python 3.14 compatibility**: weasyprint 69.0 is not compatible with Python 3.14 (the CSS module fails to import). On Python 3.14, `check_weasyprint_available()` returns `False` (the runtime smoke test detects the failure) and the gate falls through to wkhtmltopdf or xelatex automatically. Install weasyprint only on Python <3.14 via `pip install weasyprint` or `pip install 'anvil[html]'`.
- **`wkhtmltopdf` is the HTML fallback.** It is a standalone binary
  (`brew install --cask wkhtmltopdf` / `apt-get install
  wkhtmltopdf`), supports the bulk of HTML+CSS without the Python
  install, and has slightly different paged-media handling that the
  framework treats as acceptable for memos. Some `@page` rules are
  passed via `--header-* / --footer-*` CLI flags rather than the CSS
  itself — the Phase 3 command code will handle that translation.
- **`xelatex` is the engine-of-last-resort.** It exists for
  environments where the HTML chain is unavailable but TeX Live is
  installed. The output is not pixel-identical to the HTML chain by
  design — the HTML chain owns the canonical typography. The xelatex
  fallback gets you a memo PDF, period.

### Renderer detection

`anvil/lib/render.py` ships three availability checks corresponding
to the three engines in the chain:

```python
from anvil.lib.render import (
    check_pandoc_available,
    check_weasyprint_available,
    check_wkhtmltopdf_available,
    MEMO_RENDERER_REMEDIATION,
)

if not check_pandoc_available():
    raise RenderError(MEMO_RENDERER_REMEDIATION)

if check_weasyprint_available():
    engine = "weasyprint"
elif check_wkhtmltopdf_available():
    engine = "wkhtmltopdf"
elif shutil.which("xelatex"):
    engine = "xelatex"
else:
    raise RenderError(MEMO_RENDERER_REMEDIATION)
```

`MEMO_RENDERER_REMEDIATION` carries the full install story for all four
binaries (pandoc + weasyprint + wkhtmltopdf + xelatex) so the operator
sees one actionable error rather than four sequential ones.

## Override discipline

Consumers who want custom typography, page layout, or LaTeX preamble
have two override paths, walked by the per-skill asset resolver in
this precedence:

| Tier | Path (consumer repo) | When to use |
|---|---|---|
| Per-theme (issue #322) | `<consumer>/.anvil/themes/<theme>/memo/<asset>` | **The durable override path.** Consumer-owned; the installer never overwrites files under `.anvil/themes/`. Use for one brand or many. |
| Consumer single-tenant | `<consumer>/.anvil/anvil/lib/memo/<asset>` | In-place edit of the installed framework copy. **Hash-protected on upgrade** (issue #490): a hand-edited asset is skipped-with-warning and preserved unless you re-run with `--force` (the Stage 5 lib copy records a `lib_hash` baseline, mirroring the #152 skill-body matrix). Still secondary to the durable theme tier; framework code under `.anvil/anvil/lib/` always upgrades regardless. |
| Framework default | shipped at `anvil/lib/memo/<asset>` (this directory) | Anvil's neutral baseline |

`<asset>` is one of `styles.css`, `template.html`, `template.tex`.
The resolver is implemented at
`anvil/skills/memo/lib/theme_resolver.py::resolve_memo_asset`; the
project BRIEF surfaces the theme name via the `theme:` frontmatter
key documented in `anvil/skills/memo/lib/project_brief.py`.

The install script (`scripts/install-anvil.sh`) copies the framework
defaults to `.anvil/anvil/lib/memo/` on every run, but since issue #490
the Stage 5 lib copy carries the same override-detection discipline as
the issue-#152 skill-body matrix (`.anvil/skills/<name>/`): the
installer records a `lib_hash` baseline over the documented override
assets (`styles.css`, `template.html`, `template.tex`) and, on
re-install, **skips with a warning and preserves** any of those assets
the consumer hand-edited — overwrite requires `--force`. The carve-out:
the rest of the lib tree (the importable `anvil.lib.*` framework code,
schema JSON, figures, marp config) and `anvil/__init__.py` always
upgrade unconditionally, so editing an override asset can never pin
stale framework code. For a durable, never-overwritten override, prefer
the theme tier: the installer scaffolds a consumer-owned starter theme
at `.anvil/themes/starter/` on install (skip-if-exists, issue #471);
declare `theme: starter` in the project BRIEF to enable it, or copy
it to a theme name of your own. When the consumer ships a custom
`styles.css` via either tier, the `memo-render` command picks it up
unchanged.

### Per-theme override (issue #322)

For consumers running multiple brands through one anvil install, the
**per-theme** tier inserts above the consumer single-tenant tier.
Declare a theme in the project BRIEF:

```yaml
# <consumer>/projects/smart-actuators/BRIEF.md
---
project: smart-actuators
theme: acme-semi
documents:
  - slug: investment-memo
    artifact_type: investment-memo
---
```

Then provide the theme's asset overrides under
`<consumer>/.anvil/themes/acme-semi/memo/`:

```
<consumer>/.anvil/themes/
  acme-semi/
    theme.yml                # accent_color, studio, render_engine, …
    memo/
      styles.css             # branded typography
      template.tex           # branded xelatex preamble
```

Themes can be partial: a theme that only overrides `styles.css` still
uses the framework default `template.html` and `template.tex`. The
resolver walks asset-by-asset, not tier-by-tier.

When the BRIEF declares `theme:` but the named theme directory is
missing or the specific asset is absent, the resolver falls through
to the framework default silently — never raises. This matches the
graceful-degrade discipline of the broader memo render path.

The theme.yml file may also carry a `render_engine:` pin (one of
`weasyprint`, `wkhtmltopdf`, `xelatex`) — see `anvil/lib/theme.py`
for the full schema. The engine pin is advisory: when the named
engine is not on PATH, the renderer falls through to the default
priority order rather than failing.

#### Per-doc `latex_header_includes` (issue #347)

For the canary's common case — a single memo that uses `{=latex}`
raw blocks for table-fidelity but doesn't justify a full
`template.tex` override — the BRIEF schema exposes a per-document
`latex_header_includes` knob. Free-form LaTeX preamble text is
threaded into pandoc's `header-includes` slot via
`--include-in-header` at render time, **only when** the dispatched
engine resolves to `xelatex`:

```yaml
# <project>/BRIEF.md
documents:
  - slug: investment-memo
    artifact_type: investment-memo
    render_engine: xelatex
    latex_header_includes: |
      \usepackage{xcolor}
      \definecolor{green}{HTML}{059669}
      \definecolor{ink}{HTML}{0f172a}
      \usepackage{tabularx}
      \newcolumntype{Y}{>{\raggedright\arraybackslash}X}
      \newenvironment{callout}{...}{...}
```

This is the lightweight alternative to a full `template.tex`
override: declare the packages, named colors, and custom
environments your `{=latex}` blocks reference, and ship the rest
of the framework default unchanged. When the dispatched engine is
HTML-side (`weasyprint` / `wkhtmltopdf`), the include is silently
skipped and the skip is recorded in `_progress.json.render_gate.reasons`
— the field is xelatex-only by name. See `memo-render` step 4d
for the render-time plumbing and `memo-draft` step 5c / `memo-revise`
step 6 for the draft / revise-side `_progress.json` carry.

#### Per-doc `render_template` / `render_lua_filters` / `render_metadata` (issue #391)

For consumers with an **existing, richer pandoc template** (branded
eyebrow, doc-version stamp, custom callout environments) plus Lua
filters and per-doc metadata, the BRIEF schema exposes three flat
per-document passthrough knobs:

```yaml
# <project>/BRIEF.md
documents:
  - slug: investment-memo
    artifact_type: investment-memo
    render_engine: xelatex
    render_template: sphere-memo-template.tex   # resolved against the project root
    render_lua_filters: [strip-alt.lua]         # --lua-filter per entry, in order
    render_metadata:                            # -M key=value per entry
      doc-type: "Investment Memo"
      doc-version: "Draft v{N}"                 # {N} = version number, expanded at render time
```

Semantics:

- `render_template` is applied as `--template <path>` **instead of**
  the theme/framework template, **iff** the file exists and its
  extension matches the dispatched engine chain (`.tex`/`.latex` on
  xelatex; `.html`/`.htm` on weasyprint/wkhtmltopdf). On mismatch or
  a missing file the default resolver chain applies and a skip
  breadcrumb lands in `_progress.json.render_gate.reasons` — the same
  silent-with-record contract as `latex_header_includes`.
- `render_lua_filters` and `render_metadata` are engine-agnostic
  (they act on pandoc's front-end) and always applied when set.
- Paths are resolved against the directory containing `BRIEF.md`
  at render time (absolute paths used as-is), so re-running
  `memo-render` alone picks up template/filter edits.
- `_progress.json.phases.render.engine` / `.template` record which
  engine and template produced the PDF, so a styling regression is
  detectable on disk.

**Decision matrix** — pick the lightest tier that covers the need:

| Need | Knob |
|---|---|
| A few packages / colors / environments for `{=latex}` blocks | `latex_header_includes` (lightest) |
| A consumer-owned template + filters + per-doc metadata for one or a few docs | `render_template` / `render_lua_filters` / `render_metadata` |
| A reusable brand across many projects / portfolios | theme tier (`.anvil/themes/<theme>/memo/<asset>`) |

Precedence at render time: per-doc `render_template` > theme-resolved
template > consumer single-tenant override > framework default.
A consumer `.tex` template should preserve the pandoc 3.x compat
block (next section) just like a `template.tex` override.

#### `template.tex` override: preserve the pandoc 3.x compat block

The shipped `template.tex` ships a "Pandoc 3.x emission compatibility"
preamble block (`xcolor`, `soul`/`lua-ul`, `fancyvrb`, `longtable`,
`booktabs`, `array`, `calc`, `etoolbox`, `footnotehyper`/`footnote`,
`bookmark`, plus `\newcounter{none}`, `\providecommand{\tightlist}{...}`,
and a `\providecommand{\st}` fallback). This block tracks what
pandoc 3.x's default LaTeX emission expects the template to provide —
e.g. `\st{...}` from `~~strike~~`, the `\toprule`/`\midrule`/
`\bottomrule` family from any markdown table, `\Verb` from inline code,
etc. Without it, modern pandoc + xelatex fails with `\Undefined control
sequence` (see issue #277 for the canary reproducer).

Consumers overriding `template.tex` for custom typography, headers, or
fonts SHOULD preserve the compat block verbatim — it is functional, not
aesthetic. The `\IfFileExists` guards mean the block is safe to ship
even on thin TeX Live installs that lack `soul.sty` or
`footnotehyper.sty`: missing-package consumers get a slightly worse
memo (strikethrough passes through unstyled) rather than a hard compile
failure.

### Maintainer policy on aesthetic PRs

The default theme is **deliberately minimal**:

- System sans-serif fallback (Helvetica / Arial), no `@font-face`.
- 11pt body, 1.45 line-height, 0.75in margins.
- No color, no logos, no background images, no decorative rules.

Aesthetic-tuning PRs against the framework defaults are
**out-of-scope** by maintainer policy. The framework ships a usable,
reproducible default; consumers customize via the override path
above. This mirrors the `anvil/lib/marp/config.yml` discipline (the
shipped Marp themes are also deliberately neutral, with consumer
overrides expected for any branded deck).

The bar isn't "no styling" — it's "no color, no logos, no
`@font-face`, no decorative rules". Edits that stay inside that bar
but materially affect the rhetorical function of an artifact are
**in-scope**. The precedent is **issue #238**: booktabs-class rule
weights for tables (top rule, header-bottom rule, final-row bottom
rule, no vertical rules, `tabular-nums` on data cells). Comparison
tables in synthesis / feedback memos carry rhetorical load — the
LaTeX fallback already emits booktabs-quality output via the default
`template.tex`, and the markdown render path is expected to track
that quality. Rule-weight tuning for the shipped `styles.css` `table`
block is treated as a functional defaults fix, not an aesthetic PR.

Functional bugs in the defaults (an `@page` rule that breaks
weasyprint, a `\setmainfont` line that fails on TeX Live without
Helvetica, a pandoc template variable that doesn't render) ARE
in-scope and should be filed as issues.

## See also

- `anvil/lib/marp/config.yml` — the precedent for a pinned framework
  renderer config with a "why pinned" doc block. Memo's
  `lib/memo/README.md` is modeled on the prose in that file.
- `anvil/lib/render.py` — `check_pandoc_available`,
  `check_weasyprint_available`, `check_wkhtmltopdf_available`, and the
  `MEMO_RENDERER_REMEDIATION` constant.
- Epic #158 — the four-phase plan for the full `anvil:memo` PDF
  rendering pipeline. This file is the Phase 1 substrate.
