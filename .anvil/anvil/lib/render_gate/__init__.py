"""Deterministic render-gate for paginated Anvil artifacts.

This is the LaTeX-skill analog of ``anvil/lib/marp_lint.py``: a
cheap, deterministic pre-flight gate over a compiled PDF (and its compile
log + sources) that runs *before* the expensive content review. It checks
four properties:

1. **Page fit** — page count of the PDF against an optional cap (skill-set,
   per-thread overridable via ``.anvil.json``). When ``page_cap`` is ``None``
   the check is skipped (a first-class no-op — the common case).
2. **Overfull boxes** — greps the LaTeX log for ``Overfull \\hbox`` /
   ``Overfull \\vbox`` advisories whose numeric amount exceeds
   ``overfull_threshold_pt`` (default ``5.0pt``).
3. **Compile success** — non-zero engine exit OR missing output PDF.
4. **Placeholders** — scans source files for ``TODO`` / ``[TBD]`` /
   ``(figure)`` / missing-include patterns, with per-skill extras.

Memo mode (``kind="memo"``)
---------------------------

When invoked with ``kind="memo"``, the gate routes through a separate
seven-dimension flow tailored to the ``anvil:memo`` markdown → PDF
rendering pipeline shipped by Epic #158. The seven memo checks are:

1. ``memo_compile_success`` — pandoc exited 0, the PDF exists, and the
   page count is positive.
2. ``memo_page_fit`` — rendered page count vs ``target_length.pages``
   (error) or the 400-wpp-converted ``target_length.words`` range
   (warning). Not run when ``target_length`` is absent.
3. ``memo_overfull_check`` — pandoc / weasyprint / wkhtmltopdf stderr
   warnings about lines that don't break cleanly (warning severity;
   graceful-degrades when the renderer emits no such warnings).
4. ``memo_image_refs_exist`` — delegates to
   ``anvil/skills/memo/lib/memo_image_refs.py::lint_memo_image_refs``
   (PR #160) and aggregates findings. Source-side lint already runs at
   review phase; render-gate adds the post-render catch.
5. ``memo_image_dimensions`` — advisory image-dimension/aspect sanity
   check (issue #395). For every image referenced from the body plus
   every PNG/JPEG under ``<version_dir>/exhibits/``, three stdlib
   header checks (pure ``struct`` PNG-IHDR / JPEG-SOFn parsing — no
   PIL, no subprocess): (a) pixel ceiling — width or height >
   ``image_max_px`` (default :data:`MEMO_IMAGE_MAX_PX` = 6000 px);
   (b) extreme aspect — ratio > :data:`MEMO_IMAGE_MAX_ASPECT` (6:1)
   either direction; (c) declared-vs-actual — when a sibling
   ``src/<stem>.py`` declares a parseable ``figsize=(W, H)`` and a
   ``dpi=N`` (or the PNG carries a ``pHYs`` density chunk), flag
   actual dims diverging more than
   :data:`MEMO_IMAGE_DECLARED_TOLERANCE` (1.5×) from declared —
   silent skip when nothing declarative is parseable. A fourth check
   (d) content-bbox vs canvas — content occupying <
   :data:`MEMO_IMAGE_MIN_CONTENT_RATIO` (25%) of the canvas, the
   exact signature of the matplotlib ``bbox_inches="tight"`` +
   rogue-artist + transparent-canvas failure (the 16,622×5,652 px
   canary) — needs PIL/numpy via the ``[image_lint]`` extra,
   graceful-skips with a ``reasons`` breadcrumb when absent, and is
   skipped per-image for canvases already over the pixel ceiling
   (decoding a 90-megapixel image is the hazard, not the cure). ALL
   findings are warning severity and the dimension never joins
   ``failed_gates`` (the same advisory model as
   ``memo_overfull_check``: recorded in ``findings``, ``passed``
   unaffected, no ``CriticalFlag``). Suppression for body-referenced
   images via ``<!-- anvil-lint-disable: memo_image_dimensions -->``
   (suppressed hits surface as info findings).
6. ``memo_placeholder_scan`` — adapts ``DEFAULT_PLACEHOLDER_PATTERNS``
   for markdown comment syntax (``<!-- TODO -->``, ``[TBD]``,
   ``_TKTKTK_``). Suppression via
   ``<!-- anvil-lint-disable: memo_placeholder_scan -->``.
7. ``memo_rhetoric_lint`` — advisory deterministic rhetoric lint
   (issue #463). Delegates to
   ``anvil/lib/rhetoric_lint.py::lint_rhetoric`` over the body
   markdown: rule-set-driven phrase/trope/AI-tell scanning (phrase,
   regex, and frequency rule kinds; the framework default set is
   ``DEFAULT_RHETORIC_RULES`` plus the em-dash-density frequency
   rule). Fenced code blocks and HTML comments are excluded from the
   scan. Consumer rules merge over the defaults via the optional
   ``rhetoric_rules_path`` JSON file (wired from the #461 voice
   contract's ``voice.rhetoric_rules`` sub-key via
   ``anvil.lib.project_brief.resolve_rhetoric_rules`` — issue #468;
   memo-render step 4g is the caller); malformed
   consumer JSON graceful-degrades to a defaults-only run with one
   warning finding naming the parse error. ALL findings are warning
   severity (info when suppressed or consumer-downgraded) and the
   dimension never joins ``failed_gates`` — the same advisory model
   as ``memo_image_dimensions`` (#395): findings recorded in
   ``_progress.json.render_gate.findings``, ``passed`` unaffected,
   no ``CriticalFlag``. Per-line suppression via
   ``<!-- anvil-lint-disable: memo_rhetoric_lint -->`` (same line or
   line directly above; suppressed hits surface as info findings).
   Rationale: rhetoric rules have irreducible false positives (quoted
   material, deliberate style); dim 9 *Rhetorical economy* critics
   make the judgment call with this as mechanical evidence.

The memo path also owns ``_render_memo_source`` (the pandoc → weasyprint
OR wkhtmltopdf OR xelatex chain) with engine preflight via the
``check_*_available`` family in ``anvil/lib/render.py`` (added in #168).
Phase 3's ``memo-render`` command wires this into the skill; this module
is the shippable lib primitive without command changes.

Result composition mirrors ``marp_lint.LintResult``: a JSON-serializable
``GateResult`` that captures every finding, plus a typed ``Review``
(``kind=Kind.TOOL_EVIDENCE``) so the gate plugs into the existing
``anvil/lib/critics.py::aggregate`` + ``compute_verdict`` pipeline without
any schema or aggregator change. When the gate fails, the ``Review``
carries one ``CriticalFlag`` per failed dimension, which forces
``Verdict.BLOCK`` downstream.

page_cap calibration
--------------------

The memo gate's ``memo_page_fit`` dimension converts
``target_length.words`` into a rendered-page-count range via a
words-per-page (wpp) proxy. The default is :data:`MEMO_WORDS_PER_PAGE`
(**400 wpp**), which is calibrated for the **mixed-content** memo the
canary's investment-memo example assumes (prose body with occasional
tables). Pure dense-prose memos (no tables) run closer to 500-600 wpp,
while table-heavy memos (financial models, comp tables, sensitivity
matrices) run effectively ~300-350 wpp once the table whitespace is
accounted for — the 400-wpp default is the practical midpoint that
avoids systematically misfiring on table-dense memos.

The override hook is per-thread: callers can pass
``words_per_page=<positive number>`` to :func:`gate` (when
``kind="memo"``) to use a custom conversion factor for the
``target_length.words → page range`` conversion. The ``memo-render``
command reads this from ``<thread>/.anvil.json`` as the
``render_gate.words_per_page`` field (see
``anvil/skills/memo/commands/memo-render.md`` step 4 + the SKILL.md
``.anvil.json`` reference).

Validation: a non-numeric override or one ``<= 0`` is silently
discarded and the default (:data:`MEMO_WORDS_PER_PAGE`) is used,
matching :func:`_resolve_target_length`'s graceful-degrade contract
for malformed inputs. The effective wpp is recorded in the
``memo_page_fit`` finding message so a reviewer can see which
calibration the gate used.

The override only affects the **derived** ``target_length.words →
pages`` path. When ``target_length.pages`` is declared directly, no
conversion happens and the override is a no-op. The word-count proxy
in rubric dim 7 (*Scope discipline*) remains authoritative for
length judgments — ``memo_page_fit`` is the advisory second layer.

Graceful degradation
--------------------

The gate degrades cleanly when toolchain pieces are missing:

- ``pdfinfo`` (poppler-utils) absent → page-fit check sets ``pages=None``
  and the gate continues with the other checks. Reasons include a
  remediation line (``brew install poppler`` / ``apt-get install
  poppler-utils``). This mirrors the ``pdftoppm`` pattern in
  ``anvil/lib/render.py``.
- Compile log absent → overfull check sets ``overfull_boxes=[]`` with a
  note in ``reasons``; the other checks still run.
- PDF missing entirely → page-fit and overfull checks skip; placeholder
  scan over the source still runs.

All four checks are **independent**: ``passed=False`` enumerates every
failed gate in ``reasons`` (no short-circuit). This is the same shape as
``marp_lint``.

Public API
----------

- ``gate(pdf_path, ...)`` — run the gate over an already-compiled PDF.
- ``compile_and_gate(tex_path, ...)`` — invoke the LaTeX engine, capture
  the log, then run the gate over the produced PDF. Used by the skills
  whose pipeline doesn't otherwise compile (installation, proposal) and as
  a fallback for the others when called before audit/finalize.
- ``GateResult`` — JSON-serializable result with ``to_json()`` (the issue
  body's ``{gate, pages, page_cap, overfull_boxes, compile, placeholders,
  pass, reasons}`` shape) and ``to_review(version_dir, critic_id)`` (the
  typed ``Review`` consumed by the critics aggregator).
- ``DEFAULT_PLACEHOLDER_PATTERNS`` — the default placeholder regex tuple;
  skills can extend via the ``placeholder_patterns`` arg.

Audit-time backstop pattern (issue #572)
----------------------------------------

The ip-skill audit commands (``ip-uspto-audit``,
``ip-uspto-provisional-audit``) reinvoke ``compile_and_gate(...)`` as a
**backstop** check, writing the result to the audit sibling's
``_gate.json``. The matching finalize commands then read that file at
their pre-finalize gate and refuse to assemble the terminal package
(``<thread>.final/`` / ``<thread>.counsel/``) when any overfull-box
finding is present. This closes the gap a *filed* legal artifact
exposed: a late-revise overfull introduced after the last pre-flight
pass would otherwise reach FILING-READY / COUNSEL-READY unchallenged.
The ip-skill call sites tighten the threshold to
``overfull_threshold_pt=2.0`` (the framework default of 5.0pt is
unchanged for ``installation`` / ``proposal`` / ``datasheet`` / ``paper``
/ ``report``). The legal-document regression fixture at
``tests/lib/fixtures/render_gate/overfull_legal_canary.txt`` (13 hits,
worst 83.6pt) is pinned in
``tests/lib/test_render_gate.py::test_overfull_legal_canary_shape`` so
threshold drift cannot silently re-open the hole.

Package split (issue #1128)
----------------------------
This module was a single 3,613-line file that grew incrementally,
issue-by-issue, along eight internally-commented section boundaries.
Issue #1128 splits it into a package along those same boundaries
(directly following the #1121 ``project_brief.py`` split precedent),
purely for maintainability — **no behavior change, no consumer
import-line change**:

- ``constants.py`` — general (non-memo) + memo-mode constants:
  dimension names, compile-status values, engine names, calibration
  values, and the shared regexes, plus :func:`_strip_nonrendered_regions`.
- ``results.py`` — :class:`GateFinding` and :class:`GateResult`.
- ``helpers.py`` — the shared parsing/scanning helpers: ``pdfinfo``
  page counting, the TeX-log file-scope-stack walker (issue #961), the
  overfull-box log parser (issue #668 dedupe), and the pending-marker-
  aware placeholder scanner (issue #842).
- ``probes.py`` — the poppler-utils probes for the issue-#692 render
  checks (glyph verification + embedded-image assertion).
- ``gate.py`` — the :func:`gate` public API (the four-dimension
  LaTeX-side gate, dispatching to the memo gate on ``kind="memo"``).
- ``memo.py`` — memo-mode (``kind="memo"``) internals: engine
  selection, theme-context discovery, the pandoc render invocation,
  the overfull-stderr parser, and the placeholder scanner.
- ``memo_image_dimensions.py`` — the issue #395 image-dimension
  helpers, plus :func:`_resolve_target_length` and the top-level
  memo-gate dispatcher :func:`_gate_memo` (both physically part of this
  module in the pre-split file's section boundary; see that module's
  docstring for why they stayed here rather than moving to ``memo.py``).
- ``compile_and_gate.py`` — the :func:`compile_and_gate` public API.

This ``__init__.py`` re-exports every name the pre-split module
exposed — both its ``__all__`` surface and the handful of non-``__all__``
names (``_check_memo_image_dimensions``, ``_coerce_image_max_px``,
``_coerce_words_per_page``, ``_discover_memo_theme_context``,
``_enumerate_memo_images``, ``_find_figure_source``, ``_gate_memo``,
``_parse_declared_figure_params``, ``_parse_memo_overfull``,
``_read_image_dimensions``, ``_read_jpeg_dimensions``,
``_read_png_dimensions``, ``_read_png_phys_dpi``, ``_render_memo_source``,
``_resolve_target_length``, ``_scan_memo_placeholders``,
``_scan_placeholders``, ``_select_memo_engine``, ``_OVERFULL_RE``,
``_file_at_offset``, ``_file_scope_transitions``, and the stdlib
``shutil`` module) that existing call sites import directly (either via
``from anvil.lib.render_gate import X`` or via module-attribute access
after ``import anvil.lib.render_gate as rg`` / ``as render_gate``) — so
every existing import across the repo's 30+ consumer files plus tests
keeps working unchanged. See ``anvil/lib/render_gate/*.py`` docstrings
for the per-module detail.
"""

from __future__ import annotations

import shutil as shutil

from anvil.lib.render_gate.compile_and_gate import compile_and_gate
from anvil.lib.render_gate.constants import (
    COMPILE_FAILED,
    COMPILE_OK,
    COMPILE_SKIPPED,
    COMPILE_UNAVAILABLE,
    DEFAULT_MEMO_PLACEHOLDER_PATTERNS,
    DEFAULT_PLACEHOLDER_PATTERNS,
    DIM_COMPILE,
    DIM_EMBEDDED_IMAGES,
    DIM_GLYPH_VERIFICATION,
    DIM_MEMO_COMPILE,
    DIM_MEMO_IMAGE_DIMENSIONS,
    DIM_MEMO_IMAGE_REFS,
    DIM_MEMO_OVERFULL,
    DIM_MEMO_PAGE_FIT,
    DIM_MEMO_PLACEHOLDERS,
    DIM_MEMO_RHETORIC,
    DIM_OVERFULL,
    DIM_PAGE_FIT,
    DIM_PLACEHOLDERS,
    GATE_NAME,
    MEMO_ENGINE_WEASYPRINT,
    MEMO_ENGINE_WKHTMLTOPDF,
    MEMO_ENGINE_XELATEX,
    MEMO_IMAGE_DECLARED_TOLERANCE,
    MEMO_IMAGE_MAX_ASPECT,
    MEMO_IMAGE_MAX_PX,
    MEMO_IMAGE_MIN_CONTENT_RATIO,
    MEMO_WORDS_PER_PAGE,
)
from anvil.lib.render_gate.constants import _OVERFULL_RE as _OVERFULL_RE
from anvil.lib.render_gate.gate import gate
from anvil.lib.render_gate.helpers import _file_at_offset as _file_at_offset
from anvil.lib.render_gate.helpers import (
    _file_scope_transitions as _file_scope_transitions,
)
from anvil.lib.render_gate.helpers import _scan_placeholders as _scan_placeholders
from anvil.lib.render_gate.memo import _coerce_image_max_px as _coerce_image_max_px
from anvil.lib.render_gate.memo import (
    _coerce_words_per_page as _coerce_words_per_page,
)
from anvil.lib.render_gate.memo import (
    _discover_memo_theme_context as _discover_memo_theme_context,
)
from anvil.lib.render_gate.memo import _parse_memo_overfull as _parse_memo_overfull
from anvil.lib.render_gate.memo import _render_memo_source as _render_memo_source
from anvil.lib.render_gate.memo import (
    _scan_memo_placeholders as _scan_memo_placeholders,
)
from anvil.lib.render_gate.memo import _select_memo_engine as _select_memo_engine
from anvil.lib.render_gate.memo_image_dimensions import (
    _check_memo_image_dimensions as _check_memo_image_dimensions,
)
from anvil.lib.render_gate.memo_image_dimensions import (
    _enumerate_memo_images as _enumerate_memo_images,
)
from anvil.lib.render_gate.memo_image_dimensions import (
    _find_figure_source as _find_figure_source,
)
from anvil.lib.render_gate.memo_image_dimensions import _gate_memo as _gate_memo
from anvil.lib.render_gate.memo_image_dimensions import (
    _image_content_ratio as _image_content_ratio,
)
from anvil.lib.render_gate.memo_image_dimensions import (
    _parse_declared_figure_params as _parse_declared_figure_params,
)
from anvil.lib.render_gate.memo_image_dimensions import (
    _read_image_dimensions as _read_image_dimensions,
)
from anvil.lib.render_gate.memo_image_dimensions import (
    _read_jpeg_dimensions as _read_jpeg_dimensions,
)
from anvil.lib.render_gate.memo_image_dimensions import (
    _read_png_dimensions as _read_png_dimensions,
)
from anvil.lib.render_gate.memo_image_dimensions import (
    _read_png_phys_dpi as _read_png_phys_dpi,
)
from anvil.lib.render_gate.memo_image_dimensions import (
    _resolve_target_length as _resolve_target_length,
)
from anvil.lib.render_gate.results import GateFinding, GateResult

__all__ = [
    "DEFAULT_PLACEHOLDER_PATTERNS",
    "DEFAULT_MEMO_PLACEHOLDER_PATTERNS",
    "GATE_NAME",
    "DIM_PAGE_FIT",
    "DIM_OVERFULL",
    "DIM_COMPILE",
    "DIM_PLACEHOLDERS",
    "DIM_GLYPH_VERIFICATION",
    "DIM_EMBEDDED_IMAGES",
    "DIM_MEMO_COMPILE",
    "DIM_MEMO_PAGE_FIT",
    "DIM_MEMO_OVERFULL",
    "DIM_MEMO_IMAGE_REFS",
    "DIM_MEMO_IMAGE_DIMENSIONS",
    "DIM_MEMO_PLACEHOLDERS",
    "DIM_MEMO_RHETORIC",
    "COMPILE_OK",
    "COMPILE_FAILED",
    "COMPILE_SKIPPED",
    "COMPILE_UNAVAILABLE",
    "MEMO_ENGINE_WEASYPRINT",
    "MEMO_ENGINE_WKHTMLTOPDF",
    "MEMO_ENGINE_XELATEX",
    "MEMO_WORDS_PER_PAGE",
    "MEMO_IMAGE_MAX_PX",
    "MEMO_IMAGE_MAX_ASPECT",
    "MEMO_IMAGE_DECLARED_TOLERANCE",
    "MEMO_IMAGE_MIN_CONTENT_RATIO",
    "GateFinding",
    "GateResult",
    "gate",
    "compile_and_gate",
]
