"""Constants for the render-gate (issue #1128 package split).

General (non-memo) dimension names, compile-status values, and placeholder
patterns, plus the memo-mode (``kind="memo"``) constants: dimension names,
engine names, length/image-dimension calibration values, and the regexes
used by the LaTeX overfull-box parser, the memo overfull-stderr scanner,
and the glyph-verification source sweep (issue #692). Also carries
:func:`_strip_nonrendered_regions`, a small helper tied directly to the
regexes defined here (used by ``probes.py``'s glyph-verification sweep).

Split out of the former monolithic ``anvil/lib/render_gate.py`` (3613
lines) along its existing section banners — see
``anvil/lib/render_gate/__init__.py`` for the full package rationale.
"""

from __future__ import annotations

import re


# Default placeholder patterns. Skills can extend via the placeholder_patterns
# arg of ``gate``/``compile_and_gate``.
#
# NOTE (issue #855): ``[PENDING ...]`` / ``[PENDING: ...]`` markers are
# INTENTIONALLY NOT matched here. They are a permitted honest-disclosure
# convention (a value that does not exist yet — see
# ``anvil/lib/snippets/pending_marker.md``) handled by the dedicated
# ``anvil/lib/pending_marker.py`` gate, not by this generic placeholder scan.
# ``_scan_placeholders`` below carves out well-formed pending-marker spans
# (issue #842, ``_RENDER_GATE_PENDING_MARKER_RE``) so the two gates never
# conflict. Do not add a ``[PENDING ...]`` pattern to this tuple — it would be
# a no-op (the carve-out excludes it regardless) and risks confusing the two
# gates' semantics (pending markers never block/penalize; generic
# placeholders do).
DEFAULT_PLACEHOLDER_PATTERNS: tuple[str, ...] = (
    r"\bTODO\b",
    r"\[TBD(?:[:\s][^\]]*)?\]",
    r"\[FIXME(?:[:\s][^\]]*)?\]",
    r"\(figure\)",
    r"\\includegraphics\{[^}]*\.MISSING[^}]*\}",
    r"\.MISSING\b",
)


# Gate names used in findings/reasons and the JSON payload. These match the
# four checks the issue body enumerates.
GATE_NAME = "render_gate"
DIM_PAGE_FIT = "page_fit"
DIM_OVERFULL = "overfull_boxes"
DIM_COMPILE = "compile"
DIM_PLACEHOLDERS = "placeholders"
# Source-driven glyph verification (issue #692). Sweeps the source body for
# every non-ASCII codepoint and asserts each survives into ``pdftotext``
# output at >= its source count. Catches silent font glyph-drops (the STIX
# Two Text ``≠`` U+2260 canary) that a hardcoded allow-list misses by
# construction.
DIM_GLYPH_VERIFICATION = "glyph_verification"
# Embedded-image assertion (issue #692). Counts ``![...](path)`` references in
# the source body and asserts ``pdfimages -list`` reports at least that many
# embedded images. Catches the "zero embedded images, every other gate green"
# failure (the botho v2 canary — the #690 contract gap).
DIM_EMBEDDED_IMAGES = "embedded_images"

# Compile status values. ``ok`` and ``failed`` are the LaTeX-invoked outcomes;
# ``skipped`` means the caller did not run a compile (i.e. ``gate`` was given
# a pre-built PDF); ``unavailable`` means the requested engine was not on
# PATH.
COMPILE_OK = "ok"
COMPILE_FAILED = "failed"
COMPILE_SKIPPED = "skipped"
COMPILE_UNAVAILABLE = "unavailable"

# Pandoc has no ``Overfull`` semantics — when the engine is pandoc, the
# overfull-box check is a documented no-op (recorded in reasons).
PANDOC_ENGINE = "pandoc"


# Dimension names for the memo gate. The ``memo_`` prefix keeps them
# distinguishable from the LaTeX-side dimensions so downstream consumers
# can route on the specific failure without ambiguity.
DIM_MEMO_COMPILE = "memo_compile_success"
DIM_MEMO_PAGE_FIT = "memo_page_fit"
DIM_MEMO_OVERFULL = "memo_overfull_check"
DIM_MEMO_IMAGE_REFS = "memo_image_refs_exist"
DIM_MEMO_IMAGE_DIMENSIONS = "memo_image_dimensions"
DIM_MEMO_PLACEHOLDERS = "memo_placeholder_scan"
DIM_MEMO_RHETORIC = "memo_rhetoric_lint"

# Engine names for the memo render chain. Selection priority per architect
# Q1 (Epic #158): weasyprint > wkhtmltopdf > xelatex. Pandoc is the common
# front-end for all three branches.
MEMO_ENGINE_WEASYPRINT = "weasyprint"
MEMO_ENGINE_WKHTMLTOPDF = "wkhtmltopdf"
MEMO_ENGINE_XELATEX = "xelatex"

# Words-per-page proxy used to convert ``target_length.words`` into a
# rendered-page-count range when ``target_length.pages`` is not declared
# explicitly. Mirrors the constant documented in
# ``anvil/skills/memo/SKILL.md`` §"Length targets" and used by the rubric.
MEMO_WORDS_PER_PAGE = 400

# ``memo_image_dimensions`` (issue #395) defaults. The pixel ceiling is
# per-thread overridable via the ``image_max_px`` parameter on
# ``gate(kind="memo")`` (the same coerce-or-silently-fallback pattern as
# ``words_per_page``); the other three thresholds are framework-pinned in
# v1. Calibration anchor: the framework style
# (``anvil/lib/figures/anvil.mplstyle``: ``figure.figsize: 12, 7`` @
# ``savefig.dpi: 200``) produces a canonical 2400×1400 px figure — well
# under the 6000 px ceiling — while the canary failure (matplotlib
# ``bbox_inches="tight"`` inflated by a rogue artist on a transparent
# canvas) shipped at 16,622×5,652 px.
MEMO_IMAGE_MAX_PX = 6000
# Aspect-ratio ceiling (either orientation). Note the canary image
# (≈2.94:1) does NOT trip this — the pixel ceiling is the load-bearing
# check; aspect catches degenerate strip renders.
MEMO_IMAGE_MAX_ASPECT = 6.0
# Declared-vs-actual divergence tolerance: actual dims more than 1.5×
# off (either direction, either dimension) from ``figsize × dpi`` flag.
MEMO_IMAGE_DECLARED_TOLERANCE = 1.5
# Content-bbox floor for the optional PIL check: content occupying less
# than this fraction of the canvas area flags (tight-bbox rogue-artist
# signature — drawing in a corner of a giant transparent canvas).
MEMO_IMAGE_MIN_CONTENT_RATIO = 0.25
# Raster extensions enumerated by the exhibits glob. SVGs are skipped
# with a breadcrumb (viewBox semantics make "pixel dims" ill-defined).
_MEMO_IMAGE_EXTENSIONS = (".png", ".jpg", ".jpeg")

# Default placeholder patterns for the memo gate. Adapted from
# ``DEFAULT_PLACEHOLDER_PATTERNS`` for markdown comment syntax and the
# memo-author idioms (``_TKTKTK_`` is the canary's "to come" marker —
# pronounced "tee-kay"). The ``<!--`` / ``-->`` delimiters are not
# matched literally so a TODO outside an HTML comment also fires.
#
# NOTE (issue #855): as with ``DEFAULT_PLACEHOLDER_PATTERNS`` above, this
# tuple intentionally carries no ``[PENDING ...]`` pattern. Well-formed
# pending markers (see ``anvil/lib/snippets/pending_marker.md``) are the
# dedicated ``anvil/lib/pending_marker.py`` gate's territory — for the memo
# skill that gate runs as its own unconditional review step (see
# ``anvil/skills/memo/commands/memo-review.md`` step 4n), independent of this
# scan. Do not add a ``[PENDING ...]`` pattern here.
DEFAULT_MEMO_PLACEHOLDER_PATTERNS: tuple[str, ...] = (
    r"<!--\s*TODO[^>]*-->",
    r"<!--\s*TBD[^>]*-->",
    r"<!--\s*FIXME[^>]*-->",
    r"\bTODO\b",
    r"\[TBD(?:[:\s][^\]]*)?\]",
    r"\[FIXME(?:[:\s][^\]]*)?\]",
    r"\[TKTKTK\]",
    r"_TKTKTK_",
    r"\bTKTKTK\b",
    r"\(figure\)",
)

# Memo-side lint-disable directive (mirrors marp_lint and memo_image_refs).
# Per-line suppression: same line OR the line directly above.
_MEMO_LINT_DISABLE_RE = re.compile(
    r"<!--\s*anvil-lint-disable:\s*(?P<rules>[a-zA-Z0-9_,\-\s]+?)\s*-->",
)

# weasyprint / wkhtmltopdf surface line-wrap warnings on stderr. The
# patterns below are intentionally loose: any stderr line containing
# "overflow" / "doesn't fit" / "exceeds" / "line is too long" is recorded
# as a memo_overfull warning. Renderers that emit none of these patterns
# (a clean run) produce zero findings — the check graceful-degrades.
_MEMO_OVERFULL_PATTERNS: tuple[str, ...] = (
    r"(?i)overflow(?:s|ed|ing)?\b",
    r"(?i)doesn'?t fit",
    r"(?i)exceeds? (?:the )?(?:page|column|box|line)",
    r"(?i)line (?:is )?too (?:long|wide)",
    r"(?i)content does not fit",
    r"(?i)cannot break",
)
_MEMO_OVERFULL_RES = tuple(re.compile(p) for p in _MEMO_OVERFULL_PATTERNS)

# Regex for ``Overfull \hbox (12.3pt too wide) ...`` and the vbox / too-high
# variant. The amount group is captured as a float string. We also capture
# the line span (``at lines NN--MM``) when present.
_OVERFULL_RE = re.compile(
    r"Overfull\s+\\(?P<kind>[hv])box\s+\(\s*(?P<amount>\d+(?:\.\d+)?)pt\s+too\s+(?:wide|high)\s*\)"
    r"(?:[^\n]*?at\s+lines?\s+(?P<line_start>\d+)(?:--(?P<line_end>\d+))?)?",
    re.IGNORECASE,
)

# TeX/LaTeX engine logs delimit "now processing this file" with a bare
# ``(<path>`` — no space between the paren and the path — and close it with
# a matching ``)`` once the engine returns to the including file (issue
# #961). The path is whatever kpathsea resolved: a job-relative ``./foo.tex``
# for a document-local ``\input``, or an absolute path for a class/style
# file pulled from the TeX distribution. Matched only when the path ends in
# a recognized TeX source/support extension so we don't false-positive on
# unrelated parenthetical prose the engine or a package emits (e.g. "(see
# the log for details)"). No leading-character requirement on the path
# itself — absolute paths (``/usr/.../article.cls``) and relative ones
# (``./claims.tex``) both match.
_FILE_OPEN_RE = re.compile(
    r"\((?P<path>[^\s()]+\.(?:tex|sty|cls|clo|cfg|def|fd|ldf|cnf|map|enc))"
    r"(?=[\s)]|$)"
)

# Regex for the last-N LaTeX error lines (``! ...``). Used to surface engine
# error context when compile fails.
_LATEX_ERROR_RE = re.compile(r"^!.*$", re.MULTILINE)

# Markdown inline-image reference: ``![alt](path)``. Used by the
# embedded-image assertion (issue #692) to count how many images the body
# claims. The ``!`` prefix distinguishes images from plain links; the alt
# text and path are captured non-greedily. Reference-style images
# (``![alt][id]``) are intentionally NOT matched — the primer/report bodies
# use inline references exclusively (the ``exhibits/…png`` convention), and a
# reference-style definition would double-count against its use.
_MD_IMAGE_REF_RE = re.compile(r"!\[[^\]]*\]\(([^)]+)\)")


# Non-rendered source regions that the glyph-verification source sweep (issue
# #692) must exclude before counting non-ASCII codepoints. Characters in these
# regions live in the markdown source but never reach the rendered PDF body
# text, so counting them source-side produces a false glyph-drop. Order of
# stripping does not matter — each pattern is independently safe to blank out.
#   * HTML comments: ``<!-- … -->`` (non-greedy, DOTALL to span newlines).
#   * Inline-link / image URL targets: the ``(target)`` half of
#     ``[text](target)`` and ``![alt](target)`` — the visible link *text* is
#     kept (it renders); only the URL target is dropped. A non-ASCII path
#     segment (``…/café-page``) never appears in the rendered body.
#   * Autolinks: ``<https://…>`` angle-bracket URLs.
_HTML_COMMENT_RE = re.compile(r"<!--.*?-->", re.DOTALL)
_MD_LINK_TARGET_RE = re.compile(r"(!?\[[^\]]*\])\(([^)]*)\)")
_AUTOLINK_RE = re.compile(r"<([a-zA-Z][a-zA-Z0-9+.-]*:[^>\s]*)>")

# LaTeX-only: an unescaped ``%`` starts a comment that runs to end-of-line.
# MUST NOT be applied to markdown sources — a bare ``%`` there is a percent
# sign, not a comment opener. Mirrors ``numeric_consistency._LATEX_COMMENT_RE``
# (issue #856): box-drawing / accented characters used purely for a comment
# section rule (e.g. ``%% ── 4. The Item Pool ──``) never reach the rendered
# PDF, so counting them source-side produces a false glyph-drop identical in
# shape to a real missing-glyph defect.
_LATEX_COMMENT_RE = re.compile(r"(?<!\\)%[^\n]*")


def _strip_nonrendered_regions(text: str, *, latex: bool = False) -> str:
    """Blank out source regions that never reach the rendered body.

    Removes HTML comments, inline link/image URL *targets* (keeping the
    visible link text), and angle-bracket autolink URLs. Used by the
    glyph-verification source sweep so non-ASCII inside a URL path
    (``[x](https://ex.com/café-page)``) or a comment (``<!-- café -->``) is
    not miscounted as a dropped body glyph (issue #692).

    When ``latex=True`` (a ``.tex`` source body), also strips unescaped
    ``%`` LaTeX comments — non-ASCII characters used only for a comment-only
    section rule (e.g. box-drawing dashes) never reach the rendered PDF, so
    counting them would false-flag a glyph drop (issue #856).
    """
    text = _HTML_COMMENT_RE.sub(" ", text)
    # Keep the link text (group 1), drop the URL target (group 2).
    text = _MD_LINK_TARGET_RE.sub(lambda m: m.group(1) + "( )", text)
    text = _AUTOLINK_RE.sub(" ", text)
    if latex:
        text = _LATEX_COMMENT_RE.sub(" ", text)
    return text

