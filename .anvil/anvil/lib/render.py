"""Rendering helpers shared by Anvil vision critics.

This module is the "render-the-artifact-to-pixels" primitive consumed by
``anvil/lib/vision.py`` and per-skill vision critics. It wraps four
external tools as subprocess shell-outs:

- ``marp`` (the Marp CLI) for Markdown deck/slides → PDF.
- ``pdftoppm`` (poppler-utils) for PDF → per-page PNGs. This is the
  primary path; ``pdf2image`` (Python wrapper around the same library) is
  a documented fallback for environments where ``pdftoppm`` is not on
  PATH but the Python wheel is installed.
- ``pandoc`` for prose Markdown (paper/report) → PDF.
- Nothing — for ``render_matplotlib_figures`` which just enumerates an
  already-rendered ``figures/`` directory.

Design notes
------------

1. **Subprocess-only.** No native Python bindings (no PyMuPDF, no
   poppler-python). Skills get a consistent installation story: install
   the system binaries, not a parallel set of Python wheels.
2. **No re-execution of figure generators.** The matplotlib walker
   enumerates PNGs that the skill's ``figures`` command has already
   produced; vision is a critic, not a producer.
3. **Marp config pin.** ``render_marp_to_pdf`` always invokes
   ``marp --config-file anvil/lib/marp/config.yml`` (per #32) so the
   rendered PDF matches what the user actually sees in production.
4. **Domain exceptions.** Each renderer raises ``RenderError`` with the
   captured stderr on non-zero exit so callers can surface the failure
   uniformly. ``RenderError`` is also raised when a required binary is
   missing — the caller should not have to grep ``FileNotFoundError``
   tracebacks.

pdftoppm vs pdf2image
---------------------

The default path uses ``pdftoppm`` directly. It's the upstream tool
shipped by poppler-utils and is already documented as a ``deck-design``
dependency. Output filenames follow pdftoppm's convention: passing
``page`` as the output basename produces ``page-1.png``, ``page-2.png``,
etc. (one-indexed, no zero-padding). ``render_pdf_to_pngs`` re-walks
the directory and returns the sorted list.

The ``pdf2image`` Python wrapper (https://pypi.org/project/pdf2image/)
calls ``pdftoppm`` under the hood. It is documented here as a fallback
for environments where the Python wheel is preferred over a system
package install, but is not used by default — ``pdftoppm`` directly
keeps the dependency set minimal.

If neither is available, ``render_pdf_to_pngs`` raises ``RenderError``
with a message naming both options.
"""

from __future__ import annotations

import importlib.util
import shutil
import subprocess
from pathlib import Path
from typing import List, Optional


# Default Marp config path, resolved relative to THIS module file (not the
# process cwd). This is load-bearing for consumer installs: the module ships
# to ``.anvil/anvil/lib/render.py`` and the config sits beside it at
# ``.anvil/anvil/lib/marp/config.yml``. A cwd-relative default (the old
# ``Path("anvil/lib/marp/config.yml")``) silently pointed marp at a
# nonexistent path whenever the process ran from a consumer repo root. The
# ``__file__``-relative form resolves correctly in both a source checkout and
# an installed consumer repo. Callers may still override via ``config=``.
DEFAULT_MARP_CONFIG = Path(__file__).parent / "marp" / "config.yml"


class RenderError(RuntimeError):
    """A rendering subprocess failed or a required binary is missing."""


# ---------------------------------------------------------------------------
# Marp Markdown → PDF
# ---------------------------------------------------------------------------


def render_marp_to_pdf(
    deck_md: Path,
    out_pdf: Path,
    config: Optional[Path] = None,
) -> Path:
    """Render a Marp Markdown deck to PDF.

    Invokes the ``marp`` CLI with ``--pdf --html
    --config-file <config> --allow-local-files`` so raw HTML, local image
    references, and the pinned Marp options (per #32) all survive into the
    rendered PDF.

    Note: ``--html`` does NOT cause inline ```mermaid fences to render as
    diagrams in the PDF (verified false, issue #65) — those must be
    pre-rendered to PNG via ``mmdc`` (see :func:`check_mmdc_available`).

    Parameters
    ----------
    deck_md:
        Path to the deck source (``deck.md`` or ``slides.md``).
    out_pdf:
        Output PDF path. Parent directory must exist.
    config:
        Optional override for the Marp config file. Defaults to
        ``anvil/lib/marp/config.yml`` per #32. Tests pass an explicit
        path; production callers should pass ``None`` to get the framework
        pin.

    Returns
    -------
    The output PDF path (the same as ``out_pdf``), for caller chaining.

    Raises
    ------
    RenderError
        If ``marp`` is not on PATH, or returns non-zero exit status.
    FileNotFoundError
        If ``deck_md`` does not exist.
    """
    deck_md = Path(deck_md)
    out_pdf = Path(out_pdf)
    if not deck_md.exists():
        raise FileNotFoundError(f"deck source not found: {deck_md}")

    if shutil.which("marp") is None:
        raise RenderError(
            "marp CLI not found on PATH. Install with "
            "`npm install -g @marp-team/marp-cli` or use `npx`."
        )

    config_path = config if config is not None else DEFAULT_MARP_CONFIG

    cmd = [
        "marp",
        str(deck_md),
        "--pdf",
        "--html",
        "--config-file",
        str(config_path),
        "--allow-local-files",
        # --no-stdin (belt) + stdin=DEVNULL (suspenders): in non-TTY/agent
        # contexts stdin is often an open pipe, and marp-cli otherwise prints
        # "Currently waiting data from stdin stream" and blocks forever (#620).
        "--no-stdin",
        "--output",
        str(out_pdf),
    ]

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        check=False,
        stdin=subprocess.DEVNULL,
    )
    if result.returncode != 0:
        raise RenderError(
            f"marp failed (exit {result.returncode}): "
            f"{result.stderr.strip() or result.stdout.strip()}"
        )
    return out_pdf


# ---------------------------------------------------------------------------
# Mermaid (mmdc) preflight
# ---------------------------------------------------------------------------

# Remediation message surfaced when ``mmdc`` is absent. Shared by the
# figurer preflight and any caller that wants to emit a ``[blocker]`` with the
# full install story. ``mmdc`` is REQUIRED for any deck containing a diagram:
# inline ```mermaid fences do NOT render as diagrams in the canonical
# ``marp --pdf`` output (verified, issue #65) — they degrade to raw code — so
# ``mmdc → PNG`` is the only working diagram path for the PDF.
MMDC_REMEDIATION = (
    "mmdc (mermaid-cli) not found on PATH — required to render mermaid "
    "diagrams to PNG. Install with `npm install -g @mermaid-js/mermaid-cli`. "
    "Note: mmdc pulls Puppeteer + a ~300MB+ headless Chromium on first "
    "install. In CI/containers Chromium typically needs --no-sandbox: pass "
    "`mmdc --puppeteerConfigFile <file>` where <file> contains "
    '{"args":["--no-sandbox"]}.'
)


def check_mmdc_available() -> bool:
    """Return ``True`` if the ``mmdc`` (mermaid-cli) binary is on PATH.

    This is the preflight guard the deck/slides figurers run before any
    ``mmdc → PNG`` render. It mirrors the ``shutil.which("marp")`` guard in
    :func:`render_marp_to_pdf` so the figurer can fail fast with a legible
    ``[blocker]`` (see :data:`MMDC_REMEDIATION`) instead of producing a deck
    that references a PNG ``mmdc`` never rendered.

    ``mmdc`` is required for any deck containing a diagram, not a fallback:
    inline ```mermaid fences do not render in the canonical ``marp --pdf``
    output (verified, issue #65). A deck with zero diagrams does not need
    ``mmdc`` and callers should not invoke this preflight in that case.

    Kept binary-presence-only (no Chromium launch) so it is unit-testable
    with a stubbed/monkeypatched ``shutil.which`` and requires no real
    Chromium at test time.

    NOTE: "binary present" is NOT the same as "renderer can launch." ``mmdc``
    drives a pinned Puppeteer + headless Chromium; a canary run (issue #692)
    hit a ``mmdc`` that was on PATH while its pinned Chromium (v148) was
    absent from ``~/.cache/puppeteer``, so every diagram render would have
    failed at launch. Callers that need launch confidence should chain this
    fast PATH check with :func:`check_mmdc_launchable` (a real probe render).
    """
    return shutil.which("mmdc") is not None


# Remediation surfaced when ``mmdc`` is on PATH but its Puppeteer/Chromium
# launch fails (the issue-#692 canary signal). This is a *different* failure
# from :data:`MMDC_REMEDIATION` (binary absent): here the binary exists but
# the headless browser it drives cannot start. The working fallback the canary
# used was a puppeteer-config ``executablePath`` override to system Chrome.
MMDC_LAUNCH_REMEDIATION = (
    "mmdc is on PATH but failed a launch probe — its pinned Puppeteer "
    "Chromium is likely missing (not downloaded to ~/.cache/puppeteer) or "
    "cannot start. Two fixes: (1) install the pinned browser with "
    "`npx puppeteer browsers install chrome`; or (2) point mmdc at an "
    "existing system Chrome via a puppeteer config file — "
    "`mmdc --puppeteerConfigFile <file>` where <file> contains "
    '{"executablePath":"/path/to/google-chrome","args":["--no-sandbox"]}. '
    "In CI/containers the --no-sandbox arg is usually also required."
)


def check_mmdc_launchable(*, timeout: float = 30.0) -> bool:
    """Return ``True`` if ``mmdc`` is on PATH AND passes a real launch probe.

    Two-stage check, mirroring :func:`check_weasyprint_available` (#308):

    1. :func:`check_mmdc_available` — fast ``shutil.which`` PATH test. Returns
       ``False`` immediately if the binary is absent (no subprocess spawn).
    2. A trivial probe render — write a one-node mermaid source to a temp file
       and run ``mmdc --input <probe.mmd> --output <probe.png>``. This
       exercises the full Puppeteer/Chromium launch path (unlike
       ``mmdc --version``, which only prints the Node CLI version without
       touching the browser). A non-zero exit, timeout, or ``OSError`` returns
       ``False`` rather than raising, matching the graceful-degrade contract
       of the ``check_*_available`` family.

    This is the launchability guard for the issue-#692 canary failure: ``mmdc``
    present on PATH but its pinned Chromium absent from ``~/.cache/puppeteer``,
    so every real diagram render fails at browser launch even though
    :func:`check_mmdc_available` reports the binary as available. Callers
    should run :func:`check_mmdc_available` first (fast) and, before committing
    to a batch of diagram renders, optionally call this probe; on ``False``
    surface :data:`MMDC_LAUNCH_REMEDIATION`.

    This function is deliberately kept SEPARATE from
    :func:`check_mmdc_available` (rather than folding a probe into it) so the
    existing binary-presence-only contract and its call sites/tests remain
    unchanged and no real Chromium is required in the default unit suite. Tests
    monkeypatch ``subprocess.run`` to exercise the probe outcomes without a
    real browser.

    Parameters
    ----------
    timeout:
        Seconds to allow the probe render before treating it as a launch
        failure. Chromium cold-start plus a trivial render is well under the
        30 s default; a hang past it is itself a launch problem.
    """
    if not check_mmdc_available():
        return False
    import tempfile

    with tempfile.TemporaryDirectory() as td:
        probe_mmd = Path(td) / "probe.mmd"
        probe_png = Path(td) / "probe.png"
        # Minimal valid mermaid grammar — a single-node flowchart. Enough to
        # force mmdc through the Puppeteer launch + SVG→PNG path.
        probe_mmd.write_text("flowchart TD\n  A[probe]\n", encoding="utf-8")
        try:
            result = subprocess.run(
                [
                    "mmdc",
                    "--input",
                    str(probe_mmd),
                    "--output",
                    str(probe_png),
                ],
                capture_output=True,
                timeout=timeout,
            )
        except (OSError, subprocess.TimeoutExpired):
            return False
        return result.returncode == 0 and probe_png.exists()


# Default path to the shared Anvil mermaid theme (navy nodes, muted-grey
# edges, Helvetica). Resolved relative to THIS module file (not the process
# cwd), so it points at the theme shipped beside the module — in a consumer
# install that is ``.anvil/anvil/lib/figures/mermaid-theme.json``. Callers may
# still override via ``config=``.
DEFAULT_MERMAID_THEME = Path(__file__).parent / "figures" / "mermaid-theme.json"


def render_mermaid_to_png(
    src_mmd: Path,
    out_png: Path,
    *,
    width: int = 1600,
    height: int = 900,
    scale: int = 2,
    background_color: str = "white",
    config: Optional[Path] = None,
) -> Path:
    """Render a Mermaid ``.mmd`` source to a PNG via the ``mmdc`` CLI.

    This is the canonical wrapper consumed by ``deck-figures`` and
    ``slides-figures`` (issue #545). The two skills previously documented
    identical inline ``mmdc`` invocations; promoting the shared call into one
    Python helper gives a single place to evolve the flag set (mirrors the
    "lib promotion after second consumer" pattern documented in
    ``CLAUDE.md``).

    The default flag set:

    - ``--width 1600 --height 900`` — viewport the diagram renders INTO
      (NOT the output canvas — mmdc crops the PNG to the diagram's intrinsic
      bounding box after rendering, so small-node-count ``flowchart LR``
      grammars still produce wide-thin output regardless of this value).
    - ``--scale 2`` — multiplies the rendered SVG dimensions by 2 before PNG
      conversion. This is the load-bearing knob for legibility on the
      default deck theme: it doubles pixel density so a 784×102 thin strip
      becomes 1568×204, which is legible at the theme's ``max-height`` cap.
      Without ``--scale``, the documented invocation produces unusable PNGs
      for sparse flowchart grammars (the goodboy canary signal that drove
      issue #545).
    - ``--backgroundColor white`` — opaque white background by default; pass
      ``transparent`` to overlay on theme-colored slide backgrounds.
    - ``-c anvil/lib/figures/mermaid-theme.json`` — the shared navy-on-grey
      Anvil mermaid theme. Pass ``config=None`` to use this default, or an
      explicit path to override (consumers who ship their own theme).

    Orientation guidance (NOT enforced by this function): for cyclic
    flowcharts (e.g., a 3-node feedback loop), prefer ``flowchart TB`` over
    ``flowchart LR`` in the ``.mmd`` source. ``LR`` with a small node count
    crops to a wide-thin strip that ``--scale 2`` legibilizes but does not
    re-orient. The figurer commands document this convention; this wrapper
    does NOT auto-rewrite (an orientation auto-detect is a tracked follow-up).

    Parameters
    ----------
    src_mmd:
        Path to the input ``.mmd`` (Mermaid grammar) source.
    out_png:
        Output PNG path. Parent directory must exist (the figurer typically
        creates ``figures/`` ahead of calling).
    width, height:
        Viewport dimensions in pixels. Defaults to ``1600x900``. Note: this
        is the render viewport, not the output canvas — see the ``--scale``
        note above for the legibility knob.
    scale:
        Multiplier applied to the rendered SVG before PNG conversion. The
        default ``2`` is the issue-#545 fix: it doubles pixel density so
        sparse flowchart grammars produce legible PNGs at the deck theme's
        ``max-height`` cap.
    background_color:
        Mermaid ``--backgroundColor`` value. ``"white"`` (default),
        ``"transparent"``, or a hex color.
    config:
        Optional override for the mermaid theme config (``-c <file>``).
        Defaults to :data:`DEFAULT_MERMAID_THEME` when ``None``.

    Returns
    -------
    The output PNG path (the same as ``out_png``), for caller chaining.

    Raises
    ------
    RenderError
        If ``mmdc`` is not on PATH (see :data:`MMDC_REMEDIATION` for the
        full install story), or returns non-zero exit status.
    FileNotFoundError
        If ``src_mmd`` does not exist.
    """
    src_mmd = Path(src_mmd)
    out_png = Path(out_png)
    if not src_mmd.exists():
        raise FileNotFoundError(f"mermaid source not found: {src_mmd}")

    if not check_mmdc_available():
        raise RenderError(MMDC_REMEDIATION)

    config_path = config if config is not None else DEFAULT_MERMAID_THEME

    cmd = [
        "mmdc",
        "--input",
        str(src_mmd),
        "--output",
        str(out_png),
        "--width",
        str(width),
        "--height",
        str(height),
        "--scale",
        str(scale),
        "--backgroundColor",
        background_color,
        "-c",
        str(config_path),
    ]

    result = subprocess.run(
        cmd, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise RenderError(
            f"mmdc failed (exit {result.returncode}): "
            f"{result.stderr.strip() or result.stdout.strip()}"
        )
    return out_png


# ---------------------------------------------------------------------------
# pdfjam preflight (OPTIONAL — only needed for slides-handout N-up layouts)
# ---------------------------------------------------------------------------

# Remediation message surfaced when ``pdfjam`` is absent and a handout layout
# that needs it (``--4-up`` or ``--2-up``) is requested. ``pdfjam`` is OPTIONAL
# at the framework level: ``slides-handout --notes-below`` uses Marp's native
# ``--pdf-notes`` mode (one slide per page with notes printed beneath) and
# requires no post-processing. Marp's rendering model is fundamentally
# one-section-per-page; there is no Marp CLI flag (or CSS injection) that
# combines N sections onto a single rendered page, so a post-process step is
# the only N-up path for the ``--4-up`` and ``--2-up`` handout variants.
PDFJAM_REMEDIATION = (
    "pdfjam (TeX Live's pdfjam package) not found on PATH — required only for "
    "`slides-handout --4-up` and `slides-handout --2-up` N-up handout layouts. "
    "Install via `tlmgr install pdfjam` (if TeX Live is already present), "
    "`apt-get install texlive-extra-utils` (Debian/Ubuntu), or "
    "`brew install --cask mactex-no-gui` (macOS). "
    "Note: TeX Live is a multi-GB install; if you do not need N-up handouts "
    "you can use `slides-handout --notes-below` instead, which renders via "
    "Marp's `--pdf-notes` mode and does NOT require pdfjam."
)


def check_pdfjam_available() -> bool:
    """Return ``True`` if the ``pdfjam`` binary is on PATH.

    This is the preflight guard ``slides-handout`` runs before invoking the
    N-up post-process step for ``--4-up`` and ``--2-up`` layouts. It mirrors
    the ``shutil.which("mmdc")`` guard in :func:`check_mmdc_available` so the
    handout exporter can fail fast with a legible ``[blocker]`` (see
    :data:`PDFJAM_REMEDIATION`) instead of producing a one-slide-per-page PDF
    while the user expected a 4-up grid.

    ``pdfjam`` is OPTIONAL, not required: ``slides-handout --notes-below``
    renders via Marp's native ``--pdf-notes`` mode and produces a usable
    leave-behind PDF with zero pdfjam dependency. Callers should not invoke
    this preflight when the requested layout is ``--notes-below``.

    Kept binary-presence-only (no subprocess spawn) so it is unit-testable
    with a stubbed/monkeypatched ``shutil.which`` and requires no real TeX
    Live install at test time.
    """
    return shutil.which("pdfjam") is not None


def require_pdfjam() -> None:
    """Raise :class:`RenderError` with full remediation if ``pdfjam`` is absent.

    Convenience wrapper over :func:`check_pdfjam_available` for callers that
    prefer the raise-on-missing shape used by :func:`render_marp_to_pdf`'s
    ``marp`` guard. The handout exporter calls this only when the requested
    layout is ``--4-up`` or ``--2-up`` — the ``--notes-below`` path renders
    without invoking this guard.
    """
    if not check_pdfjam_available():
        raise RenderError(PDFJAM_REMEDIATION)


# ---------------------------------------------------------------------------
# auto-shrink detector preflight (OPTIONAL — deck silent-Marp-auto-shrink lint)
# ---------------------------------------------------------------------------

# Remediation message surfaced when ``Pillow`` and/or ``numpy`` are absent and
# the deck-review auto-shrink lint is requested. The detector lives at
# ``anvil/skills/deck/lib/auto_shrink_detector.py`` and is OPTIONAL at the
# framework level: ``deck-review`` graceful-skips the check when the deps are
# missing rather than failing the whole review.
#
# Mirrors the #65 (mmdc) and #85 (pdfjam) preflight pattern: this module's
# ``check_*_available`` family is the single place skills look up "is this
# third-party tool/library installed?". The remediation string is the install
# story to print into the skip-record so the user knows how to enable the
# check on the next run.
AUTO_SHRINK_REMEDIATION = (
    "Pillow and/or numpy not importable — required only for the optional "
    "`anvil:deck` silent-Marp-auto-shrink lint (issue #102 / #100b). "
    "Install via the opt-in extra: `uv pip install -e .[auto_shrink]` "
    "(or `pip install Pillow numpy`). The rest of `deck-review` proceeds "
    "without this check; the missing-deps note is recorded as an info-level "
    "lint entry in the review _summary.md."
)


def check_auto_shrink_deps_available() -> bool:
    """Return ``True`` if both ``Pillow`` and ``numpy`` import cleanly.

    Pure import-test — performs NO rendering and NO subprocess spawn. This
    is the preflight guard the deck-review auto-shrink lint runs before
    invoking ``auto_shrink_detector.detect_auto_shrink``. It mirrors the
    ``check_mmdc_available`` (#65) and ``check_pdfjam_available`` (#85)
    pattern so the deck command, the detector, and the smoke tests all
    share one implementation.

    Both libraries are OPTIONAL: ``deck-review`` graceful-skips the
    auto-shrink lint when this returns ``False`` and emits the
    :data:`AUTO_SHRINK_REMEDIATION` message as an info-level lint entry.
    Callers should NOT raise on a ``False`` return — that would defeat the
    graceful-skip contract documented in the deck-review command.

    Kept import-test-only (no model loading, no PIL.Image.open call) so it
    is unit-testable with a stubbed/monkeypatched ``importlib.util.find_spec``
    and requires no real Pillow/numpy install at test time. ``find_spec``
    consults the import-system finders directly (bypassing the
    ``sys.modules`` cache), which is what we want for both production use
    (the modules genuinely aren't installed) and for monkeypatched tests
    (we want the stub to determine the answer, not a stale cached import).
    """
    for module_name in ("PIL", "numpy"):
        try:
            spec = importlib.util.find_spec(module_name)
        except (ImportError, ValueError):
            return False
        if spec is None:
            return False
    return True


# ---------------------------------------------------------------------------
# image-lint preflight (OPTIONAL — memo image content-bbox sanity check)
# ---------------------------------------------------------------------------

# Remediation message surfaced when ``Pillow`` and/or ``numpy`` are absent
# and the memo render-gate's content-bbox-vs-canvas check (issue #395,
# check 3 of the ``memo_image_dimensions`` dimension) is requested. The
# check lives in ``anvil/lib/render_gate.py`` and is OPTIONAL: the gate
# graceful-skips the bbox check (with this message as a ``reasons``
# breadcrumb) while the stdlib header checks (pixel ceiling, aspect ratio,
# declared-vs-actual) still run.
#
# Mirrors the ``check_auto_shrink_deps_available`` (#102) preflight pattern;
# the extra declares the same Pillow + numpy set as ``[auto_shrink]``.
IMAGE_LINT_REMEDIATION = (
    "Pillow and/or numpy not importable — required only for the optional "
    "content-bbox-vs-canvas image check in the memo render gate (issue "
    "#395). Install via the opt-in extra: `uv pip install -e .[image_lint]` "
    "(or `pip install Pillow numpy`). The stdlib image-dimension checks "
    "(pixel ceiling, aspect ratio, declared-vs-actual) still run without it."
)


def check_image_lint_deps_available() -> bool:
    """Return ``True`` if both ``Pillow`` and ``numpy`` import cleanly.

    Pure import-test — performs NO decoding and NO subprocess spawn. This
    is the preflight guard the memo render-gate's ``memo_image_dimensions``
    content-bbox check (issue #395) runs before opening any image with
    PIL. Mirrors :func:`check_auto_shrink_deps_available` exactly (same
    dependency set, same ``importlib.util.find_spec`` mechanism, same
    graceful-skip contract): callers should NOT raise on a ``False``
    return; they record :data:`IMAGE_LINT_REMEDIATION` as a breadcrumb
    and continue with the stdlib-only checks.
    """
    for module_name in ("PIL", "numpy"):
        try:
            spec = importlib.util.find_spec(module_name)
        except (ImportError, ValueError):
            return False
        if spec is None:
            return False
    return True


# ---------------------------------------------------------------------------
# Memo render chain preflight (pandoc + weasyprint / wkhtmltopdf / xelatex)
# ---------------------------------------------------------------------------

# Remediation message surfaced when one or more engines in the anvil:memo
# markdown → PDF chain are absent. The chain is documented in
# ``anvil/lib/memo/README.md``: pandoc is the common front-end, and the
# HTML-to-PDF leg prefers ``weasyprint``, falls back to ``wkhtmltopdf``, then
# to ``xelatex`` as the engine-of-last-resort. The remediation string covers
# all four binaries in one actionable block rather than emitting four
# sequential errors.
#
# Mirrors the #65 (mmdc), #85 (pdfjam), and #102 (auto-shrink) preflight
# pattern: this module's ``check_*_available`` family is the single place
# skills look up "is this third-party tool installed?". The remediation
# string is the install story; callers print it into the skip-record / a
# render command's ``[blocker]`` finding when the corresponding check fails.
MEMO_RENDERER_REMEDIATION = (
    "anvil:memo PDF rendering requires pandoc plus one of weasyprint, "
    "wkhtmltopdf, or xelatex (see anvil/lib/memo/README.md for the chain "
    "rationale). Install pandoc via `brew install pandoc` (macOS) or "
    "`apt-get install pandoc` (Debian/Ubuntu); it is the common front-end. "
    "Then install ONE of the HTML-to-PDF engines:\n"
    "  - weasyprint (preferred — best CSS paged-media fidelity): "
    "`pip install weasyprint` (also requires cairo + pango; "
    "`brew install cairo pango gdk-pixbuf libffi` on macOS, "
    "`apt-get install libpango-1.0-0 libpangoft2-1.0-0` on Debian/Ubuntu);\n"
    "  - wkhtmltopdf (fallback — standalone binary, no Python): "
    "`brew install --cask wkhtmltopdf` (macOS) or "
    "`apt-get install wkhtmltopdf` (Debian/Ubuntu);\n"
    "  - xelatex (last resort — TeX Live engine): "
    "`brew install --cask mactex` (macOS; the trimmed `mactex-no-gui` "
    "omits `soul.sty` / `footnotehyper.sty` that pandoc 3.x emission "
    "requires — see issue #277) or "
    "`apt-get install texlive-xetex texlive-fonts-recommended "
    "texlive-latex-extra` (Debian/Ubuntu; `texlive-latex-extra` carries "
    "`soul`, `footnotehyper`, `bookmark`, and the booktabs/longtable "
    "set pandoc 3.x emits by default). The shipped "
    "`anvil/lib/memo/template.tex` `\\IfFileExists`-guards the optional "
    "packages so a thin TeX Live install still renders something, but "
    "the full install set above is the working recipe."
)


def check_pandoc_available() -> bool:
    """Return ``True`` if the ``pandoc`` binary is on PATH.

    This is the preflight guard the (future) memo-render command runs before
    invoking the markdown → HTML / markdown → PDF chain documented in
    ``anvil/lib/memo/README.md``. Pandoc is the common front-end for all three
    chain branches (weasyprint, wkhtmltopdf, xelatex) so this check is
    required regardless of which HTML-to-PDF engine is also available.

    Mirrors the ``check_mmdc_available`` (#65), ``check_pdfjam_available``
    (#85), and ``check_auto_shrink_deps_available`` (#102) precedents: a
    pure ``shutil.which`` test that is unit-testable with a monkeypatched
    ``shutil.which`` and requires no real pandoc install at test time.

    Note: this function only checks PATH presence. It does NOT validate the
    pandoc version, available output formats, or that any specific filter
    is installed. Phase 3's memo-render command runs the real pandoc
    invocation and surfaces any version-incompatibility errors at that time.

    See also :data:`MEMO_RENDERER_REMEDIATION` for the install story
    callers should surface when this returns ``False``.
    """
    return shutil.which("pandoc") is not None


def check_weasyprint_available() -> bool:
    """Return ``True`` if ``weasyprint`` is on PATH AND passes a runtime smoke test.

    The smoke test runs ``weasyprint --version`` and treats a non-zero exit as
    unavailable. This catches cases where the binary is on PATH but runtime
    deps (libgobject-2.0-0 / cairo / pango) are missing — which causes exit 43
    at render time without a useful error message.

    Two-stage check:
    1. ``shutil.which`` — fast binary-presence test (existing pattern)
    2. ``subprocess.run(["weasyprint", "--version"])`` — runtime viability check

    A ``TimeoutExpired`` (5 s) or ``OSError`` on the smoke test returns ``False``
    rather than raising, matching the graceful-degrade contract of this family.

    ``weasyprint`` is the PREFERRED HTML-to-PDF engine for the anvil:memo
    render chain (see ``anvil/lib/memo/README.md``). It supports the full CSS
    paged-media spec used in ``anvil/lib/memo/styles.css`` (the ``@page``
    rule with ``counter(page) / counter(pages)`` page numbering) without
    CLI-flag translation.

    Subprocess-only by design: the framework intentionally calls weasyprint
    as a CLI binary (``weasyprint input.html output.pdf``) rather than
    importing it as a Python module. This keeps the install story uniform
    across engines (HTML chain = one binary per engine) and matches the
    rest of ``render.py`` (no Python wheels in the dependency surface).

    See also :data:`MEMO_RENDERER_REMEDIATION` for the install story callers
    should surface when this and ``check_wkhtmltopdf_available`` both return
    ``False``.
    """
    if shutil.which("weasyprint") is None:
        return False
    try:
        result = subprocess.run(
            ["weasyprint", "--version"],
            capture_output=True,
            timeout=5,
        )
        return result.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def check_wkhtmltopdf_available() -> bool:
    """Return ``True`` if the ``wkhtmltopdf`` binary is on PATH.

    ``wkhtmltopdf`` is the FALLBACK HTML-to-PDF engine for the anvil:memo
    render chain (see ``anvil/lib/memo/README.md``). It is a standalone
    binary with no Python dependency, useful in environments where the
    weasyprint native deps (cairo, pango) are unavailable but a single-binary
    install is acceptable.

    NOTE: wkhtmltopdf's paged-media support is a partial subset of CSS3
    paged-media. Some of the ``@page`` rules in ``anvil/lib/memo/styles.css``
    (notably the ``@bottom-center { content: counter(page) ... }`` page
    footer) are not honored by wkhtmltopdf and must be passed via its
    ``--footer-center`` / ``--header-*`` CLI flags instead. Phase 3's
    memo-render command will own that translation. This availability check
    does NOT distinguish the two paths — it only confirms the binary is on
    PATH; the engine-selection logic decides which translation to apply.

    Mirrors the ``check_mmdc_available`` (#65) preflight pattern: a pure
    ``shutil.which`` test that is unit-testable with a monkeypatched
    ``shutil.which`` and requires no real wkhtmltopdf install at test time.

    See also :data:`MEMO_RENDERER_REMEDIATION` for the install story
    callers should surface when both this and ``check_weasyprint_available``
    return ``False``.
    """
    return shutil.which("wkhtmltopdf") is not None


# ---------------------------------------------------------------------------
# XeLaTeX preflight (shared Markdown-substrate PDF render path)
# ---------------------------------------------------------------------------

# Remediation message surfaced when ``xelatex`` is absent and the shared
# ``anvil/lib/latex_render.py`` BRIEF-configured PDF path is requested.
# Unlike the memo xelatex fallback (which uses the memo render chain and
# requires soul.sty / footnotehyper.sty that pandoc 3.x emits), this path
# uses the ``anvil-doc.cls`` base class directly and drives Markdown → LaTeX
# via pandoc --to=latex only (not the full pandoc → PDF chain). The note about
# mactex-no-gui is intentionally carried forward from the memo remediation so
# operators have the full context in one place.
XELATEX_REMEDIATION = (
    "xelatex not found on PATH — required for the LaTeX-substrate PDF render path. "
    "Install via `brew install --cask mactex-no-gui` (macOS; note: mactex-no-gui "
    "omits soul.sty / footnotehyper.sty that pandoc 3.x emits — use full mactex "
    "if also using the memo xelatex path) or "
    "`apt-get install texlive-xetex texlive-fonts-recommended texlive-latex-extra` "
    "(Debian/Ubuntu)."
)


def check_xelatex_available() -> bool:
    """Return ``True`` if the ``xelatex`` binary is on PATH.

    This is the preflight guard ``anvil/lib/latex_render.py`` runs before
    invoking the shared Markdown-substrate XeLaTeX PDF render path
    (``anvil-doc.cls`` + ``anvil-doc.tex.j2``). It mirrors the
    ``check_mmdc_available`` (#65), ``check_pdfjam_available`` (#85), and
    ``check_pandoc_available`` (#168) precedents: a pure ``shutil.which``
    test that is unit-testable with a monkeypatched ``shutil.which`` and
    requires no real TeX Live install at test time.

    The XeLaTeX path is required (not optional): skills that declare
    ``pdf_output: true`` in their BRIEF.md need this engine to produce
    the PDF. Callers should return ``COMPILE_UNAVAILABLE`` (not raise) when
    this returns ``False``, per the ``render_gate.py`` graceful-degrade
    contract.

    See also :data:`XELATEX_REMEDIATION` for the install story callers
    should surface when this returns ``False``.
    """
    return shutil.which("xelatex") is not None


# ---------------------------------------------------------------------------
# PDF → per-page PNGs
# ---------------------------------------------------------------------------


def render_pdf_to_pngs(
    pdf: Path,
    out_dir: Path,
    dpi: int = 150,
) -> List[Path]:
    """Convert a PDF to one PNG per page.

    Default path: ``pdftoppm -r <dpi> -png <pdf> <out_dir>/page``, which
    writes ``page-1.png``, ``page-2.png``, ... (one-indexed, no zero-pad).
    Fallback path: ``pdf2image.convert_from_path`` — only attempted when
    ``pdftoppm`` is not available AND the ``pdf2image`` module is
    importable.

    Parameters
    ----------
    pdf:
        Path to the input PDF.
    out_dir:
        Output directory. Created if it does not exist.
    dpi:
        Output resolution. 150 is a sensible default for 1080p-class
        critique; bump to 200+ for fine-grained chart-label legibility
        evaluation.

    Returns
    -------
    Sorted list of PNG paths produced.

    Raises
    ------
    RenderError
        If neither ``pdftoppm`` nor ``pdf2image`` is available, or the
        chosen tool returns non-zero.
    FileNotFoundError
        If the input PDF does not exist.
    """
    pdf = Path(pdf)
    out_dir = Path(out_dir)
    if not pdf.exists():
        raise FileNotFoundError(f"PDF not found: {pdf}")
    out_dir.mkdir(parents=True, exist_ok=True)

    if shutil.which("pdftoppm") is not None:
        # Primary path.
        cmd = [
            "pdftoppm",
            "-r",
            str(dpi),
            "-png",
            str(pdf),
            str(out_dir / "page"),
        ]
        result = subprocess.run(
            cmd, capture_output=True, text=True, check=False
        )
        if result.returncode != 0:
            raise RenderError(
                f"pdftoppm failed (exit {result.returncode}): "
                f"{result.stderr.strip() or result.stdout.strip()}"
            )
        return _collect_page_pngs(out_dir)

    # Fallback: pdf2image (Python wrapper around the same library).
    try:
        from pdf2image import convert_from_path  # type: ignore
    except ImportError as exc:
        raise RenderError(
            "Neither pdftoppm (poppler-utils) nor pdf2image is "
            "available. Install poppler "
            "(`brew install poppler` / `apt-get install poppler-utils`) "
            "or `pip install pdf2image`."
        ) from exc

    images = convert_from_path(str(pdf), dpi=dpi)
    out_paths: List[Path] = []
    for i, image in enumerate(images, start=1):
        path = out_dir / f"page-{i}.png"
        image.save(str(path), "PNG")
        out_paths.append(path)
    return sorted(out_paths)


def _collect_page_pngs(out_dir: Path) -> List[Path]:
    """Sort the page PNGs produced by pdftoppm by page number.

    pdftoppm writes ``page-1.png``, ``page-2.png``, ..., ``page-10.png``.
    Plain string sort would order ``page-10.png`` before ``page-2.png``,
    so we extract the integer suffix.
    """
    pngs = list(out_dir.glob("page-*.png"))

    def _page_num(p: Path) -> int:
        stem = p.stem  # "page-3"
        try:
            return int(stem.rsplit("-", 1)[1])
        except (ValueError, IndexError):
            return -1

    return sorted(pngs, key=_page_num)


# ---------------------------------------------------------------------------
# Pandoc Markdown → PDF (for paper/report)
# ---------------------------------------------------------------------------


def render_pandoc_to_pdf(
    source_md: Path,
    out_pdf: Path,
    defaults: Optional[Path] = None,
) -> Path:
    """Render a prose Markdown document to PDF via pandoc.

    Used by future ``paper-vision`` and ``report-vision`` critics where the
    artifact is a research paper or technical report rather than a deck.
    The Marp path is appropriate for slide artifacts only.

    Parameters
    ----------
    source_md:
        Path to the source Markdown.
    out_pdf:
        Output PDF path. Parent directory must exist.
    defaults:
        Optional path to a pandoc ``defaults.yaml`` file. When ``None``,
        pandoc runs with no flags beyond ``-o``.

    Returns
    -------
    The output PDF path.

    Raises
    ------
    RenderError
        If ``pandoc`` is not on PATH, or returns non-zero exit status.
    FileNotFoundError
        If ``source_md`` does not exist.
    """
    source_md = Path(source_md)
    out_pdf = Path(out_pdf)
    if not source_md.exists():
        raise FileNotFoundError(f"source not found: {source_md}")

    if shutil.which("pandoc") is None:
        raise RenderError(
            "pandoc not found on PATH. Install with "
            "`brew install pandoc` (macOS) or `apt-get install pandoc`."
        )

    cmd = ["pandoc", str(source_md), "-o", str(out_pdf)]
    if defaults is not None:
        cmd.extend(["--defaults", str(defaults)])

    result = subprocess.run(
        cmd, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise RenderError(
            f"pandoc failed (exit {result.returncode}): "
            f"{result.stderr.strip() or result.stdout.strip()}"
        )
    return out_pdf


# ---------------------------------------------------------------------------
# matplotlib figure walker
# ---------------------------------------------------------------------------


def render_matplotlib_figures(figures_dir: Path) -> List[Path]:
    """Enumerate already-rendered PNG figures under ``figures_dir``.

    This is a no-op walker, not a re-renderer. The skill's ``figures``
    command is responsible for executing ``figures/src/*.py`` and writing
    output PNGs; this helper just hands the vision critic a sorted list
    of those PNGs.

    Parameters
    ----------
    figures_dir:
        Path to the figures directory (e.g., ``acme-seed.3/figures/``).
        If the directory does not exist, returns an empty list.

    Returns
    -------
    Sorted list of PNG paths directly under ``figures_dir`` (non-recursive
    for predictability — a critic that wants nested figures should pass
    each subdir explicitly).
    """
    figures_dir = Path(figures_dir)
    if not figures_dir.exists() or not figures_dir.is_dir():
        return []
    return sorted(figures_dir.glob("*.png"))


__all__ = [
    "AUTO_SHRINK_REMEDIATION",
    "DEFAULT_MARP_CONFIG",
    "DEFAULT_MERMAID_THEME",
    "IMAGE_LINT_REMEDIATION",
    "MEMO_RENDERER_REMEDIATION",
    "MMDC_LAUNCH_REMEDIATION",
    "MMDC_REMEDIATION",
    "PDFJAM_REMEDIATION",
    "XELATEX_REMEDIATION",
    "RenderError",
    "check_auto_shrink_deps_available",
    "check_image_lint_deps_available",
    "check_mmdc_available",
    "check_mmdc_launchable",
    "check_pandoc_available",
    "check_pdfjam_available",
    "check_weasyprint_available",
    "check_wkhtmltopdf_available",
    "check_xelatex_available",
    "require_pdfjam",
    "render_marp_to_pdf",
    "render_mermaid_to_png",
    "render_pdf_to_pngs",
    "render_pandoc_to_pdf",
    "render_matplotlib_figures",
]
