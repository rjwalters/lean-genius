"""Shared XeLaTeX render primitive for Anvil Markdown-substrate skills.

This module implements ``render_brief_to_pdf``, a shared PDF render path for
skills that declare ``pdf_output: true`` in their BRIEF.md. It drives a
two-pass XeLaTeX compile from a Markdown body file using the shared
``anvil-doc.cls`` base class and the ``anvil-doc.tex.j2`` template.

The render pipeline:

1. **Preflight**: confirm ``xelatex`` and ``pandoc`` are on PATH. Return
   ``COMPILE_UNAVAILABLE`` (not raise) when either is absent.
2. **BRIEF gate**: check ``brief.get("pdf_output", False)``. Return
   ``COMPILE_SKIPPED`` when False or absent.
3. **Markdown → LaTeX fragment**: run ``pandoc --from=markdown --to=latex``
   on the body Markdown file to produce the ``body_latex`` fragment.
4. **Template render**: use ``string.Template`` to substitute the 8 BRIEF
   keys into ``anvil/lib/latex/anvil-doc.tex.j2``.
5. **Compile**: write the rendered ``.tex`` + ``anvil-doc.cls`` into a
   temporary directory, then run ``xelatex`` twice (two-pass for
   cross-references).
6. **Copy**: move the produced PDF to ``out_pdf``.
7. **Cleanup**: remove the temporary directory in a ``finally`` block.

Design notes
------------

- **No new base Python deps.** Template rendering uses the stdlib
  ``string.Template`` class (``${var}`` syntax), not Jinja2.
- **Graceful-degrade on missing tools.** Returns ``GateResult`` with
  ``compile_status=COMPILE_UNAVAILABLE`` when either xelatex or pandoc is
  absent, matching the ``render_gate.py`` contract.
- **Subprocess-only.** Both ``pandoc`` and ``xelatex`` are invoked as CLI
  subprocesses. No Python LaTeX bindings used.
- **Two-pass xelatex.** Standard two-pass compile for cross-reference
  resolution (table of contents, section labels). A single pass is enough
  for most anvil docs but two-pass is always safe and avoids ``??``
  placeholders in generated TOC entries.

Public API
----------

- ``render_brief_to_pdf(brief, body_md, out_pdf)`` — the primary entry point.
"""

from __future__ import annotations

import shutil
import string
import subprocess
import tempfile
from pathlib import Path

from anvil.lib.render import check_pandoc_available, check_xelatex_available
from anvil.lib.render_gate import (
    COMPILE_FAILED,
    COMPILE_OK,
    COMPILE_SKIPPED,
    COMPILE_UNAVAILABLE,
    GateResult,
)

# Path to the shared LaTeX assets relative to this file.
_LATEX_DIR = Path(__file__).parent / "latex"
_CLS_PATH = _LATEX_DIR / "anvil-doc.cls"
_TEMPLATE_PATH = _LATEX_DIR / "anvil-doc.tex.j2"


def render_brief_to_pdf(
    brief: dict,
    body_md: Path,
    out_pdf: Path,
) -> GateResult:
    """Render a Markdown body + BRIEF metadata to a PDF via XeLaTeX.

    This is the shared Markdown-substrate PDF render primitive for Anvil
    skills. It uses ``anvil-doc.cls`` and ``anvil-doc.tex.j2`` to produce
    a styled PDF from the skill's BRIEF.md frontmatter keys and the versioned
    body Markdown file.

    Parameters
    ----------
    brief:
        Dictionary of BRIEF.md frontmatter keys. The following keys are
        consumed:

        - ``pdf_output`` (bool, required to enable): if False or absent,
          returns ``COMPILE_SKIPPED`` immediately.
        - ``title`` (str): document title. Defaults to ``""`` if absent.
        - ``studio`` (str): studio name for the footer. Defaults to ``""``
          if absent.
        - ``date`` (str): date string. Defaults to ``""`` if absent.
        - ``stage`` (str): stage label. Defaults to ``""`` if absent.
        - ``hero`` (str): path to the hero image (relative to the compile
          working directory). Defaults to ``""`` (no-op in the cls).
        - ``signature_color`` (str): 6-character hex color (no ``#``).
          Defaults to ``"6B7280"`` (neutral gray).
        - ``orientation`` (str): ``"landscape"`` switches geometry.
          Defaults to portrait (``""``).

    body_md:
        Path to the versioned body Markdown file (e.g.,
        ``<thread>.N/<slug>.md``). Must exist.
    out_pdf:
        Destination PDF path. Parent directory must exist.

    Returns
    -------
    GateResult
        With ``compile_status`` set to one of:

        - ``COMPILE_SKIPPED`` — ``pdf_output`` is False or absent.
        - ``COMPILE_UNAVAILABLE`` — ``xelatex`` or ``pandoc`` not on PATH.
        - ``COMPILE_OK`` — compile succeeded and PDF was written to
          ``out_pdf``.
        - ``COMPILE_FAILED`` — compile failed (pandoc or xelatex
          returned non-zero).

        ``passed`` mirrors compile success: True for OK/SKIPPED/UNAVAILABLE
        (graceful degrade), False for COMPILE_FAILED.
    """
    body_md = Path(body_md)
    out_pdf = Path(out_pdf)

    # ------------------------------------------------------------------
    # Preflight: tool availability
    # ------------------------------------------------------------------
    if not check_xelatex_available():
        return _unavailable_result(
            out_pdf,
            reason="xelatex not found on PATH — install TeX Live or MacTeX.",
        )
    if not check_pandoc_available():
        return _unavailable_result(
            out_pdf,
            reason="pandoc not found on PATH — required to convert Markdown to LaTeX fragment.",
        )

    # ------------------------------------------------------------------
    # BRIEF gate: pdf_output must be truthy
    # ------------------------------------------------------------------
    if not brief.get("pdf_output", False):
        return GateResult(
            pdf_path=str(out_pdf),
            log_path=None,
            pages=None,
            page_cap=None,
            overfull_boxes=[],
            overfull_threshold_pt=5.0,
            compile_status=COMPILE_SKIPPED,
            compile_exit_code=None,
            placeholders=[],
            passed=True,
            reasons=["pdf_output is False or absent in BRIEF — PDF render skipped."],
        )

    # ------------------------------------------------------------------
    # Step 1: Markdown → LaTeX fragment via pandoc
    # ------------------------------------------------------------------
    pandoc_cmd = [
        "pandoc",
        "--from=markdown",
        "--to=latex",
        str(body_md),
    ]
    pandoc_result = subprocess.run(
        pandoc_cmd, capture_output=True, text=True, check=False
    )
    if pandoc_result.returncode != 0:
        return GateResult(
            pdf_path=str(out_pdf),
            log_path=None,
            pages=None,
            page_cap=None,
            overfull_boxes=[],
            overfull_threshold_pt=5.0,
            compile_status=COMPILE_FAILED,
            compile_exit_code=pandoc_result.returncode,
            placeholders=[],
            passed=False,
            reasons=[
                f"pandoc Markdown→LaTeX failed (exit {pandoc_result.returncode}): "
                f"{pandoc_result.stderr.strip() or pandoc_result.stdout.strip()}"
            ],
        )
    body_latex = pandoc_result.stdout

    # ------------------------------------------------------------------
    # Step 2: Template substitution
    # ------------------------------------------------------------------
    template_text = _TEMPLATE_PATH.read_text(encoding="utf-8")
    tmpl = string.Template(template_text)

    orientation_option = (
        "landscape" if brief.get("orientation") == "landscape" else ""
    )
    substituted = tmpl.substitute(
        orientation_option=orientation_option,
        signature_color=brief.get("signature_color", "6B7280"),
        title=brief.get("title", ""),
        studio=brief.get("studio", ""),
        date=brief.get("date", ""),
        stage=brief.get("stage", ""),
        hero=brief.get("hero", ""),
        body_latex=body_latex,
    )

    # ------------------------------------------------------------------
    # Step 3: Compile in a temp directory (two-pass xelatex)
    # ------------------------------------------------------------------
    tmpdir = Path(tempfile.mkdtemp())
    try:
        tex_file = tmpdir / "doc.tex"
        tex_file.write_text(substituted, encoding="utf-8")
        # Copy anvil-doc.cls next to the .tex so xelatex resolves the class.
        shutil.copy2(_CLS_PATH, tmpdir / "anvil-doc.cls")

        xelatex_cmd = [
            "xelatex",
            "-interaction=nonstopmode",
            "-output-directory",
            str(tmpdir),
            str(tex_file),
        ]

        # First pass. In a two-pass LaTeX compile the first invocation
        # routinely reports errors/warnings (missing .aux data, unresolved
        # cross-references) that the second pass silently resolves, so its
        # exit code is not a reliable success/failure signal on its own —
        # only proc2's result (after both passes have run) is checked below.
        # We still capture output/exit code here (rather than discarding
        # it) so it is available if a future diagnostic path wants it.
        proc1 = subprocess.run(
            xelatex_cmd,
            capture_output=True,
            text=True,
            check=False,
            cwd=str(tmpdir),
        )
        # Second pass (for cross-references / TOC)
        proc2 = subprocess.run(
            xelatex_cmd,
            capture_output=True,
            text=True,
            check=False,
            cwd=str(tmpdir),
        )

        exit_code = proc2.returncode
        produced_pdf = tmpdir / "doc.pdf"
        log_file = tmpdir / "doc.log"

        if exit_code != 0 or not produced_pdf.exists():
            log_content = ""
            if log_file.exists():
                log_content = log_file.read_text(encoding="utf-8", errors="replace")
            log_tail = log_content.strip()[-500:] if log_content.strip() else ""
            return GateResult(
                pdf_path=str(out_pdf),
                log_path=None,
                pages=None,
                page_cap=None,
                overfull_boxes=[],
                overfull_threshold_pt=5.0,
                compile_status=COMPILE_FAILED,
                compile_exit_code=exit_code,
                placeholders=[],
                passed=False,
                reasons=[
                    f"xelatex compile failed (exit {exit_code}, first pass exit "
                    f"{proc1.returncode}). "
                    f"Stderr: {proc2.stderr.strip()[:500] if proc2.stderr else '(none)'}. "
                    + (
                        f"Log tail: {log_tail}"
                        if log_tail
                        else "See log for details."
                    )
                ],
            )

        # Copy the produced PDF to the destination.
        shutil.copy2(produced_pdf, out_pdf)

        return GateResult(
            pdf_path=str(out_pdf),
            log_path=None,
            pages=None,
            page_cap=None,
            overfull_boxes=[],
            overfull_threshold_pt=5.0,
            compile_status=COMPILE_OK,
            compile_exit_code=0,
            placeholders=[],
            passed=True,
            reasons=[],
        )

    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------


def _unavailable_result(out_pdf: Path, *, reason: str) -> GateResult:
    """Return a COMPILE_UNAVAILABLE GateResult with a human-readable reason."""
    return GateResult(
        pdf_path=str(out_pdf),
        log_path=None,
        pages=None,
        page_cap=None,
        overfull_boxes=[],
        overfull_threshold_pt=5.0,
        compile_status=COMPILE_UNAVAILABLE,
        compile_exit_code=None,
        placeholders=[],
        passed=True,  # graceful-degrade: unavailable is not a failure
        reasons=[reason],
    )


__all__ = [
    "render_brief_to_pdf",
]
