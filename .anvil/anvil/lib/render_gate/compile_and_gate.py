"""Public API: ``compile_and_gate()`` (issue #1128 package split).

Invokes the LaTeX engine (or pandoc), captures the log, then runs
:func:`anvil.lib.render_gate.gate.gate` over the produced PDF. Split out
of the former monolithic ``anvil/lib/render_gate.py`` along its
existing section banners — see ``anvil/lib/render_gate/__init__.py``
for the full package rationale.
"""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path
from typing import Optional

from anvil.lib.render_gate.constants import (
    COMPILE_FAILED,
    COMPILE_OK,
    COMPILE_UNAVAILABLE,
    PANDOC_ENGINE,
)
from anvil.lib.render_gate.gate import gate
from anvil.lib.render_gate.results import GateResult




def compile_and_gate(
    tex_path: Path,
    *,
    engine: str = "xelatex",
    page_cap: Optional[int] = None,
    overfull_threshold_pt: float = 5.0,
    placeholder_patterns: Optional[tuple[str, ...]] = None,
    extra_source_paths: Optional[list[Path]] = None,
    output_dir: Optional[Path] = None,
    pdfinfo_path: Optional[str] = None,
    pdftotext_path: Optional[str] = None,
    pdfimages_path: Optional[str] = None,
) -> GateResult:
    """Compile ``tex_path`` with ``engine``, capture the log, then run the
    gate over the produced PDF.

    Used by skills whose pipeline doesn't otherwise compile (installation,
    proposal) and as a fallback for the others when the gate runs before
    audit/finalize. The compile is **single-pass** by default — enough to
    catch syntax errors and overfull boxes. Skills that need a full
    multi-pass compile (e.g., ``paper`` needs ``pdflatex && bibtex &&
    pdflatex && pdflatex`` for citations) should run that compile in their
    audit step and then call ``gate(...)`` against the produced PDF +
    log; this helper is the "first pass / no upstream compile" path.

    On engine-not-on-PATH, returns a ``GateResult`` with
    ``compile_status="unavailable"`` (the page-fit / overfull /
    placeholder checks then run against any pre-existing PDF + log if
    they happen to exist, or skip gracefully).

    Parameters
    ----------
    tex_path:
        Source ``.tex`` to compile.
    engine:
        ``"xelatex"`` (default) / ``"pdflatex"`` / ``"pandoc"``. When
        ``"pandoc"`` the overfull-box check is skipped (no semantics).
    page_cap, overfull_threshold_pt, placeholder_patterns, pdfinfo_path:
        Passed through to ``gate``.
    extra_source_paths:
        Additional source files to scan for placeholders (in addition to
        ``tex_path`` itself). Useful when the artifact has a multi-file
        source (e.g., ``main.tex`` + included chapter files).
    output_dir:
        Directory the engine should write output to. Defaults to
        ``tex_path.parent``.

    Returns
    -------
    GateResult
        With ``compile_status``, ``compile_exit_code``, and the four
        gate-check outcomes populated. ``passed=False`` if any gate
        failed; ``True`` otherwise.
    """
    tex_path = Path(tex_path)
    out_dir = Path(output_dir) if output_dir is not None else tex_path.parent
    sources = [tex_path] + [Path(p) for p in (extra_source_paths or [])]

    # Conventional output layout: PDF and log next to the .tex, named after
    # the .tex stem. xelatex/pdflatex honor -output-directory; pandoc takes
    # an explicit -o.
    pdf_path = out_dir / f"{tex_path.stem}.pdf"
    log_path = out_dir / f"{tex_path.stem}.log"

    if shutil.which(engine) is None:
        # Engine unavailable. Gate against whatever the filesystem already
        # has (pre-existing PDF + log), with COMPILE_UNAVAILABLE recorded.
        return gate(
            pdf_path=pdf_path,
            log_path=log_path if log_path.exists() else None,
            source_paths=sources,
            page_cap=page_cap,
            overfull_threshold_pt=overfull_threshold_pt,
            placeholder_patterns=placeholder_patterns,
            pdfinfo_path=pdfinfo_path,
            pdftotext_path=pdftotext_path,
            pdfimages_path=pdfimages_path,
            engine=engine,
            compile_status=COMPILE_UNAVAILABLE,
            compile_exit_code=None,
        )

    # Run the engine. For LaTeX, use -interaction=nonstopmode so a syntax
    # error doesn't hang; for pandoc, the -o flag determines output.
    if engine == PANDOC_ENGINE:
        cmd = [engine, str(tex_path), "-o", str(pdf_path)]
    else:
        cmd = [
            engine,
            "-interaction=nonstopmode",
            "-output-directory",
            str(out_dir),
            str(tex_path),
        ]
    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=False,
            cwd=str(out_dir),
        )
        exit_code = proc.returncode
        compile_status = COMPILE_OK if exit_code == 0 else COMPILE_FAILED
        # Pandoc doesn't write a .log; capture stderr as the log so the
        # gate's compile-failure path can show context.
        if engine == PANDOC_ENGINE and (proc.stderr or proc.stdout):
            log_path.write_text(
                (proc.stderr or "") + ("\n" if proc.stderr and proc.stdout else "") + (proc.stdout or ""),
                encoding="utf-8",
            )
    except (OSError, FileNotFoundError):
        exit_code = -1
        compile_status = COMPILE_FAILED

    return gate(
        pdf_path=pdf_path,
        log_path=log_path if log_path.exists() else None,
        source_paths=sources,
        page_cap=page_cap,
        overfull_threshold_pt=overfull_threshold_pt,
        placeholder_patterns=placeholder_patterns,
        pdfinfo_path=pdfinfo_path,
        pdftotext_path=pdftotext_path,
        pdfimages_path=pdfimages_path,
        engine=engine,
        compile_status=compile_status,
        compile_exit_code=exit_code,
    )
